/**
 * Structural rewrites for union matches, array bounds, and single-evaluation
 * ?? / ?. expressions. Ordinary optional guards stay as source control flow;
 * resolve introduces checked payload reads without changing storage types.
 */

import type { TModule, TFunction, TStmt, TExpr } from "./typedir.js";
import { isTerminatorKind } from "./typedir.js";
import {
  type CondCtx, leadingIsArray, freshOcBinder,
  applyChain, arrayBoundsCond,
  isArrayFact, typeofStringFact, variantFact, negVariantFact,
} from "./condition-facts.js";

// ── Walkers ──────────────────────────────────────────────────

function walkExpr(e: TExpr, ctx: CondCtx): TExpr {
  const r = recurseExpr(e, ctx);
  return ruleNullish(r, ctx) ?? ruleNullishIndex(r) ?? ruleOptChainIndex(r) ?? ruleOptChain(r, ctx) ?? ruleImplArrayIsArray(r, ctx) ?? ruleConditionalArrayIsArray(r, ctx) ?? ruleConditionalAndArrayIsArray(r, ctx) ?? r;
}

function recurseExpr(e: TExpr, ctx: CondCtx): TExpr {
  const re = (x: TExpr) => walkExpr(x, ctx);
  switch (e.kind) {
    case "var": case "num": case "bigint": case "str": case "bool":
    case "havoc":
      return e;
    case "binop": return { ...e, left: re(e.left), right: re(e.right) };
    case "unop": case "coerce": return { ...e, expr: re(e.expr) };
    case "call": return { ...e, fn: re(e.fn), args: e.args.map(re) };
    case "index": return { ...e, obj: re(e.obj), idx: re(e.idx) };
    case "field": return { ...e, obj: re(e.obj) };
    case "record": return { ...e, spread: e.spread ? re(e.spread) : null,
      fields: e.fields.map(f => ({ ...f, value: re(f.value) })) };
    case "arrayLiteral": return { ...e, elems: e.elems.map(re) };
    case "lambda": return { ...e, body: walkStmts(e.body, ctx) };
    case "conditional": return { ...e, cond: re(e.cond), then: re(e.then), else: re(e.else) };
    case "optChain": return { ...e, obj: re(e.obj),
      chain: e.chain.map(s => s.kind === "call" ? { ...s, args: s.args.map(re) }
        : s.kind === "index" ? { ...s, idx: re(s.idx) }
        : s) };
    case "nullish": return { ...e, left: re(e.left), right: re(e.right) };
    case "forall": return { ...e, body: re(e.body) };
    case "exists": return { ...e, body: re(e.body) };
    case "someMatch": return { ...e, someBody: re(e.someBody), noneBody: re(e.noneBody) };
    case "tagMatch": return { ...e, scrutinee: re(e.scrutinee),
      cases: e.cases.map(c => ({ ...c, body: re(c.body) })),
      fallthrough: e.fallthrough ? re(e.fallthrough) : null };
  }
}

function walkStmt(s: TStmt, ctx: CondCtx): TStmt {
  // Recurse into children first, then try rules at this node.
  const r = recurseStmt(s, ctx);
  return ruleIfAndArrayIsArray(r, ctx) ?? ruleOptionalIndexBinding(r) ?? r;
}

function walkStmts(stmts: TStmt[], ctx: CondCtx): TStmt[] {
  const result: TStmt[] = [];
  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i];
    // Discriminant rules consume a prefix of stmts; remaining is processed normally.
    const tagged = ruleDiscriminantChain(stmts.slice(i), ctx) ?? ruleDiscriminantNegEarlyReturn(stmts.slice(i), ctx);
    if (tagged) {
      result.push(walkStmt(tagged.stmt, ctx));
      i += tagged.consumed - 1;
      continue;
    }
    const walked = walkStmt(s, ctx);
    result.push(walked);
  }
  return result;
}

function recurseStmt(s: TStmt, ctx: CondCtx): TStmt {
  const re = (x: TExpr) => walkExpr(x, ctx);
  const rs = (x: TStmt[]) => walkStmts(x, ctx);
  switch (s.kind) {
    case "let": return { ...s, init: re(s.init) };
    case "assign": return { ...s, value: re(s.value) };
    case "return": return { ...s, value: re(s.value) };
    case "break": case "continue": case "throw": return s;
    case "expr": return { ...s, expr: re(s.expr) };
    case "if": return { ...s, cond: re(s.cond), then: rs(s.then), else: rs(s.else) };
    case "while": return { ...s, cond: re(s.cond),
      invariants: s.invariants.map(re),
      decreases: s.decreases ? re(s.decreases) : null,
      doneWith: s.doneWith ? re(s.doneWith) : null,
      body: rs(s.body) };
    case "switch": return { ...s, expr: re(s.expr),
      cases: s.cases.map(c => ({ ...c, body: rs(c.body) })),
      defaultBody: rs(s.defaultBody) };
    case "forof": return { ...s, iterable: re(s.iterable),
      invariants: s.invariants.map(re),
      doneWith: s.doneWith ? re(s.doneWith) : null,
      body: rs(s.body) };
    case "ghostLet": return { ...s, init: re(s.init) };
    case "ghostAssign": return { ...s, value: re(s.value) };
    case "assert": return { ...s, expr: re(s.expr) };
    case "tagMatch": return { ...s, scrutinee: re(s.scrutinee),
      cases: s.cases.map(c => ({ ...c, body: rs(c.body) })),
      fallthrough: rs(s.fallthrough) };
  }
}

function isTerminating(stmts: TStmt[]): boolean {
  if (stmts.length === 0) return false;
  return isTerminatorKind(stmts[stmts.length - 1].kind);
}

/** Driver (expression): `left ?? right` — nullish coalescing.
 *  → `someMatch left { Some(_v) => _v, None => right }`.
 *  Single-evaluation: scrutinee may be any expression. Presence-only
 *  semantics (`??` tests null/undefined, not falsiness) — no falsy gate. */
function ruleNullish(e: TExpr, ctx: CondCtx): TExpr | null {
  if (e.kind !== "nullish") return null;
  if (e.left.ty.kind !== "optional") return null;
  const innerTy = e.left.ty.inner;
  const binder = freshOcBinder(ctx);
  return {
    kind: "someMatch",
    scrutinee: e.left, binder, binderTy: innerTy,
    someBody: { kind: "var", name: binder, ty: innerTy },
    noneBody: e.right,
    ty: e.ty,
  };
}

/** Driver (expression): `arr[i] ?? right` — in-bounds fact in nullish
 *  position. Under noUncheckedIndexedAccess `arr[i]` is `T | undefined`,
 *  undefined exactly when out of bounds, so
 *  → `(0 <= i && i < arr.length) ? arr[i] : right`. The guarded `then`
 *  keeps the seq index in bounds for the backend. (Map index is already
 *  optional-typed and handled by ruleNullish above.) */
function ruleNullishIndex(e: TExpr): TExpr | null {
  if (e.kind !== "nullish") return null;
  if (e.left.kind !== "index") return null;
  if (e.left.obj.ty.kind !== "array") return null;
  const cond = arrayBoundsCond(e.left.obj, e.left.idx);
  return { kind: "conditional", cond, then: e.left, else: e.right, ty: e.ty };
}

/** Driver (expression): `arr[i]?.<chain>` — in-bounds fact in optChain
 *  position, the optChain sibling of ruleNullishIndex.
 *  → `(0 <= i && i < arr.length) ? <chain on arr[i]> : undefined`. The
 *  conditional's optional type makes transform wrap the in-bounds chain
 *  result in Some and the OOB branch in None. (ruleOptChain itself bails
 *  here: an array index is typed as the non-optional element type.) */
function ruleOptChainIndex(e: TExpr): TExpr | null {
  if (e.kind !== "optChain") return null;
  if (e.obj.kind !== "index") return null;
  if (e.obj.obj.ty.kind !== "array") return null;
  const cond = arrayBoundsCond(e.obj.obj, e.obj.idx);
  const body = applyChain(e.obj, e.chain); // arr[i] — in bounds under `cond`
  const undef: TExpr = { kind: "var", name: "undefined", ty: { kind: "void" } };
  return { kind: "conditional", cond, then: body, else: undef, ty: e.ty };
}

/** Driver (statement): reconcile a `const e = arr[i]` whose binding is optional
 *  (`e: T | undefined`) but whose array-index initializer is total (`T`) —
 *  in-bounds fact in initializer position. Model the index as its JS
 *  semantics — `e := inBounds ? arr[i] : undefined` — so `e` is a real
 *  `Option<T>` and a later `e?.f` someMatch is well-typed; an in-bounds proof
 *  makes the None branch dead. Skipped when the element type is already
 *  optional: no mismatch. */
function ruleOptionalIndexBinding(s: TStmt): TStmt | null {
  if (s.kind !== "let") return null;
  if (s.ty.kind !== "optional") return null;
  const init = s.init;
  if (init.kind !== "index") return null;
  if (init.obj.ty.kind !== "array") return null;
  if (init.ty.kind === "optional") return null;  // array-of-optionals: not a flag artifact
  const cond = arrayBoundsCond(init.obj, init.idx);
  const undef: TExpr = { kind: "var", name: "undefined", ty: { kind: "void" } };
  const guarded: TExpr = { kind: "conditional", cond, then: init, else: undef, ty: s.ty };
  return { ...s, init: guarded };
}

/** Driver (expression): `obj?.<chain>` — single-eval optional chain.
 *  → `someMatch obj { Some(_oc{N}_val) => apply(chain, _oc{N}_val), None => undefined }`.
 *  The someBody applies the chain to the binder directly (field/call/index),
 *  so transform doesn't substitute. Scrutinee can be any expression. */
function ruleOptChain(e: TExpr, ctx: CondCtx): TExpr | null {
  if (e.kind !== "optChain") return null;
  if (e.obj.ty.kind !== "optional") return null;
  const innerTy = e.obj.ty.inner;
  const binder = freshOcBinder(ctx);
  const body = applyChain({ kind: "var", name: binder, ty: innerTy }, e.chain);
  const noneBody: TExpr = { kind: "var", name: "undefined", ty: { kind: "void" } };
  return {
    kind: "someMatch",
    scrutinee: e.obj, binder, binderTy: innerTy,
    someBody: body, noneBody, ty: e.ty,
  };
}

/** Driver (expression): `Array.isArray(x) ==> B` or `!Array.isArray(x) ==> B` —
 *  isArray fact in implication position (spec premises).
 *  → `tagMatch x { ArrayBranch => walkExpr(B), _ => true }` (or NonArrayBranch).
 *  The other variant becomes a vacuous-true fallthrough. */
function ruleImplArrayIsArray(e: TExpr, ctx: CondCtx): TExpr | null {
  if (e.kind !== "binop" || e.op !== "==>") return null;
  const pos = isArrayFact(e.left, ctx);
  const neg = e.left.kind === "unop" && e.left.op === "!"
    ? isArrayFact(e.left.expr, ctx)
    : null;
  const matched = pos ?? (neg ? { scrutinee: neg.scrutinee, typeName: neg.typeName, variant: "NonArrayBranch" as const } : null);
  if (!matched) return null;
  return {
    kind: "tagMatch",
    scrutinee: matched.scrutinee,
    typeName: matched.typeName,
    cases: [{ variant: matched.variant, body: walkExpr(e.right, ctx) }],
    fallthrough: { kind: "bool", value: true, ty: { kind: "bool" } },
    ty: { kind: "bool" },
  };
}

/** Driver (expression): `Array.isArray(x) ? a : b` — isArray fact in ternary
 *  position (also `typeof x === "string"`, which selects the NonArrayBranch).
 *  → `tagMatch x { <variant> => walkExpr(then-side) } fallthrough walkExpr(else-side)`.
 *  Inside the matched arm, bare references to `x` are rewritten to the
 *  variant's payload field by `transformExpr` when emitting the tagMatch. */
function ruleConditionalArrayIsArray(e: TExpr, ctx: CondCtx): TExpr | null {
  if (e.kind !== "conditional") return null;
  const pos = isArrayFact(e.cond, ctx);
  // `typeof x === "string"` is a positive check like `Array.isArray`, but selects
  // the NonArrayBranch — its then-branch is the matched-variant body.
  const tof = pos ? null : typeofStringFact(e.cond, ctx);
  const neg = !pos && !tof && e.cond.kind === "unop" && e.cond.op === "!"
    ? isArrayFact(e.cond.expr, ctx)
    : null;
  const matched = pos ?? tof ?? (neg ? { scrutinee: neg.scrutinee, typeName: neg.typeName, variant: "NonArrayBranch" as const } : null);
  if (!matched) return null;
  // The selected variant already accounts for negation. Its arm always runs
  // the source then-branch; swapping branches here would negate the test twice.
  return {
    kind: "tagMatch",
    scrutinee: matched.scrutinee,
    typeName: matched.typeName,
    cases: [{ variant: matched.variant, body: walkExpr(e.then, ctx) }],
    fallthrough: walkExpr(e.else, ctx),
    ty: e.ty,
  };
}

/** Split conjunctions containing union checks in source order. Earlier guards
 *  may justify an optional payload read in a later union scrutinee. */
function ruleIfAndArrayIsArray(s: TStmt, ctx: CondCtx): TStmt | null {
  if (s.kind !== "if") return null;
  const direct = isArrayFact(s.cond, ctx);
  if (direct) return { kind: "tagMatch", scrutinee: direct.scrutinee,
    typeName: direct.typeName, cases: [{ variant: direct.variant, body: s.then }], fallthrough: s.else };
  if (s.cond.kind !== "binop" || s.cond.op !== "&&" ||
      !leadingIsArray(s.cond, ctx)) return null;
  return walkStmt({ ...s, cond: s.cond.left,
    then: [{ ...s, cond: s.cond.right }] }, ctx);
}

/** Split a guarded ternary in source order so preceding optional guards run
 *  before an Array.isArray receiver is read. The recursive walk creates the
 *  variant match only inside the selected branch. */
function ruleConditionalAndArrayIsArray(e: TExpr, ctx: CondCtx): TExpr | null {
  if (e.kind !== "conditional" || e.cond.kind !== "binop" || e.cond.op !== "&&" ||
      !leadingIsArray(e.cond, ctx)) return null;
  return walkExpr({ ...e, cond: e.cond.left,
    then: { ...e, cond: e.cond.right } }, ctx);
}

/** Driver (list-level): consecutive `if (x.kind === "v") ...` chain →
 *  tagMatch. Walks consecutive top-level ifs on the same discriminator var;
 *  the first one with an else-branch ends the chain (else becomes
 *  fallthrough; if-else-if flattens into more cases). Returns the tagMatch
 *  and how many stmts consumed. */
function ruleDiscriminantChain(stmts: TStmt[], ctx: CondCtx): { stmt: TStmt; consumed: number } | null {
  if (stmts.length === 0 || stmts[0].kind !== "if") return null;
  const first = variantFact(stmts[0].cond, ctx);
  if (!first) return null;

  const cases: { variant: string; body: TStmt[] }[] = [];

  function collectElse(s: TStmt & { kind: "if" }): TStmt[] {
    const p = variantFact(s.cond, ctx);
    if (!p || p.scrutinee.name !== first!.scrutinee.name) return [s];
    cases.push({ variant: p.variant, body: s.then });
    if (s.else.length === 0) return [];
    if (s.else.length === 1 && s.else[0].kind === "if") return collectElse(s.else[0]);
    return s.else;
  }

  let consumed = 0;
  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i];
    if (s.kind !== "if") break;
    const p = variantFact(s.cond, ctx);
    if (!p || p.scrutinee.name !== first.scrutinee.name) break;
    cases.push({ variant: p.variant, body: s.then });
    consumed = i + 1;
    if (s.else.length > 0) {
      const ft = (s.else.length === 1 && s.else[0].kind === "if") ? collectElse(s.else[0]) : s.else;
      return { stmt: { kind: "tagMatch", scrutinee: first.scrutinee, typeName: first.typeName,
        cases, fallthrough: ft }, consumed };
    }
  }
  if (cases.length === 0) return null;
  // If every case terminates, the trailing statements are the default arm
  // (preserving the clean dispatch-as-expression shape). Otherwise the tail runs
  // after the match for every variant, so leave it to the caller (empty default)
  // rather than mis-routing it into the default arm only.
  if (cases.every(c => isTerminating(c.body))) {
    return { stmt: { kind: "tagMatch", scrutinee: first.scrutinee, typeName: first.typeName,
      cases, fallthrough: stmts.slice(consumed) }, consumed: stmts.length };
  }
  return { stmt: { kind: "tagMatch", scrutinee: first.scrutinee, typeName: first.typeName,
    cases, fallthrough: [] }, consumed };
}

/** Driver (list-level): `if (x.kind !== "v") terminate; rest` → tagMatch
 *  with cases = [{ variant: v, body: rest }] and fallthrough = terminate. */
function ruleDiscriminantNegEarlyReturn(stmts: TStmt[], ctx: CondCtx): { stmt: TStmt; consumed: number } | null {
  if (stmts.length < 2) return null;
  const first = stmts[0];
  if (first.kind !== "if" || first.else.length > 0) return null;
  if (!isTerminating(first.then)) return null;
  const cond = negVariantFact(first.cond, ctx);
  if (!cond) return null;
  return { stmt: { kind: "tagMatch", scrutinee: cond.scrutinee, typeName: cond.typeName,
    cases: [{ variant: cond.variant, body: stmts.slice(1) }], fallthrough: first.then },
    consumed: stmts.length };
}

// ── Function / module entry ──────────────────────────────────

function narrowFunction(fn: TFunction, ctx: CondCtx): TFunction {
  return {
    ...fn,
    requires: fn.requires.map(e => walkExpr(e, ctx)),
    ensures: fn.ensures.map(e => walkExpr(e, ctx)),
    decreases: fn.decreases ? walkExpr(fn.decreases, ctx) : null,
    body: walkStmts(fn.body, ctx),
  };
}

export function narrowModule(mod: TModule): TModule {
  const ctx: CondCtx = { decls: mod.typeDecls, oc: { n: 0 } };
  return {
    ...mod,
    constants: mod.constants.map(c => ({ ...c, value: walkExpr(c.value, ctx) })),
    functions: mod.functions.map(fn => narrowFunction(fn, ctx)),
    classes: mod.classes.map(cls => ({
      ...cls,
      methods: cls.methods.map(m => narrowFunction(m, ctx)),
    })),
  };
}
