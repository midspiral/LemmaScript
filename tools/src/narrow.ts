/**
 * narrow — Structural-narrowing rewrite pass.
 *
 * Pipeline: resolve → narrow → transform → emit.
 *
 * Syntax-directed pattern matching on typed IR. Detects optional-narrowing
 * patterns and rewrites each into a `someMatch` IR node carrying the
 * scrutinee, binder, unwrapped type, and arms:
 *   - `if (e !== undefined) S`                 (statement)
 *   - `if (e === undefined) terminate; rest`   (early-return + rest consumption)
 *   - `if (e !== undefined && rest) S`         (&& in if; no else)
 *   - `if (a === undefined || b === undefined) terminate; rest`  (|| chain)
 *   - `let x = (e_opt && rest) ? a : b`        (statement, impure-OK guard)
 *   - `e !== undefined ? a : b`                (ternary)
 *   - `e !== undefined && rest ? a : b`        (&& in ternary; pure rest)
 *   - `opt ? a : b`                            (truthiness)
 *   - `path !== undefined [&& rest] ==> B`     (spec implication narrowing)
 *   - `optChain(obj, field)`                   (`obj?.field` from extract)
 *
 * Following TS semantics, narrowing rules only fire for pure access paths
 * (`var(x)` or `field(purePath, name)`). Complex scrutinees (call results,
 * index ops) require bind-first: `const v = m.get(k); if (v !== undefined) ...`.
 * The `optChain` rule is the exception: narrow constructs the someBody to use the
 * binder directly, so any scrutinee shape is allowed.
 *
 * Transform lowers `someMatch` to IR `match` Some/None, substituting the
 * binder for path-shaped scrutinees via `replacePathInTExpr` /
 * `replacePathInTStmts`. Resolve runs before narrow and handles type narrowing
 * only (env extension, `narrowedPaths`). Narrow doesn't substitute on raw IR
 * — the body keeps its original expressions until transform.
 *
 * Walker shape: bottom-up over TExpr/TStmt. At each node, recurse children
 * via the *Recurse* helpers, then try the rules in order. List-level rules
 * (early-return, let-cond) run in `walkStmts` so they can consume the rest
 * of the block.
 */

import type { TModule, TFunction, TStmt, TExpr, Ty } from "./typedir.js";
import { isTerminatorKind } from "./typedir.js";
import type { TypeDeclInfo } from "./types.js";
import { freshName } from "./names.js";

// ── Optional-check detection ────────────────────────────────

/** Counter for naming optChain binders. Reset per module. */
let _ocCounter = 0;

/** Type declarations for this module. Set in narrowModule, used by the
 *  discriminant-narrowing rules to resolve `'key' in x` to a variant. */
let _typeDecls: TypeDeclInfo[] = [];

/** Detect optional checks: `e !== undefined`, `e === undefined`, or `!e` for a
 *  pure-access-path optional-typed e. `!e` is equivalent to `=== undefined`.
 *  Following TS, only pure access paths narrow; complex scrutinees return null. */
function parseOptionalCheck(cond: TExpr): { scrutinee: TExpr; innerTy: Ty; negated: boolean; binderHint: string; truthiness: boolean } | null {
  // `!e` where e is optional — a truthiness form: false iff e is absent OR its
  // inner value is itself falsy (so `Some(0)`/`Some("")` count as falsy too).
  if (cond.kind === "unop" && cond.op === "!" && cond.expr.ty.kind === "optional") {
    const e = cond.expr;
    const innerTy = cond.expr.ty.inner;
    const hint = binderHintFor(e);
    if (hint === null) return null;
    return { scrutinee: e, innerTy, negated: true, binderHint: freshName(hint), truthiness: true };
  }
  if (cond.kind !== "binop" || (cond.op !== "!==" && cond.op !== "===")) {
    // Bare optional truthiness: `if (e)` where e: T | undefined — true iff e is
    // present AND its inner value is truthy.
    if (cond.ty.kind === "optional") {
      const hint = binderHintFor(cond);
      if (hint === null) return null;
      return { scrutinee: cond, innerTy: cond.ty.inner, negated: false, binderHint: freshName(hint), truthiness: true };
    }
    return null;
  }
  // Explicit `e === undefined` / `e !== undefined` — a pure presence check,
  // independent of the inner value (so NOT a truthiness form).
  let e: TExpr | null = null;
  if (cond.right.kind === "var" && cond.right.name === "undefined") e = cond.left;
  if (cond.left.kind === "var" && cond.left.name === "undefined") e = cond.right;
  if (!e || e.ty.kind !== "optional") return null;
  const hint = binderHintFor(e);
  if (hint === null) return null;
  return { scrutinee: e, innerTy: e.ty.inner, negated: cond.op === "===", binderHint: freshName(hint), truthiness: false };
}

function binderHintFor(e: TExpr): string | null {
  // Pure access paths: var(x) or field(purePath, name).
  // Walks down to the var root, collecting field names. Returns
  // `_root_field1_field2_..._val` (or `_root_val` for a bare var).
  const fields: string[] = [];
  let cur = e;
  while (cur.kind === "field") { fields.unshift(cur.field); cur = cur.obj; }
  if (cur.kind !== "var") return null;
  // \result is stored as the IR var name "\\result"; sanitize for a valid identifier.
  const root = cur.name === "\\result" ? "result" : cur.name;
  return fields.length === 0 ? `_${root}_val` : `_${root}_${fields.join("_")}_val`;
}

// Aliased for code that historically called the simpler check.
const parseSimpleOptionalCheck = parseOptionalCheck;

// ── Walkers ──────────────────────────────────────────────────

function walkExpr(e: TExpr): TExpr {
  const r = recurseExpr(e);
  return ruleNullish(r) ?? ruleNullishIndex(r) ?? ruleOptChainIndex(r) ?? ruleOptChain(r) ?? ruleImplOptional(r) ?? ruleImplArrayIsArray(r) ?? ruleConditionalArrayIsArray(r) ?? ruleConditionalAndArrayIsArray(r) ?? ruleConditionalAndOptional(r) ?? ruleConditionalOptionalSimple(r) ?? ruleConditionalInMap(r) ?? ruleConditionalOptionalTruthy(r) ?? r;
}

function recurseExpr(e: TExpr): TExpr {
  const re = walkExpr;
  switch (e.kind) {
    case "var": case "num": case "str": case "bool":
    case "havoc":
      return e;
    case "binop": return { ...e, left: re(e.left), right: re(e.right) };
    case "unop": return { ...e, expr: re(e.expr) };
    case "call": return { ...e, fn: re(e.fn), args: e.args.map(re) };
    case "index": return { ...e, obj: re(e.obj), idx: re(e.idx) };
    case "field": return { ...e, obj: re(e.obj) };
    case "record": return { ...e, spread: e.spread ? re(e.spread) : null,
      fields: e.fields.map(f => ({ ...f, value: re(f.value) })) };
    case "arrayLiteral": return { ...e, elems: e.elems.map(re) };
    case "lambda": return { ...e, body: walkStmts(e.body) };
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

function walkStmt(s: TStmt): TStmt {
  // Recurse into children first, then try rules at this node.
  const r = recurseStmt(s);
  // Optional narrowing fires before Array.isArray narrowing: in a chain like
  // `next && Array.isArray(next.content)` the optional check must unwrap `next`
  // *outside* the array match, since `next.content` is unreachable until then.
  // (When the chain has no leading optional, ruleIfAndOptional no-ops and the
  // array rule fires; independent narrows commute, so the order is harmless.)
  // && rules fire before the simple rule because they produce nested ifs whose
  // inner shape doesn't match the simple rule directly.
  return ruleIfAndOptional(r) ?? ruleIfAndArrayIsArray(r) ?? ruleIfOptionalSimple(r) ?? ruleExprStmtAndOptional(r) ?? ruleOptionalIndexBinding(r) ?? r;
}

function walkStmts(stmts: TStmt[]): TStmt[] {
  const result: TStmt[] = [];
  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i];
    const rest = stmts.slice(i + 1);
    // Discriminant rules consume a prefix of stmts; remaining is processed normally.
    const tagged = ruleDiscriminantChain(stmts.slice(i)) ?? ruleDiscriminantNegEarlyReturn(stmts.slice(i));
    if (tagged) {
      result.push(walkStmt(tagged.stmt));
      i += tagged.consumed - 1;
      continue;
    }
    const consumed = ruleEarlyReturnOrChain(s, rest) ?? ruleEarlyReturnConsume(s, rest) ?? ruleEarlyReturnOptChainCompare(s, rest);
    if (consumed) {
      result.push(walkStmt(consumed));
      return result;
    }
    // walkStmt first — narrow's expression rules may rewrite the let init from
    // `conditional` to `someMatch`, in which case the let-cond desugar shouldn't fire.
    const walked = walkStmt(s);
    const expanded = ruleLetCondAndOptional(walked);
    if (expanded) {
      for (const x of expanded) result.push(walkStmt(x));
      continue;
    }
    result.push(walked);
  }
  return result;
}

function recurseStmt(s: TStmt): TStmt {
  const re = walkExpr;
  const rs = walkStmts;
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
    case "someMatch": return { ...s, someBody: rs(s.someBody), noneBody: rs(s.noneBody) };
    case "tagMatch": return { ...s, scrutinee: re(s.scrutinee),
      cases: s.cases.map(c => ({ ...c, body: rs(c.body) })),
      fallthrough: rs(s.fallthrough) };
  }
}

// `Some(0)` / `Some("")` / `Some(false)` are falsy, so a truthiness check
// (`if (o)`, `!o`, `o ? :`) over a nullable primitive must still test the bound
// value. Nullable objects/arrays are always truthy, and `!== undefined` is a pure
// presence check — neither needs the gate.
type Check = NonNullable<ReturnType<typeof parseOptionalCheck>>;
const canBeFalsy = (c: Check) => c.truthiness && ["int", "nat", "string", "bool"].includes(c.innerTy.kind);
const bound = (c: Check): TExpr => ({ kind: "var", name: c.binderHint, ty: c.innerTy });

// ── Rules ───────────────────────────────────────────────────

/** Rule: `if (e !== undefined) then else` where e is a simple optional var or
 *  `obj.field` chain, and the Some branch is non-empty.
 *  → `someMatch e { Some(_e_val) => then, None => else }`. */
function ruleIfOptionalSimple(s: TStmt): TStmt | null {
  if (s.kind !== "if") return null;
  const check = parseSimpleOptionalCheck(s.cond);
  if (!check) return null;
  const someBody = check.negated ? s.else : s.then;
  const noneBody = check.negated ? s.then : s.else;
  if (someBody.length === 0) return null;
  return {
    kind: "someMatch",
    scrutinee: check.scrutinee, binderTy: check.innerTy,
    binder: check.binderHint,
    someBody: canBeFalsy(check) ? [{ kind: "if", cond: bound(check), then: someBody, else: noneBody }] : someBody,
    noneBody,
  };
}

/** Rule: `if (e === undefined) terminate; rest` (early return / throw / break).
 *  → `someMatch e { Some(_e_val) => rest, None => terminate }`.
 *  Fires when the Some branch is empty AND there's a non-empty rest of the
 *  block — pulling the continuation into the narrowed scope. */
function ruleEarlyReturnConsume(s: TStmt, rest: TStmt[]): TStmt | null {
  if (s.kind !== "if") return null;
  if (rest.length === 0) return null;
  const check = parseSimpleOptionalCheck(s.cond);
  if (!check) return null;
  const someBranch = check.negated ? s.else : s.then;
  const noneBranch = check.negated ? s.then : s.else;
  if (someBranch.length !== 0) return null;
  if (!isTerminating(noneBranch)) return null;
  return {
    kind: "someMatch",
    scrutinee: check.scrutinee, binderTy: check.innerTy,
    binder: check.binderHint,
    someBody: canBeFalsy(check) ? [{ kind: "if", cond: bound(check), then: rest, else: noneBranch }] : rest,
    noneBody: noneBranch,
  };
}

/** Flatten a nested `||` chain into its leaf conditions. */
function flattenOr(e: TExpr): TExpr[] {
  if (e.kind === "binop" && e.op === "||") return [...flattenOr(e.left), ...flattenOr(e.right)];
  return [e];
}

/** A `||` disjunct that `x === None` makes true (so if every disjunct is false,
 *  `x` is Some). `residual` is the guard it still contributes once `x` is Some
 *  (`!v` for a falsy-capable `!x`; `v.chain !== lit` for an optchain compare;
 *  null otherwise). */
type NoneDetector = { scrutinee: TExpr; innerTy: Ty; binder: string; residual: TExpr | null };

function classifyDisjunct(leaf: TExpr): NoneDetector | null {
  // `x?.chain !== lit` — `undefined !== lit` is true when x is None.
  if (leaf.kind === "binop" && leaf.op === "!==") {
    const oc = leaf.left.kind === "optChain" ? leaf.left : leaf.right.kind === "optChain" ? leaf.right : null;
    if (oc && oc.kind === "optChain" && oc.obj.ty.kind === "optional") {
      const hint = binderHintFor(oc.obj);
      if (hint === null) return null;
      const binder = freshName(hint);
      const unwrapped = applyChain({ kind: "var", name: binder, ty: oc.obj.ty.inner }, oc.chain);
      if (unwrapped.kind === "field" && unwrapped.obj.ty.kind === "user") {
        const base = unwrapped.obj.ty.name.replace(/<.*/, "");
        const decl = _typeDecls.find(d => d.name === base);
        if (decl?.kind === "discriminated-union" && decl.discriminant === unwrapped.field) unwrapped.isDiscriminant = true;
      }
      const lit = leaf.left === oc ? leaf.right : leaf.left;
      return { scrutinee: oc.obj, innerTy: oc.obj.ty.inner, binder, residual: { kind: "binop", op: "!==", left: unwrapped, right: lit, ty: { kind: "bool" } } };
    }
  }
  // `!x` / `x === undefined`.
  const chk = parseOptionalCheck(leaf);
  if (chk && chk.negated) {
    const residual: TExpr | null = canBeFalsy(chk)
      ? { kind: "unop", op: "!", expr: { kind: "var", name: chk.binderHint, ty: chk.innerTy }, ty: { kind: "bool" } }
      : null;
    return { scrutinee: chk.scrutinee, innerTy: chk.innerTy, binder: chk.binderHint, residual };
  }
  return null;
}

/** Rule: `if (D1 || … || Dn) terminate; rest`. Each `Di` that detects some optional
 *  `x` is None (`!x`, `x === undefined`, `x?.chain !== lit`) narrows that `x` to Some
 *  across `rest`; the rest — value guards reading a narrowed `x` directly, plus the
 *  detectors' Some-case residuals — become a trailing early-return. Sound: reaching
 *  `rest` means every disjunct was false, so every detected optional is present.
 *  Covers `if (!x || x.f !== v) continue` / `if (x?.t !== 'm' || x.g) break`.
 *  Closes the resolve.ts:602 TODO ("|| narrowing"). */
function ruleEarlyReturnOrChain(s: TStmt, rest: TStmt[]): TStmt | null {
  if (s.kind !== "if") return null;
  if (rest.length === 0) return null;
  if (s.then.length === 0 || s.else.length !== 0 || !isTerminating(s.then)) return null;
  if (s.cond.kind !== "binop" || s.cond.op !== "||") return null;  // single check is the simpler rule
  const leaves = flattenOr(s.cond);
  if (leaves.length < 2) return null;

  const detectors: NoneDetector[] = [];
  const residualLeaves: TExpr[] = [];
  const seen = new Set<string>();
  for (const leaf of leaves) {
    const d = classifyDisjunct(leaf);
    if (!d) { residualLeaves.push(leaf); continue; }
    const key = binderHintFor(d.scrutinee)!;
    if (seen.has(key)) return null;  // two detectors on one optional: rare; leave to other rules
    seen.add(key);
    detectors.push(d);
    if (d.residual) residualLeaves.push(d.residual);
  }
  if (detectors.length === 0) return null;

  let inner: TStmt[] = residualLeaves.length === 0
    ? rest
    : [{ kind: "if", cond: residualLeaves.reduce((a, b): TExpr => ({ kind: "binop", op: "||", left: a, right: b, ty: { kind: "bool" } })), then: s.then, else: [] }, ...rest];
  for (let i = detectors.length - 1; i >= 0; i--) {
    const d = detectors[i]!;
    inner = [{ kind: "someMatch", scrutinee: d.scrutinee, binderTy: d.innerTy, binder: d.binder, someBody: inner, noneBody: s.then }];
  }
  return inner[0];
}

/** Rule: `if (opt?.chain !== lit) terminate; rest` where `opt` is optional.
 *  `opt?.chain` is `undefined` when `opt` is None, and `undefined !== lit` is
 *  true, so the None case takes the terminating branch — falling through to
 *  `rest` proves `opt` is Some. Rewrite to
 *    someMatch opt { Some(v) => [if (v.chain !== lit) terminate; rest]; None => terminate }
 *  narrowing `opt` to `v` across `rest` (transform substitutes the scrutinee) and
 *  handing the now-non-optional inner guard to the ordinary rules (e.g.
 *  discriminant narrowing). Bound-optional companion to ruleEarlyReturnConsume,
 *  which handles only a bare presence check (`opt !== undefined`). Restricted to
 *  `!==` so the None case is guaranteed to terminate. */
function ruleEarlyReturnOptChainCompare(s: TStmt, rest: TStmt[]): TStmt | null {
  if (s.kind !== "if") return null;
  if (rest.length === 0) return null;
  if (s.else.length !== 0 || !isTerminating(s.then)) return null;
  const c = s.cond;
  if (c.kind !== "binop" || c.op !== "!==") return null;
  const oc = c.left.kind === "optChain" ? c.left : c.right.kind === "optChain" ? c.right : null;
  if (!oc || oc.kind !== "optChain" || oc.obj.ty.kind !== "optional") return null;
  const lit = c.left === oc ? c.right : c.left;
  const innerTy = oc.obj.ty.inner;
  const hint = binderHintFor(oc.obj);
  if (hint === null) return null;
  const binder = freshName(hint);
  const binderVar: TExpr = { kind: "var", name: binder, ty: innerTy };
  const unwrapped = applyChain(binderVar, oc.chain);
  // applyChain rebuilds the field without the `isDiscriminant` flag resolve sets
  // on a direct `x.disc`; restore it when the unwrapped access is the binder
  // union's discriminant, so the inner guard feeds discriminant narrowing.
  if (unwrapped.kind === "field" && unwrapped.obj.ty.kind === "user") {
    const base = unwrapped.obj.ty.name.replace(/<.*/, "");
    const decl = _typeDecls.find(d => d.name === base);
    if (decl?.kind === "discriminated-union" && decl.discriminant === unwrapped.field) {
      unwrapped.isDiscriminant = true;
    }
  }
  const innerGuard: TExpr = { kind: "binop", op: "!==", left: unwrapped, right: lit, ty: { kind: "bool" } };
  // Keep `rest` as trailing statements (not an else branch) — `s.then` terminates,
  // so `if (g) terminate; rest` ≡ `if (g) terminate else rest`, and the trailing
  // form lets the ordinary early-exit rules (e.g. discriminant narrowing) fire on
  // the now-non-optional inner guard when `chain` is a union discriminant.
  const someBody: TStmt[] = [{ kind: "if", cond: innerGuard, then: s.then, else: [] }, ...rest];
  return { kind: "someMatch", scrutinee: oc.obj, binder, binderTy: innerTy, someBody, noneBody: s.then };
}

/** Rule (expression): `e !== undefined ? a : b`. */
function ruleConditionalOptionalSimple(e: TExpr): TExpr | null {
  if (e.kind !== "conditional") return null;
  const check = parseOptionalCheck(e.cond);
  if (!check) return null;
  const someBody = check.negated ? e.else : e.then;
  const noneBody = check.negated ? e.then : e.else;
  return {
    kind: "someMatch",
    scrutinee: check.scrutinee, binderTy: check.innerTy,
    binder: check.binderHint,
    someBody: canBeFalsy(check) ? { kind: "conditional", cond: bound(check), then: someBody, else: noneBody, ty: e.ty } : someBody,
    noneBody,
    ty: e.ty,
  };
}

/** Rule (expression): `Array.isArray(x) ==> B` or `!Array.isArray(x) ==> B` —
 *  premise narrowing for spec implications. Mirrors `ruleImplOptional` but for
 *  synth array-union discriminators.
 *  → `tagMatch x { ArrayBranch => walkExpr(B), _ => true }` (or NonArrayBranch).
 *  The other variant becomes a vacuous-true fallthrough (the implication is
 *  trivially satisfied when the premise is false). */
function ruleImplArrayIsArray(e: TExpr): TExpr | null {
  if (e.kind !== "binop" || e.op !== "==>") return null;
  const pos = parseArrayIsArrayCall(e.left);
  const neg = e.left.kind === "unop" && e.left.op === "!"
    ? parseArrayIsArrayCall(e.left.expr)
    : null;
  const matched = pos ?? (neg ? { scrutinee: neg.scrutinee, typeName: neg.typeName, variant: "NonArrayBranch" as const } : null);
  if (!matched) return null;
  return {
    kind: "tagMatch",
    scrutinee: matched.scrutinee,
    typeName: matched.typeName,
    cases: [{ variant: matched.variant, body: walkExpr(e.right) }],
    fallthrough: { kind: "bool", value: true, ty: { kind: "bool" } },
    ty: { kind: "bool" },
  };
}

/** Rule (expression): `Array.isArray(x) ? a : b` — ternary narrowing for
 *  synth array-unions. Mirrors `ruleImplArrayIsArray` but at the conditional
 *  position rather than the `==>` position.
 *  → `tagMatch x { ArrayBranch => walkExpr(a) } fallthrough walkExpr(b)`
 *  (or NonArrayBranch when the condition is negated).
 *  Inside the matched arm, bare references to `x` are rewritten to the
 *  variant's payload field (e.g. `x.arr`) by `transformExpr` when emitting
 *  the tagMatch — same mechanism `ruleImplArrayIsArray` already relies on. */
function ruleConditionalArrayIsArray(e: TExpr): TExpr | null {
  if (e.kind !== "conditional") return null;
  const pos = parseArrayIsArrayCall(e.cond);
  // `typeof x === "string"` is a positive check like `Array.isArray`, but selects
  // the NonArrayBranch — its then-branch is the matched-variant body.
  const tof = pos ? null : parseTypeofStringCheck(e.cond);
  const neg = !pos && !tof && e.cond.kind === "unop" && e.cond.op === "!"
    ? parseArrayIsArrayCall(e.cond.expr)
    : null;
  const matched = pos ?? tof ?? (neg ? { scrutinee: neg.scrutinee, typeName: neg.typeName, variant: "NonArrayBranch" as const } : null);
  if (!matched) return null;
  const positive = pos ?? tof;
  const thenBody = positive ? e.then : e.else;
  const elseBody = positive ? e.else : e.then;
  return {
    kind: "tagMatch",
    scrutinee: matched.scrutinee,
    typeName: matched.typeName,
    cases: [{ variant: matched.variant, body: walkExpr(thenBody) }],
    fallthrough: walkExpr(elseBody),
    ty: e.ty,
  };
}

/** Rule (expression): `(path !== undefined [&& rest]) ==> B` — premise narrowing
 *  for spec implications (ensures/requires). The premise's optional checks
 *  bind narrowed values that the conclusion can use.
 *  → `someMatch path { Some(_p_val) => (rest ==> B), None => true }`.
 *  Walks the inner ==> recursively so chained checks (`a !== undefined && a.b !== undefined ==> ...`) become nested someMatches. */
function ruleImplOptional(e: TExpr): TExpr | null {
  if (e.kind !== "binop" || e.op !== "==>") return null;
  let check: NonNullable<ReturnType<typeof parseSimpleOptionalCheck>>;
  let restCond: TExpr | null = null;
  const extracted = extractLeftmostOptionalCheck(e.left);
  if (extracted) {
    check = extracted.check;
    restCond = extracted.restCond;
  } else {
    const c = parseSimpleOptionalCheck(e.left);
    if (!c || c.negated) return null;
    check = c;
  }
  const innerBody: TExpr = restCond
    ? { kind: "binop", op: "==>", left: restCond, right: e.right, ty: { kind: "bool" } }
    : e.right;
  return {
    kind: "someMatch",
    scrutinee: check.scrutinee, binderTy: check.innerTy,
    binder: check.binderHint,
    someBody: walkExpr(innerBody),
    noneBody: { kind: "bool", value: true, ty: { kind: "bool" } },
    ty: { kind: "bool" },
  };
}

type OptChain = Extract<TExpr, { kind: "optChain" }>;

/** Apply an optional chain's steps (field / index / call) to a base expr —
 *  shared by `ruleOptChain` (base = binder) and `ruleOptChainIndex` (base = arr[i]). */
function applyChain(body: TExpr, chain: OptChain["chain"]): TExpr {
  for (const step of chain) {
    if (step.kind === "field") body = { kind: "field", obj: body, field: step.name, ty: step.ty };
    else if (step.kind === "index") body = { kind: "index", obj: body, idx: step.idx, ty: step.ty };
    else body = { kind: "call", fn: body, args: step.args, ty: step.ty, callKind: step.callKind };
  }
  return body;
}

/** `0 <= idx && idx < arr.length` — the in-bounds guard for an array index. */
function arrayBoundsCond(arr: TExpr, idx: TExpr): TExpr {
  const len: TExpr = { kind: "field", obj: arr, field: "length", ty: { kind: "int" } };
  const lo: TExpr = { kind: "binop", op: "<=", left: { kind: "num", value: 0, ty: { kind: "int" } }, right: idx, ty: { kind: "bool" } };
  const hi: TExpr = { kind: "binop", op: "<", left: idx, right: len, ty: { kind: "bool" } };
  return { kind: "binop", op: "&&", left: lo, right: hi, ty: { kind: "bool" } };
}

/** Rule (expression): `left ?? right` — nullish coalescing.
 *  → `someMatch left { Some(_v) => _v, None => right }`.
 *  Single-evaluation: scrutinee may be any expression. */
function ruleNullish(e: TExpr): TExpr | null {
  if (e.kind !== "nullish") return null;
  if (e.left.ty.kind !== "optional") return null;
  const innerTy = e.left.ty.inner;
  const binder = freshName(`_oc${_ocCounter++}_val`);
  return {
    kind: "someMatch",
    scrutinee: e.left, binder, binderTy: innerTy,
    someBody: { kind: "var", name: binder, ty: innerTy },
    noneBody: e.right,
    ty: e.ty,
  };
}

/** Rule (expression): `arr[i] ?? right` — nullish coalescing on an array index.
 *  Under noUncheckedIndexedAccess `arr[i]` is `T | undefined`, undefined exactly
 *  when out of bounds, so → `(0 <= i && i < arr.length) ? arr[i] : right`. The
 *  guarded `then` keeps the seq index in bounds for the backend. (Map index is
 *  already optional-typed and handled by ruleNullish above; this is the array
 *  case, whose element type stays non-optional in expression position.) */
function ruleNullishIndex(e: TExpr): TExpr | null {
  if (e.kind !== "nullish") return null;
  if (e.left.kind !== "index") return null;
  if (e.left.obj.ty.kind !== "array") return null;
  const cond = arrayBoundsCond(e.left.obj, e.left.idx);
  return { kind: "conditional", cond, then: e.left, else: e.right, ty: e.ty };
}

/** Rule (expression): `arr[i]?.<chain>` — optional chaining on an array index,
 *  the optChain sibling of ruleNullishIndex. `arr[i]` is `T | undefined`,
 *  undefined exactly out of bounds, so → `(0 <= i && i < arr.length) ? <chain on
 *  arr[i]> : undefined`. The conditional's optional type makes transform wrap the
 *  in-bounds chain result in Some and the OOB branch in None — the same Option<…>
 *  a directly-optional scrutinee yields via ruleOptChain, just bounds-guarded.
 *  (ruleOptChain itself bails here: an array index is typed as the non-optional
 *  element type, so its `?.` never reaches that rule.) */
function ruleOptChainIndex(e: TExpr): TExpr | null {
  if (e.kind !== "optChain") return null;
  if (e.obj.kind !== "index") return null;
  if (e.obj.obj.ty.kind !== "array") return null;
  const cond = arrayBoundsCond(e.obj.obj, e.obj.idx);
  const body = applyChain(e.obj, e.chain); // arr[i] — in bounds under `cond`
  const undef: TExpr = { kind: "var", name: "undefined", ty: { kind: "void" } };
  return { kind: "conditional", cond, then: body, else: undef, ty: e.ty };
}

/** Rule (statement): reconcile a `const e = arr[i]` whose binding is optional
 *  (`e: T | undefined`) but whose array-index initializer is total (`T`). Model
 *  the index as its JS semantics — `e := (0 <= i && i < arr.length) ? arr[i] :
 *  undefined` — so `e` is a real `Option<T>` and a later `e?.f` someMatch is
 *  well-typed; an in-bounds proof makes the None branch dead, so safely-indexed
 *  code verifies as if total. Bound-form sibling of ruleOptChainIndex /
 *  ruleNullishIndex. Fires purely on the optional-binding/total-index shape (the
 *  usual source is `noUncheckedIndexedAccess`, but the flag itself is never
 *  checked). Skipped when the element type is already optional: no mismatch. */
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

/** Rule (expression): `obj?.<chain>` — single-eval optional chain.
 *  → `someMatch obj { Some(_oc{N}_val) => apply(chain, _oc{N}_val), None => undefined }`.
 *  The someBody applies the chain to the binder directly (field/call/index),
 *  so transform doesn't substitute. Scrutinee can be any expression. */
function ruleOptChain(e: TExpr): TExpr | null {
  if (e.kind !== "optChain") return null;
  if (e.obj.ty.kind !== "optional") return null;
  const innerTy = e.obj.ty.inner;
  const binder = freshName(`_oc${_ocCounter++}_val`);
  const body = applyChain({ kind: "var", name: binder, ty: innerTy }, e.chain);
  const noneBody: TExpr = { kind: "var", name: "undefined", ty: { kind: "void" } };
  return {
    kind: "someMatch",
    scrutinee: e.obj, binder, binderTy: innerTy,
    someBody: body, noneBody, ty: e.ty,
  };
}

/** Minimal structural equality on the IR shapes we narrow against: var, field
 *  chain, and index (with pure key). Enough to recognize `m[k]` on both sides
 *  of a `k in m ? m[k] : default` ternary. */
function exprEqual(a: TExpr, b: TExpr): boolean {
  if (a.kind !== b.kind) return false;
  if (a.kind === "var" && b.kind === "var") return a.name === b.name;
  if (a.kind === "field" && b.kind === "field")
    return a.field === b.field && exprEqual(a.obj, b.obj);
  if (a.kind === "index" && b.kind === "index")
    return exprEqual(a.obj, b.obj) && exprEqual(a.idx, b.idx);
  return false;
}

/** Produce a reader-friendly binder hint for `m[k]` when both m and k are
 *  access-path shaped (var / field chain). Falls back to a generic counter
 *  name for computed keys. */
function binderHintForMapAccess(m: TExpr, k: TExpr): string {
  const mHint = binderHintFor(m);
  const kHint = binderHintFor(k);
  if (mHint && kHint) {
    // mHint is `_m_val`, kHint is `_k_val` — stitch into `_m_k_val`.
    const mStem = mHint.replace(/_val$/, "");
    const kStem = kHint.replace(/^_/, "").replace(/_val$/, "");
    return freshName(`${mStem}_${kStem}_val`);
  }
  return freshName(`_oc${_ocCounter++}_val`);
}

/** Rule (expression): `k in m ? m[k] : default` where m is map-typed.
 *  The then-branch must be exactly `m[k]` (same obj, same key). This mirrors
 *  the discriminant-`in` path (line 438) but gated on `map` instead of `user`.
 *  → `someMatch m[k] { Some(_m_k_val) => _m_k_val, None => default }`.
 *  The existing Dafny peephole collapses the result to
 *  `if k in m then m[k] else default`. */
function ruleConditionalInMap(e: TExpr): TExpr | null {
  if (e.kind !== "conditional") return null;
  if (e.cond.kind !== "binop" || e.cond.op !== "in") return null;
  const m = e.cond.right;
  const k = e.cond.left;
  if (m.ty.kind !== "map") return null;
  // Then-branch must be exactly m[k].
  if (e.then.kind !== "index") return null;
  if (!exprEqual(e.then.obj, m) || !exprEqual(e.then.idx, k)) return null;
  // Only narrow when the else branch has a concrete non-optional type — otherwise
  // the overall ternary could legitimately be Option<V> (e.g., `k in m ? m[k] : undefined`).
  if (e.else.ty.kind === "optional" || e.else.ty.kind === "void") return null;
  // Dormant backup: when resolve's in-atom narrowing has already fired, e.then.ty is V,
  // not Option<V>. The `someMatch` scrutinee would then have the wrong shape. Skip —
  // the enclosing expression is already a plain if-then-else of the correct type.
  if (e.then.ty.kind !== "optional") return null;
  const innerTy = m.ty.value;
  const binder = binderHintForMapAccess(m, k);
  return {
    kind: "someMatch",
    scrutinee: e.then, binder, binderTy: innerTy,
    someBody: { kind: "var", name: binder, ty: innerTy },
    noneBody: e.else, ty: innerTy,
  };
}

/** Rule (expression): `opt ? a : b` (truthiness — cond itself is optional).
 *  Only fires for simple var or simple `obj.field` cond. */
function ruleConditionalOptionalTruthy(e: TExpr): TExpr | null {
  if (e.kind !== "conditional") return null;
  if (e.cond.ty.kind !== "optional") return null;
  const hint = binderHintFor(e.cond);
  if (hint === null) return null;
  const binder = freshName(hint);
  return {
    kind: "someMatch",
    scrutinee: e.cond, binderTy: e.cond.ty.inner,
    binder,
    someBody: e.then, noneBody: e.else, ty: e.ty,
  };
}

/** Find the leftmost `parse`-matching conjunct anywhere in an `&&` chain,
 *  returning it plus the remaining conjunction. Conjunct order doesn't carry
 *  semantic weight, so either side is fine. Shared by the optional and
 *  Array.isArray chain extractors — they differ only in `parse`.
 *  `(x !== undefined && b) && c` → { check, restCond: b && c }. */
function extractLeftmostCheck<C>(cond: TExpr, parse: (e: TExpr) => C | null): { check: C; restCond: TExpr } | null {
  if (cond.kind !== "binop" || cond.op !== "&&") return null;
  const left = parse(cond.left);
  if (left) return { check: left, restCond: cond.right };
  const right = parse(cond.right);
  if (right) return { check: right, restCond: cond.left };
  if (cond.left.kind === "binop" && cond.left.op === "&&") {
    const inner = extractLeftmostCheck(cond.left, parse);
    if (inner) return { check: inner.check, restCond: { ...cond, left: inner.restCond } as TExpr };
  }
  if (cond.right.kind === "binop" && cond.right.op === "&&") {
    const inner = extractLeftmostCheck(cond.right, parse);
    if (inner) return { check: inner.check, restCond: { ...cond, right: inner.restCond } as TExpr };
  }
  return null;
}

/** `&&`-chain extractor for a positive optional check. */
function extractLeftmostOptionalCheck(cond: TExpr) {
  return extractLeftmostCheck(cond, e => {
    const c = parseSimpleOptionalCheck(e);
    return c && !c.negated ? c : null;
  });
}

/** Rule: `if (x !== undefined && rest) then` (no else) where x is a pure
 *  access path.
 *  → `someMatch x { Some(_x_val) => if rest then then; , None => {} }`.
 *  Walks the inner if back through narrow so that nested optional checks in rest
 *  (`a !== undefined && a.b !== undefined && ...`) also become someMatches. */
function ruleIfAndOptional(s: TStmt): TStmt | null {
  if (s.kind !== "if") return null;
  if (s.else.length !== 0) return null;
  const extracted = extractLeftmostOptionalCheck(s.cond);
  if (!extracted) return null;
  const { check, restCond } = extracted;
  const innerIf: TStmt = { kind: "if", cond: restCond, then: s.then, else: [] };
  const someBody: TStmt[] = canBeFalsy(check)
    ? [{ kind: "if", cond: bound(check), then: [walkStmt(innerIf)], else: [] }]
    : [walkStmt(innerIf)];
  return {
    kind: "someMatch",
    scrutinee: check.scrutinee, binderTy: check.innerTy,
    binder: check.binderHint,
    someBody,
    noneBody: [],
  };
}

/** Rule: a bare expression statement `x !== undefined && rest` (the `if`-less
 *  guard idiom, TS-equivalent to `if (x !== undefined) rest;`) where `x` is a
 *  pure access path.
 *  → `someMatch x { Some(_x_val) => rest;, None => {} }`.
 *  Runs `rest` for effect inside the narrowed scope. Wrapping `rest` as an
 *  expr-statement and walking it lets chained checks
 *  (`a !== undefined && a.b !== undefined && a.b.f()`) nest into someMatches.
 *  Unlike the ternary rule (`ruleConditionalAndOptional`), a method call in
 *  `rest` is fine here: a statement-level someMatch arm keeps it in statement
 *  position, so transform never ANF-lifts it out of the arm (which would drop
 *  the guard and reference the un-narrowed optional). */
function ruleExprStmtAndOptional(s: TStmt): TStmt | null {
  if (s.kind !== "expr") return null;
  if (s.expr.kind !== "binop" || s.expr.op !== "&&") return null;
  const extracted = extractLeftmostOptionalCheck(s.expr);
  if (!extracted) return null;
  const { check, restCond } = extracted;
  const innerStmt: TStmt = { kind: "expr", expr: restCond };
  const someBody: TStmt[] = canBeFalsy(check)
    ? [{ kind: "if", cond: bound(check), then: [walkStmt(innerStmt)], else: [] }]
    : [walkStmt(innerStmt)];
  return {
    kind: "someMatch",
    scrutinee: check.scrutinee, binderTy: check.innerTy,
    binder: check.binderHint,
    someBody,
    noneBody: [],
  };
}

// ── Discriminant narrowing ──────────────────────────────────

/** Detect `Array.isArray(<path>)` where `<path>` is a var or a chain of
 *  field accesses rooted at a var, and the path's type is a synthesized
 *  array-union (discriminant `"__isArray__"`). Returns the variant name to
 *  narrow to. The scrutinee is whatever path the user wrote — downstream
 *  transforms substitute it inside the matched arm. */
function parseArrayIsArrayCall(call: TExpr): { scrutinee: TExpr; typeName: string; variant: "ArrayBranch" } | null {
  if (call.kind !== "call") return null;
  if (call.fn.kind !== "field" || call.fn.field !== "isArray") return null;
  if (call.fn.obj.kind !== "var" || call.fn.obj.name !== "Array") return null;
  if (call.args.length !== 1) return null;
  const arg = call.args[0];
  if (!isNarrowablePath(arg) || arg.ty.kind !== "user") return null;
  const baseTyName = arg.ty.name.includes("<") ? arg.ty.name.slice(0, arg.ty.name.indexOf("<")) : arg.ty.name;
  const decl = _typeDecls.find(d => d.name === baseTyName);
  if (decl?.kind !== "discriminated-union" || decl.discriminant !== "__isArray__") return null;
  return { scrutinee: arg, typeName: arg.ty.name, variant: "ArrayBranch" };
}

/** Detect `typeof <path> === "string"` where `<path>`'s type is a synth array-
 *  union (`U | T[]`) AND its `NonArrayBranch` payload `U` is itself `string`.
 *  The runtime `=== "string"` test matches that branch only when `U` is string —
 *  for any other non-array payload (`number | T[]`, …) it never holds, so we must
 *  NOT narrow. Returns the `NonArrayBranch` variant; the dual of `Array.isArray`. */
function parseTypeofStringCheck(e: TExpr): { scrutinee: TExpr; typeName: string; variant: "NonArrayBranch" } | null {
  if (e.kind !== "binop" || e.op !== "===") return null;
  const tof = e.left.kind === "unop" && e.left.op === "typeof" ? e.left.expr
    : e.right.kind === "unop" && e.right.op === "typeof" ? e.right.expr : null;
  const lit = e.left.kind === "str" ? e.left.value : e.right.kind === "str" ? e.right.value : null;
  if (!tof || lit !== "string") return null;
  if (!isNarrowablePath(tof) || tof.ty.kind !== "user") return null;
  const baseTyName = tof.ty.name.includes("<") ? tof.ty.name.slice(0, tof.ty.name.indexOf("<")) : tof.ty.name;
  const decl = _typeDecls.find(d => d.name === baseTyName);
  if (decl?.kind !== "discriminated-union" || decl.discriminant !== "__isArray__") return null;
  const valTy = decl.variants?.find(v => v.name === "NonArrayBranch")?.fields.find(f => f.name === "val")?.type;
  if (valTy?.kind !== "string") return null;   // guard: the non-array branch must actually be `string`
  return { scrutinee: tof, typeName: tof.ty.name, variant: "NonArrayBranch" };
}

/** A "narrowable path" is a var or a chain of field accesses rooted at a var
 *  — i.e., pure and structurally addressable, so transforms can substitute
 *  occurrences inside a matched arm without worrying about re-evaluation. */
function isNarrowablePath(e: TExpr): boolean {
  if (e.kind === "var") return true;
  if (e.kind === "field") return isNarrowablePath(e.obj);
  return false;
}

/** `&&`-chain extractor for `Array.isArray(path)` (positive form only — a negated
 *  `!Array.isArray(...)` would narrow to the wrong variant for then-body consumers,
 *  so those are left to the untouched-conditional path). */
function extractLeftmostArrayIsArrayCheck(cond: TExpr) {
  return extractLeftmostCheck(cond, parseArrayIsArrayCall);
}

/** Detect `x.kind === "variant"`, `'key' in x`, or `Array.isArray(x)` (synth
 *  array-union) as a positive discriminant check. Returns the scrutinee var
 *  (with its type), type name, and variant. */
function parseDiscriminantCond(cond: TExpr): { scrutinee: TExpr & { kind: "var" }; typeName: string; variant: string } | null {
  // Pattern: x.discriminant === "variant"
  if (cond.kind === "binop" && cond.op === "===" && cond.right.kind === "str" &&
      cond.left.kind === "field" && cond.left.isDiscriminant &&
      cond.left.obj.kind === "var" && cond.left.obj.ty.kind === "user") {
    return { scrutinee: cond.left.obj, typeName: cond.left.obj.ty.name, variant: cond.right.value };
  }
  // Pattern: 'key' in x — narrows x to the unique variant containing `key`.
  if (cond.kind === "binop" && cond.op === "in" &&
      cond.left.kind === "str" && cond.right.kind === "var" &&
      cond.right.ty.kind === "user") {
    const key = cond.left.value;
    const typeName = cond.right.ty.name;
    const baseTyName = typeName.includes("<") ? typeName.slice(0, typeName.indexOf("<")) : typeName;
    const decl = _typeDecls.find(d => d.name === baseTyName);
    if (decl?.kind === "discriminated-union" && decl.variants) {
      const matches = decl.variants.filter(v => v.fields.some(f => f.name === key));
      if (matches.length === 1) {
        return { scrutinee: cond.right, typeName, variant: matches[0].name };
      }
    }
  }
  // Pattern: Array.isArray(x) — narrows x to the ArrayBranch variant of a
  // synthesized array-union (discriminant "__isArray__"). Statement-level
  // discriminant chains (`if (Array.isArray(x)) {...} else if (...)`) still
  // require a bare-var scrutinee since the existing var-name-keyed
  // replacement machinery in transform.ts only handles that shape; path
  // scrutinees (e.g. `m.content`) are handled exclusively by
  // `ruleConditionalArrayIsArray` and the expression-form tagMatch path.
  const arrCheck = parseArrayIsArrayCall(cond);
  if (arrCheck && arrCheck.scrutinee.kind === "var") {
    return { scrutinee: arrCheck.scrutinee, typeName: arrCheck.typeName, variant: arrCheck.variant };
  }
  return null;
}

/** Detect `x.kind !== "variant"` (negative discriminant check) or
 *  `!Array.isArray(x)` (synth array-union, narrows to NonArrayBranch). */
function parseNegativeDiscriminantCond(cond: TExpr): { scrutinee: TExpr & { kind: "var" }; typeName: string; variant: string } | null {
  if (cond.kind === "binop" && cond.op === "!==" && cond.right.kind === "str" &&
      cond.left.kind === "field" && cond.left.isDiscriminant &&
      cond.left.obj.kind === "var" && cond.left.obj.ty.kind === "user") {
    return { scrutinee: cond.left.obj, typeName: cond.left.obj.ty.name, variant: cond.right.value };
  }
  // Pattern: !Array.isArray(x) — narrows x to the NonArrayBranch variant.
  // Same var-scrutinee restriction as parseDiscriminantCond.
  if (cond.kind === "unop" && cond.op === "!") {
    const arrCheck = parseArrayIsArrayCall(cond.expr);
    if (arrCheck && arrCheck.scrutinee.kind === "var") {
      return { scrutinee: arrCheck.scrutinee, typeName: arrCheck.typeName, variant: "NonArrayBranch" };
    }
  }
  return null;
}

function isTerminating(stmts: TStmt[]): boolean {
  if (stmts.length === 0) return false;
  return isTerminatorKind(stmts[stmts.length - 1].kind);
}

/** Rule (list-level): consecutive `if (x.kind === "v") ...` chain → tagMatch.
 *  Walks consecutive top-level ifs on the same discriminator var; the first
 *  one with an else-branch ends the chain (else becomes fallthrough; if-else-if
 *  flattens into more cases). Returns the tagMatch and how many stmts consumed. */
function ruleDiscriminantChain(stmts: TStmt[]): { stmt: TStmt; consumed: number } | null {
  if (stmts.length === 0 || stmts[0].kind !== "if") return null;
  const first = parseDiscriminantCond(stmts[0].cond);
  if (!first) return null;

  const cases: { variant: string; body: TStmt[] }[] = [];

  function collectElse(s: TStmt & { kind: "if" }): TStmt[] {
    const p = parseDiscriminantCond(s.cond);
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
    const p = parseDiscriminantCond(s.cond);
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

/** Rule (list-level): `if (x.kind !== "v") terminate; rest` → tagMatch
 *  with cases = [{ variant: v, body: rest }] and fallthrough = terminate. */
function ruleDiscriminantNegEarlyReturn(stmts: TStmt[]): { stmt: TStmt; consumed: number } | null {
  if (stmts.length < 2) return null;
  const first = stmts[0];
  if (first.kind !== "if" || first.else.length > 0) return null;
  if (!isTerminating(first.then)) return null;
  const cond = parseNegativeDiscriminantCond(first.cond);
  if (!cond) return null;
  return { stmt: { kind: "tagMatch", scrutinee: cond.scrutinee, typeName: cond.typeName,
    cases: [{ variant: cond.variant, body: stmts.slice(1) }], fallthrough: first.then },
    consumed: stmts.length };
}

/** Rule (statement): `let x = (e_opt && rest) ? a : b` where rest may contain
 *  method calls. → `var x: T := b; someMatch e_opt { Some(_v) => { if rest { x := a } } }`.
 *  Statement-level form is needed because Dafny doesn't allow method calls
 *  inside match expression arms. */
function ruleLetCondAndOptional(s: TStmt): TStmt[] | null {
  if (s.kind !== "let" || s.mutable) return null;
  if (s.init.kind !== "conditional") return null;
  const extracted = extractLeftmostOptionalCheck(s.init.cond);
  if (!extracted) return null;
  const { check, restCond } = extracted;
  const assignIf: TStmt = { kind: "if", cond: restCond,
    then: [{ kind: "assign", target: s.name, value: s.init.then }], else: [] };
  const someBody: TStmt[] = canBeFalsy(check)
    ? [{ kind: "if", cond: bound(check), then: [assignIf], else: [] }]
    : [assignIf];
  const sm: TStmt = {
    kind: "someMatch",
    scrutinee: check.scrutinee, binderTy: check.innerTy,
    binder: check.binderHint,
    someBody,
    noneBody: [],
  };
  return [
    { kind: "let", name: s.name, ty: s.ty, mutable: true, init: s.init.else },
    sm,
  ];
}

/** Built-in collection methods that lower to pure Dafny expressions
 *  (`x in arr`, `x in m`, `x in s`, `|s|`, `s.Keys`, etc.) even though they
 *  carry `callKind: "method"` from resolve. Safe inside match arms. */
const PURE_BUILTIN_METHODS = new Set([
  "includes", "has", "size", "length", "keys", "values",
]);

/** Does this expression contain a method call that would be lifted to a
 *  var binding outside its containing expression by transform? Such calls
 *  are unsafe inside a match arm — the lifted binding would reference a
 *  name only valid in the arm. Built-in pure methods are exempt. */
function containsMethodCall(e: TExpr): boolean {
  if (e.kind === "call" && e.callKind === "method" &&
      !(e.fn.kind === "field" && PURE_BUILTIN_METHODS.has(e.fn.field))) {
    return true;
  }
  switch (e.kind) {
    case "var": case "num": case "str": case "bool":
    case "havoc":
      return false;
    case "binop": return containsMethodCall(e.left) || containsMethodCall(e.right);
    case "unop": return containsMethodCall(e.expr);
    case "call": return containsMethodCall(e.fn) || e.args.some(containsMethodCall);
    case "index": return containsMethodCall(e.obj) || containsMethodCall(e.idx);
    case "field": return containsMethodCall(e.obj);
    case "record":
      return (e.spread ? containsMethodCall(e.spread) : false) ||
        e.fields.some(f => containsMethodCall(f.value));
    case "arrayLiteral": return e.elems.some(containsMethodCall);
    case "lambda": return false;  // body is its own scope
    case "conditional":
      return containsMethodCall(e.cond) || containsMethodCall(e.then) || containsMethodCall(e.else);
    case "optChain": return containsMethodCall(e.obj);
    case "nullish": return containsMethodCall(e.left) || containsMethodCall(e.right);
    case "forall": case "exists": return containsMethodCall(e.body);
    case "someMatch": return containsMethodCall(e.scrutinee) ||
      containsMethodCall(e.someBody) || containsMethodCall(e.noneBody);
    case "tagMatch": return containsMethodCall(e.scrutinee) ||
      e.cases.some(c => containsMethodCall(c.body)) ||
      (e.fallthrough ? containsMethodCall(e.fallthrough) : false);
  }
}

/** Rule (expression): `x !== undefined && rest ? a : b`.
 *  → `someMatch x { Some(_x_val) => if rest then a else b, None => b }`.
 *  Walks the inner conditional back through narrow so chained checks
 *  (`a !== undefined && a.b !== undefined ? ... : ...`) become nested
 *  someMatches rather than leaving inner optional checks as raw conditionals.
 *  Does NOT fire if the guard `rest` contains method calls — transform lifts
 *  those out of the match arm, breaking the binder scope. The original
 *  transform's let-desugar (transformStmt let-case) handles those by lifting
 *  to a mutable var first. */
function ruleConditionalAndOptional(e: TExpr): TExpr | null {
  if (e.kind !== "conditional") return null;
  const extracted = extractLeftmostOptionalCheck(e.cond);
  if (!extracted) return null;
  const { check, restCond } = extracted;
  if (containsMethodCall(restCond)) return null;
  const innerCond: TExpr = {
    kind: "conditional",
    cond: restCond, then: e.then, else: e.else, ty: e.ty,
  };
  const someExpr = walkExpr(innerCond);
  const someBody: TExpr = canBeFalsy(check)
    ? { kind: "conditional", cond: bound(check), then: someExpr, else: e.else, ty: e.ty }
    : someExpr;
  return {
    kind: "someMatch",
    scrutinee: check.scrutinee, binderTy: check.innerTy,
    binder: check.binderHint,
    someBody, noneBody: e.else, ty: e.ty,
  };
}

/** Rule (statement): `if (<rest> && Array.isArray(path) && <more>) then [else]`
 *  → `tagMatch path { ArrayBranch => if (<rest && more>) then [else] }`.
 *  The remaining conjuncts move inside the matched arm so any narrowing the
 *  `then` body relies on (typed `path` accesses) sees the unwrapped variant.
 *  Mirrors `ruleIfAndOptional` but for synth array-unions. */
function ruleIfAndArrayIsArray(s: TStmt): TStmt | null {
  if (s.kind !== "if") return null;
  const extracted = extractLeftmostArrayIsArrayCheck(s.cond);
  if (!extracted) return null;
  const { check, restCond } = extracted;
  // Inner if uses the remaining conjunction (or just the then-body if rest is
  // a tautology — but in practice extractLeftmost leaves at least one other
  // conjunct). Walk recursively so nested checks compose.
  const innerThen: TStmt[] = [{ kind: "if", cond: restCond, then: s.then, else: s.else }];
  return {
    kind: "tagMatch",
    scrutinee: check.scrutinee,
    typeName: check.typeName,
    cases: [{ variant: check.variant, body: innerThen.map(walkStmt) }],
    fallthrough: s.else,
  };
}

/** Rule (expression): `(<rest> && Array.isArray(path)) ? a : b`
 *  → `tagMatch path { ArrayBranch => (<rest>) ? a : b } fallthrough b`.
 *  Mirrors `ruleConditionalAndOptional`. */
function ruleConditionalAndArrayIsArray(e: TExpr): TExpr | null {
  if (e.kind !== "conditional") return null;
  const extracted = extractLeftmostArrayIsArrayCheck(e.cond);
  if (!extracted) return null;
  const { check, restCond } = extracted;
  const innerCond: TExpr = {
    kind: "conditional",
    cond: restCond, then: e.then, else: e.else, ty: e.ty,
  };
  return {
    kind: "tagMatch",
    scrutinee: check.scrutinee,
    typeName: check.typeName,
    cases: [{ variant: check.variant, body: walkExpr(innerCond) }],
    fallthrough: e.else,
    ty: e.ty,
  };
}

// ── Function / module entry ──────────────────────────────────

function narrowFunction(fn: TFunction): TFunction {
  return {
    ...fn,
    requires: fn.requires.map(e => walkExpr(e)),
    ensures: fn.ensures.map(e => walkExpr(e)),
    decreases: fn.decreases ? walkExpr(fn.decreases) : null,
    body: walkStmts(fn.body),
  };
}

export function narrowModule(mod: TModule): TModule {
  _ocCounter = 0;
  _typeDecls = mod.typeDecls;
  return {
    ...mod,
    constants: mod.constants.map(c => ({ ...c, value: walkExpr(c.value) })),
    functions: mod.functions.map(narrowFunction),
    classes: mod.classes.map(cls => ({
      ...cls,
      methods: cls.methods.map(narrowFunction),
    })),
  };
}
