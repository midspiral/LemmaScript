/**
 * narrow — Array-index bounds guards and discriminated-union `tagMatch` pass.
 *
 * Optional and nullish narrowing no longer rewrite control flow or introduce
 * `someMatch` binders; they are handled directly via checked `coerce` nodes
 * emitted during resolution and lowered locally in `transform.ts`.
 */

import type { TModule, TFunction, TStmt, TExpr } from "./typedir.js";
import { isTerminatorKind } from "./typedir.js";
import { UNDEFINED } from "./nullish.js";
import {
  type CondCtx,
  leadingIsArray, applyChain, arrayBoundsCond,
  isArrayFact, typeofStringFact, variantFact, negVariantFact,
} from "./condition-facts.js";

// ── Walkers ──────────────────────────────────────────────────

function walkExpr(e: TExpr, ctx: CondCtx): TExpr {
  const r = recurseExpr(e, ctx);
  return ruleNullishIndex(r)
    ?? ruleOptChainIndex(r)
    ?? ruleImplArrayIsArray(r, ctx)
    ?? ruleConditionalArrayIsArray(r, ctx)
    ?? ruleConditionalAndArrayIsArray(r, ctx)
    ?? r;
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
    case "tagMatch": return { ...e, scrutinee: re(e.scrutinee),
      cases: e.cases.map(c => ({ ...c, body: re(c.body) })),
      fallthrough: e.fallthrough ? re(e.fallthrough) : null };
  }
}

function walkStmt(s: TStmt, ctx: CondCtx): TStmt {
  const r = recurseStmt(s, ctx);
  return ruleIfAndArrayIsArray(r, ctx) ?? ruleOptionalIndexBinding(r) ?? r;
}

function walkStmts(stmts: TStmt[], ctx: CondCtx): TStmt[] {
  const result: TStmt[] = [];
  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i];
    const tagged = ruleDiscriminantChain(stmts.slice(i), ctx) ?? ruleDiscriminantNegEarlyReturn(stmts.slice(i), ctx);
    if (tagged) {
      result.push(walkStmt(tagged.stmt, ctx));
      i += tagged.consumed - 1;
      continue;
    }
    result.push(walkStmt(s, ctx));
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

// ── In-bounds array index rules ─────────────────────────────

function ruleNullishIndex(e: TExpr): TExpr | null {
  if (e.kind !== "nullish") return null;
  if (e.left.kind !== "index") return null;
  if (e.left.obj.ty.kind !== "array") return null;
  if (e.left.ty.kind === "optional") return null;
  const cond = arrayBoundsCond(e.left.obj, e.left.idx);
  return { kind: "conditional", cond, then: e.left, else: e.right, ty: e.ty };
}

function ruleOptChainIndex(e: TExpr): TExpr | null {
  if (e.kind !== "optChain") return null;
  if (e.obj.kind !== "index") return null;
  if (e.obj.obj.ty.kind !== "array") return null;
  if (e.obj.ty.kind === "optional") return null;
  const cond = arrayBoundsCond(e.obj.obj, e.obj.idx);
  const body = applyChain(e.obj, e.chain);
  const undef: TExpr = { kind: "var", name: "undefined", ty: UNDEFINED };
  return { kind: "conditional", cond, then: body, else: undef, ty: e.ty };
}

function ruleOptionalIndexBinding(s: TStmt): TStmt | null {
  if (s.kind !== "let") return null;
  if (s.ty.kind !== "optional") return null;
  const init = s.init.kind === "coerce" && s.init.expr.kind === "index" ? s.init.expr : s.init;
  if (init.kind !== "index") return null;
  if (init.obj.ty.kind !== "array") return null;
  if (init.ty.kind === "optional") return null;
  const cond = arrayBoundsCond(init.obj, init.idx);
  const undef: TExpr = { kind: "var", name: "undefined", ty: UNDEFINED };
  const guarded: TExpr = { kind: "conditional", cond, then: init, else: undef, ty: s.ty };
  return { ...s, init: guarded };
}

// ── Variant drivers (discriminants and synth array-unions) ──

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

function ruleConditionalArrayIsArray(e: TExpr, ctx: CondCtx): TExpr | null {
  if (e.kind !== "conditional") return null;
  const pos = isArrayFact(e.cond, ctx);
  const tof = pos ? null : typeofStringFact(e.cond, ctx);
  const neg = !pos && !tof && e.cond.kind === "unop" && e.cond.op === "!"
    ? isArrayFact(e.cond.expr, ctx)
    : null;
  const matched = pos ?? tof ?? (neg ? { scrutinee: neg.scrutinee, typeName: neg.typeName, variant: "NonArrayBranch" as const } : null);
  if (!matched) return null;
  return {
    kind: "tagMatch",
    scrutinee: matched.scrutinee,
    typeName: matched.typeName,
    cases: [{ variant: matched.variant, body: walkExpr(e.then, ctx) }],
    fallthrough: walkExpr(e.else, ctx),
    ty: e.ty,
  };
}

function ruleIfAndArrayIsArray(s: TStmt, ctx: CondCtx): TStmt | null {
  if (s.kind !== "if") return null;
  const extracted = leadingIsArray(s.cond, ctx);
  if (!extracted) return null;
  const { check, restCond } = extracted;
  const innerThen: TStmt[] = [{ kind: "if", cond: restCond, then: s.then, else: s.else }];
  return {
    kind: "tagMatch",
    scrutinee: check.scrutinee,
    typeName: check.typeName,
    cases: [{ variant: check.variant, body: innerThen.map(x => walkStmt(x, ctx)) }],
    fallthrough: s.else,
  };
}

function ruleConditionalAndArrayIsArray(e: TExpr, ctx: CondCtx): TExpr | null {
  if (e.kind !== "conditional") return null;
  const extracted = leadingIsArray(e.cond, ctx);
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
    cases: [{ variant: check.variant, body: walkExpr(innerCond, ctx) }],
    fallthrough: e.else,
    ty: e.ty,
  };
}

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
  if (cases.every(c => isTerminating(c.body))) {
    return { stmt: { kind: "tagMatch", scrutinee: first.scrutinee, typeName: first.typeName,
      cases, fallthrough: stmts.slice(consumed) }, consumed: stmts.length };
  }
  return { stmt: { kind: "tagMatch", scrutinee: first.scrutinee, typeName: first.typeName,
    cases, fallthrough: [] }, consumed };
}

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
  const ctx: CondCtx = { decls: mod.typeDecls };
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
