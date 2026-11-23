/**
 * narrow — In-bounds array-index guard pass (`arr[i] ?? d`, `arr[i]?.f`, `const x = arr[i]`).
 *
 * All type-narrowing (optional/nullish, discriminated unions, and `Array.isArray` /
 * `typeof` synth array-unions) is handled directly via checked local coercions and
 * `ofVariant` annotations emitted during resolution and lowered locally in `transform.ts`.
 */

import type { TModule, TFunction, TStmt, TExpr } from "./typedir.js";
import { UNDEFINED } from "./nullish.js";
import { applyChain, arrayBoundsCond } from "./condition-facts.js";

// ── Walkers ──────────────────────────────────────────────────

function walkExpr(e: TExpr): TExpr {
  const r = recurseExpr(e);
  return ruleNullishIndex(r) ?? ruleOptChainIndex(r) ?? r;
}

function recurseExpr(e: TExpr): TExpr {
  switch (e.kind) {
    case "var": case "num": case "bigint": case "str": case "bool":
    case "havoc":
      return e;
    case "binop": return { ...e, left: walkExpr(e.left), right: walkExpr(e.right) };
    case "unop": case "coerce": return { ...e, expr: walkExpr(e.expr) };
    case "call": return { ...e, fn: walkExpr(e.fn), args: e.args.map(walkExpr) };
    case "index": return { ...e, obj: walkExpr(e.obj), idx: walkExpr(e.idx) };
    case "field": return { ...e, obj: walkExpr(e.obj) };
    case "record": return { ...e, spread: e.spread ? walkExpr(e.spread) : null,
      fields: e.fields.map(f => ({ ...f, value: walkExpr(f.value) })) };
    case "arrayLiteral": return { ...e, elems: e.elems.map(walkExpr) };
    case "lambda": return { ...e, body: walkStmts(e.body) };
    case "conditional": return { ...e, cond: walkExpr(e.cond), then: walkExpr(e.then), else: walkExpr(e.else) };
    case "optChain": return { ...e, obj: walkExpr(e.obj),
      chain: e.chain.map(s => s.kind === "call" ? { ...s, args: s.args.map(walkExpr) }
        : s.kind === "index" ? { ...s, idx: walkExpr(s.idx) }
        : s) };
    case "nullish": return { ...e, left: walkExpr(e.left), right: walkExpr(e.right) };
    case "forall": return { ...e, body: walkExpr(e.body) };
    case "exists": return { ...e, body: walkExpr(e.body) };
  }
}

function walkStmt(s: TStmt): TStmt {
  return ruleOptionalIndexBinding(recurseStmt(s)) ?? recurseStmt(s);
}

function walkStmts(stmts: TStmt[]): TStmt[] {
  return stmts.map(walkStmt);
}

function recurseStmt(s: TStmt): TStmt {
  switch (s.kind) {
    case "let": return { ...s, init: walkExpr(s.init) };
    case "assign": return { ...s, value: walkExpr(s.value) };
    case "return": return { ...s, value: walkExpr(s.value) };
    case "break": case "continue": case "throw": return s;
    case "expr": return { ...s, expr: walkExpr(s.expr) };
    case "if": return { ...s, cond: walkExpr(s.cond), then: walkStmts(s.then), else: walkStmts(s.else) };
    case "while": return { ...s, cond: walkExpr(s.cond),
      invariants: s.invariants.map(walkExpr),
      decreases: s.decreases ? walkExpr(s.decreases) : null,
      doneWith: s.doneWith ? walkExpr(s.doneWith) : null,
      body: walkStmts(s.body) };
    case "switch": return { ...s, expr: walkExpr(s.expr),
      cases: s.cases.map(c => ({ ...c, body: walkStmts(c.body) })),
      defaultBody: walkStmts(s.defaultBody) };
    case "forof": return { ...s, iterable: walkExpr(s.iterable),
      invariants: s.invariants.map(walkExpr),
      doneWith: s.doneWith ? walkExpr(s.doneWith) : null,
      body: walkStmts(s.body) };
    case "ghostLet": return { ...s, init: walkExpr(s.init) };
    case "ghostAssign": return { ...s, value: walkExpr(s.value) };
    case "assert": return { ...s, expr: walkExpr(s.expr) };
  }
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

// ── Function / module entry ──────────────────────────────────

function narrowFunction(fn: TFunction): TFunction {
  return {
    ...fn,
    requires: fn.requires.map(walkExpr),
    ensures: fn.ensures.map(walkExpr),
    decreases: fn.decreases ? walkExpr(fn.decreases) : null,
    body: walkStmts(fn.body),
  };
}

export function narrowModule(mod: TModule): TModule {
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
