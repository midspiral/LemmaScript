/**
 * pe — Partial-evaluation pass for narrowing emulation.
 *
 * Pipeline: resolve → pe → transform → emit.
 *
 * Operates on the typed IR (TExpr/TStmt) with an environment threaded
 * through the walk. Currently a no-op identity rewrite — the walker shape
 * is in place so future rules slot in without restructuring.
 *
 * The intent is to consolidate narrowing emulation here. Each pattern
 * (`if (x !== undefined) ...`, `x ? a : b`, `&&`, `||`, early return) gets
 * a rule in pe; the corresponding handling in resolve and transform gets
 * removed in lockstep.
 */

import type { TModule, TFunction, TStmt, TExpr, Ty } from "./typedir.js";

// ── Environment ──────────────────────────────────────────────
//
// Will eventually carry:
//   - bindings  (var → translated value, for inlined consts)
//   - narrowing facts (var → known-Some / known-None)
// For now it's a placeholder so the walker has the shape.

interface Env { /* empty for now */ }

const emptyEnv: Env = {};

// ── Optional-check detection ────────────────────────────────

/** Detect `v !== undefined` or `undefined !== v` where v is a simple variable
 *  of optional type. Returns the var name + inner type if so. */
function parseSimpleOptionalCheck(cond: TExpr): { varName: string; innerTy: Ty; negated: boolean } | null {
  if (cond.kind !== "binop" || (cond.op !== "!==" && cond.op !== "===")) return null;
  let vExpr: TExpr | null = null;
  if (cond.right.kind === "var" && cond.right.name === "undefined") vExpr = cond.left;
  if (cond.left.kind === "var" && cond.left.name === "undefined") vExpr = cond.right;
  if (!vExpr || vExpr.kind !== "var" || vExpr.ty.kind !== "optional") return null;
  return { varName: vExpr.name, innerTy: vExpr.ty.inner, negated: cond.op === "===" };
}

// ── Walkers ──────────────────────────────────────────────────

function walkExpr(e: TExpr, _env: Env): TExpr {
  // No-op for now.
  return e;
}

function walkStmt(s: TStmt, env: Env): TStmt {
  // Recurse into children first, then try rules at this node.
  const r = recurseStmt(s, env);
  return ruleIfOptionalSimple(r) ?? r;
}

function walkStmts(stmts: TStmt[], env: Env): TStmt[] {
  return stmts.map(s => walkStmt(s, env));
}

function recurseStmt(s: TStmt, env: Env): TStmt {
  const re = (e: TExpr) => walkExpr(e, env);
  const rs = (xs: TStmt[]) => walkStmts(xs, env);
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
  }
}

// ── Rules ───────────────────────────────────────────────────

/** Rule: `if (x !== undefined) then else` where x is a simple optional var
 *  → `someMatch x { Some(_x_val) => then, None => else }`.
 *  Only fires when the Some branch is non-empty. Early-return shapes like
 *  `if (x === undefined) return; rest` have an empty Some branch and are
 *  left for transform's `prepareOptionalMatch` (which consumes `rest`). */
function ruleIfOptionalSimple(s: TStmt): TStmt | null {
  if (s.kind !== "if") return null;
  const check = parseSimpleOptionalCheck(s.cond);
  if (!check) return null;
  const someBody = check.negated ? s.else : s.then;
  const noneBody = check.negated ? s.then : s.else;
  if (someBody.length === 0) return null;
  return {
    kind: "someMatch",
    varName: check.varName, varTy: check.innerTy,
    binder: `_${check.varName}_val`,
    someBody, noneBody,
  };
}

// ── Function / module entry ──────────────────────────────────

function peFunction(fn: TFunction): TFunction {
  return {
    ...fn,
    requires: fn.requires.map(e => walkExpr(e, emptyEnv)),
    ensures: fn.ensures.map(e => walkExpr(e, emptyEnv)),
    decreases: fn.decreases ? walkExpr(fn.decreases, emptyEnv) : null,
    body: walkStmts(fn.body, emptyEnv),
  };
}

export function peModule(mod: TModule): TModule {
  return {
    ...mod,
    constants: mod.constants.map(c => ({ ...c, value: walkExpr(c.value, emptyEnv) })),
    functions: mod.functions.map(peFunction),
    classes: mod.classes.map(cls => ({
      ...cls,
      methods: cls.methods.map(peFunction),
    })),
  };
}
