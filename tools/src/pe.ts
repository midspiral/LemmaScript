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

/** Detect `e !== undefined` or `undefined !== e` where e is either:
 *  - a simple variable of optional type, or
 *  - a simple `obj.field` chain where obj is a var and the field has optional type.
 *  Returns the scrutinee expression + unwrapped inner type. */
function parseSimpleOptionalCheck(cond: TExpr): { scrutinee: TExpr; innerTy: Ty; negated: boolean; binderHint: string } | null {
  if (cond.kind !== "binop" || (cond.op !== "!==" && cond.op !== "===")) return null;
  let e: TExpr | null = null;
  if (cond.right.kind === "var" && cond.right.name === "undefined") e = cond.left;
  if (cond.left.kind === "var" && cond.left.name === "undefined") e = cond.right;
  if (!e || e.ty.kind !== "optional") return null;
  if (e.kind === "var") {
    return { scrutinee: e, innerTy: e.ty.inner, negated: cond.op === "===", binderHint: `_${e.name}_val` };
  }
  if (e.kind === "field" && e.obj.kind === "var") {
    return { scrutinee: e, innerTy: e.ty.inner, negated: cond.op === "===", binderHint: `_${e.obj.name}_${e.field}_val` };
  }
  return null;
}

// ── Walkers ──────────────────────────────────────────────────

function walkExpr(e: TExpr, env: Env): TExpr {
  // Recurse into children first, then try rules at this node.
  const r = recurseExpr(e, env);
  return ruleConditionalOptionalSimple(r) ?? r;
}

function recurseExpr(e: TExpr, env: Env): TExpr {
  const re = (x: TExpr) => walkExpr(x, env);
  switch (e.kind) {
    case "var": case "num": case "str": case "bool":
    case "result": case "havoc":
      return e;
    case "binop": return { ...e, left: re(e.left), right: re(e.right) };
    case "unop": return { ...e, expr: re(e.expr) };
    case "call": return { ...e, fn: re(e.fn), args: e.args.map(re) };
    case "index": return { ...e, obj: re(e.obj), idx: re(e.idx) };
    case "field": return { ...e, obj: re(e.obj) };
    case "record": return { ...e, spread: e.spread ? re(e.spread) : null,
      fields: e.fields.map(f => ({ ...f, value: re(f.value) })) };
    case "arrayLiteral": return { ...e, elems: e.elems.map(re) };
    case "lambda": return { ...e, body: walkStmts(e.body, env) };
    case "conditional": return { ...e, cond: re(e.cond), then: re(e.then), else: re(e.else) };
    case "forall": return { ...e, body: re(e.body) };
    case "exists": return { ...e, body: re(e.body) };
    case "someMatch": return { ...e, someBody: re(e.someBody), noneBody: re(e.noneBody) };
  }
}

function walkStmt(s: TStmt, env: Env): TStmt {
  // Recurse into children first, then try rules at this node.
  const r = recurseStmt(s, env);
  // && rule fires before simple rule because it produces nested ifs whose
  // inner shape doesn't match simple rule directly. someMatch result needs
  // no further rewriting at this level.
  return ruleIfAndOptional(r) ?? ruleIfOptionalSimple(r) ?? r;
}

function walkStmts(stmts: TStmt[], env: Env): TStmt[] {
  const result: TStmt[] = [];
  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i];
    const rest = stmts.slice(i + 1);
    // List-level rules consume the rest of the block, so try them before per-stmt walk.
    const consumed = ruleEarlyReturnOrChain(s, rest) ?? ruleEarlyReturnConsume(s, rest);
    if (consumed) {
      result.push(walkStmt(consumed, env));
      return result;  // rest is now inside someBody
    }
    result.push(walkStmt(s, env));
  }
  return result;
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
    someBody, noneBody,
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
  return {
    kind: "someMatch",
    scrutinee: check.scrutinee, binderTy: check.innerTy,
    binder: check.binderHint,
    someBody: rest,
    noneBody: noneBranch,
  };
}

/** Collect a `||` chain of negative optional checks (`x === undefined`).
 *  Returns the list of checks if every leaf is a negative optional check; null otherwise. */
function collectOrChainOfNegativeChecks(cond: TExpr): ReturnType<typeof parseSimpleOptionalCheck>[] | null {
  if (cond.kind === "binop" && cond.op === "||") {
    const left = collectOrChainOfNegativeChecks(cond.left);
    const right = collectOrChainOfNegativeChecks(cond.right);
    if (!left || !right) return null;
    return [...left, ...right];
  }
  const check = parseSimpleOptionalCheck(cond);
  if (!check || !check.negated) return null;
  return [check];
}

/** Rule: `if (x === undefined || y === undefined || ...) terminate; rest`.
 *  → nested someMatches narrowing each var in turn, each None branch = terminate,
 *    deepest someBody = rest.
 *  Closes the resolve.ts:602 TODO ("|| narrowing"). */
function ruleEarlyReturnOrChain(s: TStmt, rest: TStmt[]): TStmt | null {
  if (s.kind !== "if") return null;
  if (rest.length === 0) return null;
  if (s.then.length === 0 || s.else.length !== 0) return null;
  if (s.cond.kind !== "binop" || s.cond.op !== "||") return null;  // single check is the simpler rule
  const checks = collectOrChainOfNegativeChecks(s.cond);
  if (!checks || checks.length < 2) return null;
  // Build nested someMatch from innermost outward
  let inner: TStmt[] = rest;
  for (let i = checks.length - 1; i >= 0; i--) {
    const check = checks[i]!;
    inner = [{
      kind: "someMatch",
      scrutinee: check.scrutinee, binderTy: check.innerTy,
      binder: check.binderHint,
      someBody: inner,
      noneBody: s.then,
    }];
  }
  return inner[0];
}

/** Rule (expression): `e !== undefined ? a : b` where e is a simple optional
 *  var or `obj.field` chain.
 *  → `someMatch e { Some(_e_val) => a, None => b }` (TExpr form). */
function ruleConditionalOptionalSimple(e: TExpr): TExpr | null {
  if (e.kind !== "conditional") return null;
  const check = parseSimpleOptionalCheck(e.cond);
  if (!check) return null;
  const someBody = check.negated ? e.else : e.then;
  const noneBody = check.negated ? e.then : e.else;
  return {
    kind: "someMatch",
    scrutinee: check.scrutinee, binderTy: check.innerTy,
    binder: check.binderHint,
    someBody, noneBody,
    ty: e.ty,
  };
}

/** Extract the leftmost optional check from an `&&` chain.
 *  `(x !== undefined && b) && c` → { check, restCond: b && c }. */
function extractLeftmostOptionalCheck(cond: TExpr): {
  check: NonNullable<ReturnType<typeof parseSimpleOptionalCheck>>;
  restCond: TExpr;
} | null {
  if (cond.kind !== "binop" || cond.op !== "&&") return null;
  const check = parseSimpleOptionalCheck(cond.left);
  if (check && !check.negated) return { check, restCond: cond.right };
  if (cond.left.kind === "binop" && cond.left.op === "&&") {
    const inner = extractLeftmostOptionalCheck(cond.left);
    if (inner) return { check: inner.check, restCond: { ...cond, left: inner.restCond } as TExpr };
  }
  return null;
}

/** Rule: `if (x !== undefined && rest) then` (no else) where x is a simple
 *  optional var or `obj.field` chain.
 *  → `someMatch x { Some(_x_val) => if rest then then; , None => {} }`.
 *  The substitution of x→_x_val happens during transform via the someMatch
 *  handler, so the inner `if rest then` automatically gets x narrowed. */
function ruleIfAndOptional(s: TStmt): TStmt | null {
  if (s.kind !== "if") return null;
  if (s.else.length !== 0) return null;
  const extracted = extractLeftmostOptionalCheck(s.cond);
  if (!extracted) return null;
  const { check, restCond } = extracted;
  const innerIf: TStmt = { kind: "if", cond: restCond, then: s.then, else: [] };
  return {
    kind: "someMatch",
    scrutinee: check.scrutinee, binderTy: check.innerTy,
    binder: check.binderHint,
    someBody: [innerIf],
    noneBody: [],
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
