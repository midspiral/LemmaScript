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

// ── Optional-check detection ────────────────────────────────

/** Counter for naming optChain binders. Reset per module. */
let _ocCounter = 0;

/** Detect optional checks: `e !== undefined`, `e === undefined`, or `!e` for a
 *  pure-access-path optional-typed e. `!e` is equivalent to `=== undefined`.
 *  Following TS, only pure access paths narrow; complex scrutinees return null. */
function parseOptionalCheck(cond: TExpr): { scrutinee: TExpr; innerTy: Ty; negated: boolean; binderHint: string } | null {
  // `!e` where e is optional — same as `e === undefined` (negated: true).
  if (cond.kind === "unop" && cond.op === "!" && cond.expr.ty.kind === "optional") {
    const e = cond.expr;
    const innerTy = cond.expr.ty.inner;
    const hint = binderHintFor(e);
    if (hint === null) return null;
    return { scrutinee: e, innerTy, negated: true, binderHint: hint };
  }
  if (cond.kind !== "binop" || (cond.op !== "!==" && cond.op !== "===")) return null;
  let e: TExpr | null = null;
  if (cond.right.kind === "var" && cond.right.name === "undefined") e = cond.left;
  if (cond.left.kind === "var" && cond.left.name === "undefined") e = cond.right;
  if (!e || e.ty.kind !== "optional") return null;
  const hint = binderHintFor(e);
  if (hint === null) return null;
  return { scrutinee: e, innerTy: e.ty.inner, negated: cond.op === "===", binderHint: hint };
}

function binderHintFor(e: TExpr): string | null {
  // Pure access paths: var(x) or field(purePath, name).
  // Walks down to the var root, collecting field names. Returns
  // `_root_field1_field2_..._val` (or `_root_val` for a bare var).
  const fields: string[] = [];
  let cur = e;
  while (cur.kind === "field") { fields.unshift(cur.field); cur = cur.obj; }
  if (cur.kind !== "var") return null;
  return fields.length === 0 ? `_${cur.name}_val` : `_${cur.name}_${fields.join("_")}_val`;
}

// Aliased for code that historically called the simpler check.
const parseSimpleOptionalCheck = parseOptionalCheck;

// ── Walkers ──────────────────────────────────────────────────

function walkExpr(e: TExpr): TExpr {
  const r = recurseExpr(e);
  return ruleNullish(r) ?? ruleOptChain(r) ?? ruleImplOptional(r) ?? ruleConditionalAndOptional(r) ?? ruleConditionalOptionalSimple(r) ?? ruleConditionalOptionalTruthy(r) ?? r;
}

function recurseExpr(e: TExpr): TExpr {
  const re = walkExpr;
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
  }
}

function walkStmt(s: TStmt): TStmt {
  // Recurse into children first, then try rules at this node.
  const r = recurseStmt(s);
  // && rule fires before simple rule because it produces nested ifs whose
  // inner shape doesn't match simple rule directly. someMatch result needs
  // no further rewriting at this level.
  return ruleIfAndOptional(r) ?? ruleIfOptionalSimple(r) ?? r;
}

function walkStmts(stmts: TStmt[]): TStmt[] {
  const result: TStmt[] = [];
  for (let i = 0; i < stmts.length; i++) {
    const s = stmts[i];
    const rest = stmts.slice(i + 1);
    const consumed = ruleEarlyReturnOrChain(s, rest) ?? ruleEarlyReturnConsume(s, rest);
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
    someBody, noneBody,
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

/** Rule (expression): `left ?? right` — nullish coalescing.
 *  → `someMatch left { Some(_v) => _v, None => right }`.
 *  Single-evaluation: scrutinee may be any expression. */
function ruleNullish(e: TExpr): TExpr | null {
  if (e.kind !== "nullish") return null;
  if (e.left.ty.kind !== "optional") return null;
  const innerTy = e.left.ty.inner;
  const binder = `_oc${_ocCounter++}_val`;
  return {
    kind: "someMatch",
    scrutinee: e.left, binder, binderTy: innerTy,
    someBody: { kind: "var", name: binder, ty: innerTy },
    noneBody: e.right,
    ty: e.ty,
  };
}

/** Rule (expression): `obj?.<chain>` — single-eval optional chain.
 *  → `someMatch obj { Some(_oc{N}_val) => apply(chain, _oc{N}_val), None => undefined }`.
 *  The someBody applies the chain to the binder directly (field/call/index),
 *  so transform doesn't substitute. Scrutinee can be any expression. */
function ruleOptChain(e: TExpr): TExpr | null {
  if (e.kind !== "optChain") return null;
  if (e.obj.ty.kind !== "optional") return null;
  const innerTy = e.obj.ty.inner;
  const binder = `_oc${_ocCounter++}_val`;
  let body: TExpr = { kind: "var", name: binder, ty: innerTy };
  for (const step of e.chain) {
    if (step.kind === "field") {
      body = { kind: "field", obj: body, field: step.name, ty: step.ty };
    } else if (step.kind === "index") {
      body = { kind: "index", obj: body, idx: step.idx, ty: step.ty };
    } else {
      body = { kind: "call", fn: body, args: step.args, ty: step.ty, callKind: step.callKind };
    }
  }
  const noneBody: TExpr = { kind: "var", name: "undefined", ty: { kind: "void" } };
  return {
    kind: "someMatch",
    scrutinee: e.obj, binder, binderTy: innerTy,
    someBody: body, noneBody, ty: e.ty,
  };
}

/** Rule (expression): `opt ? a : b` (truthiness — cond itself is optional).
 *  Only fires for simple var or simple `obj.field` cond. */
function ruleConditionalOptionalTruthy(e: TExpr): TExpr | null {
  if (e.kind !== "conditional") return null;
  if (e.cond.ty.kind !== "optional") return null;
  const binder = binderHintFor(e.cond);
  if (binder === null) return null;
  return {
    kind: "someMatch",
    scrutinee: e.cond, binderTy: e.cond.ty.inner,
    binder,
    someBody: e.then, noneBody: e.else, ty: e.ty,
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
  return {
    kind: "someMatch",
    scrutinee: check.scrutinee, binderTy: check.innerTy,
    binder: check.binderHint,
    someBody: [walkStmt(innerIf)],
    noneBody: [],
  };
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
  const sm: TStmt = {
    kind: "someMatch",
    scrutinee: check.scrutinee, binderTy: check.innerTy,
    binder: check.binderHint,
    someBody: [{ kind: "if", cond: restCond,
      then: [{ kind: "assign", target: s.name, value: s.init.then }], else: [] }],
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
    case "result": case "havoc":
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
  }
}

/** Rule (expression): `x !== undefined && rest ? a : b`.
 *  → `someMatch x { Some(_x_val) => if rest then a else b, None => b }`.
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
  return {
    kind: "someMatch",
    scrutinee: check.scrutinee, binderTy: check.innerTy,
    binder: check.binderHint,
    someBody: innerCond, noneBody: e.else, ty: e.ty,
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
