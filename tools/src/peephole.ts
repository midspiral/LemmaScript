/**
 * Peephole — local IR-to-IR rewrites that eliminate wrap-then-unwrap ceremony.
 *
 * Opt-in via `//@ peephole` directive in the source file.
 * Runs between transform and emit. Operates on backend-neutral IR.
 *
 * Rules (applied bottom-up to fixed point at each node):
 *   1. match m.get(k) { Some(v) => sb, None => nb }  →  if k in m then sb[v := m[k]] else nb
 *   2. if c then b else false  →  c && b
 *   3. if c then true else b   →  c || b
 *   4. if c then false else true  →  ¬c
 *   5. if c then true else false  →  c
 *
 * Statement-level rule 1 also handles match-statement on m.get.
 */
import type { Expr, Stmt, Decl, Module, MatchArm, StmtMatchArm, MatchPattern } from "./ir.js";
import { patternCtor, patternBinders, usesName, usesNameInStmts } from "./ir.js";

// (Note: peephole rules now bind once via let/var rather than substitute,
//  so semantics are preserved under any mutation. No substVar helpers needed.
//  Reference checks are ir.ts's usesName/usesNameInStmts — conservative in the
//  right direction for the drop-the-binding gates: also counting app/ctor name
//  references and lambda bodies can only suppress a rewrite, never misapply one.)

// ── Shape detection ──────────────────────────────────────────

type MethodCall = Extract<Expr, { kind: "methodCall" }>;

/** Detect map.get(k) — returns { obj, key, objTy } if so, else null. */
function isMapGet(e: Expr): { obj: Expr; key: Expr; objTy: MethodCall["objTy"] } | null {
  if (e.kind !== "methodCall" || e.objTy.kind !== "map" || e.method !== "get" || e.args.length !== 1) return null;
  return { obj: e.obj, key: e.args[0], objTy: e.objTy };
}

/** Binder of a Some arm — its name, or null for `.some _` / a non-`some` pattern. */
function parseSomeBinder(p: MatchPattern): string | null {
  if (patternCtor(p) !== "some") return null;
  const b = patternBinders(p)[0];
  return b === undefined || b === "_" ? null : b;
}

/** Identify a Some/None match's arms. */
function getSomeNoneArms<A extends { pattern: MatchPattern; body: any }>(arms: A[]): { someArm: A; noneArm: A; binder: string | null } | null {
  if (arms.length !== 2) return null;
  const someArm = arms.find(a => patternCtor(a.pattern) === "some");
  const noneArm = arms.find(a => patternCtor(a.pattern) === "none");
  if (!someArm || !noneArm) return null;
  return { someArm, noneArm, binder: parseSomeBinder(someArm.pattern) };
}

// ── Expression rewrite rules ────────────────────────────────

/** Rule 1 (expr): match m.get(k) { Some(v) => sb, None => nb }
 *  → if k in m then (let v = m[k] in sb) else nb
 *  Bind once (let-expression) rather than substitute, so the verifier doesn't
 *  re-derive `k in m` at every use of v inside sb. */
function ruleMatchOnMapGetExpr(e: Expr): Expr | null {
  if (e.kind !== "match") return null;
  const get = isMapGet(e.scrutinee);
  if (!get) return null;
  const arms = getSomeNoneArms(e.arms);
  if (!arms) return null;
  const idx: Expr = { kind: "index", arr: get.obj, idx: get.key };
  const someBody: Expr = arms.binder
    ? { kind: "let", name: arms.binder, value: idx, body: arms.someArm.body }
    : arms.someArm.body;
  const has: Expr = { kind: "methodCall", obj: get.obj, objTy: get.objTy, method: "has", args: [get.key], monadic: false };
  return { kind: "if", cond: has, then: someBody, else: arms.noneArm.body };
}

/** Rule 4: if c then false else true → ¬c (try before rules 2/3 to catch this specific shape) */
function ruleIfFalseElseTrue(e: Expr): Expr | null {
  if (e.kind !== "if") return null;
  if (isBool(e.then, false) && isBool(e.else, true)) return { kind: "unop", op: "¬", expr: e.cond };
  return null;
}

/** Rule 5: if c then true else false → c */
function ruleIfIdentity(e: Expr): Expr | null {
  if (e.kind !== "if") return null;
  if (isBool(e.then, true) && isBool(e.else, false)) return e.cond;
  return null;
}

/** Rule 2: if c then b else false → c && b */
function ruleIfThenFalse(e: Expr): Expr | null {
  if (e.kind !== "if") return null;
  if (isBool(e.else, false)) return { kind: "binop", op: "∧", left: e.cond, right: e.then };
  return null;
}

/** Rule 3: if c then true else b → c || b */
function ruleIfTrueElse(e: Expr): Expr | null {
  if (e.kind !== "if") return null;
  if (isBool(e.then, true)) return { kind: "binop", op: "∨", left: e.cond, right: e.else };
  return null;
}

/** Rule 6 (let-expr collapse): let x = m.get(k) in match x { Some(v) => sb, None => nb }
 *  → if k in m then (let v = m[k] in sb) else nb
 *  Body must reference x only as the match scrutinee. Bind v once via let-expression
 *  rather than substitute, so semantics are preserved under any mutation. */
function ruleLetMatchOnMapGetExpr(e: Expr): Expr | null {
  if (e.kind !== "let") return null;
  const get = isMapGet(e.value);
  if (!get) return null;
  if (e.body.kind !== "match") return null;
  const m = e.body;
  const matchOnX =
    m.scrutinee.kind === "var" && m.scrutinee.name === e.name;
  if (!matchOnX) return null;
  const arms = getSomeNoneArms(m.arms);
  if (!arms) return null;
  // x must not appear in arm bodies (otherwise the binding is needed)
  if (usesName(arms.someArm.body, e.name) || usesName(arms.noneArm.body, e.name)) return null;
  const idx: Expr = { kind: "index", arr: get.obj, idx: get.key };
  const someBody: Expr = arms.binder
    ? { kind: "let", name: arms.binder, value: idx, body: arms.someArm.body }
    : arms.someArm.body;
  const has: Expr = { kind: "methodCall", obj: get.obj, objTy: get.objTy, method: "has", args: [get.key], monadic: false };
  return { kind: "if", cond: has, then: someBody, else: arms.noneArm.body };
}

function isBool(e: Expr, v: boolean): boolean {
  return e.kind === "bool" && e.value === v;
}

// Boolean-simplification rules (rules 2-5) collapse `if c then b else false` into
// `c && b` etc.  These are sound in Dafny because `&&`/`||` are short-circuit, but
// in Lean they produce `∧`/`∨` (Prop ops) which evaluate both arguments — breaking
// structural-termination checks for recursive functions like:
//   `if n = 0 then true else ... allExpensesValid expenses (n - 1) ...`
// where the recursive call needs the if-condition to bound `n > 0`.
// So they're applied only for Dafny.
type Backend = "lean" | "dafny";

/** Direct rule chain (R1): first hit wins, in the old EXPR_RULES order —
 *  map-get rules, then (Dafny only, see comment above) the boolean
 *  simplifications. A chain of direct calls over a threaded backend flag
 *  rather than a rule table: the subset has no function-valued collections
 *  (`rules[i](e)` is out of fragment) and loops lower to methods, so this
 *  shape is what remains. */
function applyExprRules(e: Expr, backend: Backend): Expr | null {
  const r1 = ruleMatchOnMapGetExpr(e);
  if (r1 !== null) return r1;
  const r6 = ruleLetMatchOnMapGetExpr(e);
  if (r6 !== null) return r6;
  if (backend !== "dafny") return null;
  const r4 = ruleIfFalseElseTrue(e);
  if (r4 !== null) return r4;
  const r5 = ruleIfIdentity(e);
  if (r5 !== null) return r5;
  const r2 = ruleIfThenFalse(e);
  if (r2 !== null) return r2;
  const r3 = ruleIfTrueElse(e);
  if (r3 !== null) return r3;
  return null;
}

// ── Statement rewrite rules ──────────────────────────────────

/** Stmt rule 1: match m.get(k) { Some(v) => sb, None => nb }
 *  → if k in m { var v := m[k]; sb } else { nb }
 *  Bind once (var declaration) rather than substitute — substituting would
 *  re-evaluate m[k] at every use, changing semantics if the body mutates m. */
function ruleMatchOnMapGetStmt(s: Stmt): Stmt | null {
  if (s.kind !== "match") return null;
  const get = isMapGet(s.scrutinee);
  if (!get) return null;
  const arms = getSomeNoneArms(s.arms);
  if (!arms) return null;
  const idx: Expr = { kind: "index", arr: get.obj, idx: get.key };
  const valTy = get.objTy.kind === "map" ? get.objTy.value : { kind: "unknown" as const };
  const someBody: Stmt[] = arms.binder
    ? [{ kind: "let", name: arms.binder, type: valTy, mutable: false, value: idx }, ...arms.someArm.body]
    : arms.someArm.body;
  const has: Expr = { kind: "methodCall", obj: get.obj, objTy: get.objTy, method: "has", args: [get.key], monadic: false };
  return { kind: "if", cond: has, then: someBody, else: arms.noneArm.body };
}


// ── Statement-list rules (pairs of adjacent stmts) ──────────

/** Pair rule: let x = m.get(k); match x { Some(v) => sb, None => nb }
 *  → if k in m { var v := m[k]; sb } else { nb }
 *  Requires x not referenced in any stmt after the match. Bind v once instead
 *  of substituting, to preserve semantics under mutation of m. */
function tryLetMatchOnMapGet(s1: Stmt, s2: Stmt, restStmts: Stmt[]): Stmt | null {
  if (s1.kind !== "let" || s1.mutable) return null;
  const get = isMapGet(s1.value);
  if (!get) return null;
  if (s2.kind !== "match") return null;
  const matchOnX =
    s2.scrutinee.kind === "var" && s2.scrutinee.name === s1.name;
  if (!matchOnX) return null;
  const arms = getSomeNoneArms(s2.arms);
  if (!arms) return null;
  if (usesNameInStmts(restStmts, s1.name)) return null;
  const idx: Expr = { kind: "index", arr: get.obj, idx: get.key };
  const valTy = get.objTy.kind === "map" ? get.objTy.value : { kind: "unknown" as const };
  const someBody: Stmt[] = arms.binder
    ? [{ kind: "let", name: arms.binder, type: valTy, mutable: false, value: idx }, ...arms.someArm.body]
    : arms.someArm.body;
  const has: Expr = { kind: "methodCall", obj: get.obj, objTy: get.objTy, method: "has", args: [get.key], monadic: false };
  return { kind: "if", cond: has, then: someBody, else: arms.noneArm.body };
}

/** Walk a statement list applying pair rules. */
function rewriteStmtListPairs(stmts: Stmt[], backend: Backend): Stmt[] {
  if (stmts.length === 0) return [];
  if (stmts.length >= 2) {
    const merged = tryLetMatchOnMapGet(stmts[0], stmts[1], stmts.slice(2));
    if (merged) {
      // Recurse into the new stmt's children to peephole them too
      return [peepholeStmt(merged, backend), ...rewriteStmtListPairs(stmts.slice(2), backend)];
    }
  }
  return [stmts[0], ...rewriteStmtListPairs(stmts.slice(1), backend)];
}

/** Peephole a statement list: per-stmt rules first, then pair rules. */
function peepholeStmts(stmts: Stmt[], backend: Backend): Stmt[] {
  return rewriteStmtListPairs(stmts.map(s => peepholeStmt(s, backend)), backend);
}

// ── Bottom-up rewrite to fixed point at each node ───────────

/** Termination (proved Dafny-side, not exposed here): every rule strictly
 *  decreases (match-count, if-count) lexicographically — rules 1/6 trade a
 *  match for an if, rules 2–5 drop an if — so the rule-hit recursion is
 *  finite; child recursion is structural. No fuel needed: a recursive call's
 *  root is already at fixed point when it returns, so one hit-then-recurse
 *  replaces the old retry loop exactly. */
function peepholeExpr(e: Expr, backend: Backend): Expr {
  // Recurse into children first, then apply the first matching rule
  const cur = rewriteChildrenExpr(e, backend);
  const hit = applyExprRules(cur, backend);
  return hit !== null ? peepholeExpr(hit, backend) : cur;
}

function rewriteChildrenExpr(e: Expr, backend: Backend): Expr {
  const r = (x: Expr) => peepholeExpr(x, backend);
  switch (e.kind) {
    case "var": case "num": case "bool": case "str": case "constructor":
    case "emptyMap": case "emptySet": case "havoc": case "default": case "mapLiteral": return e;
    case "binop": return { ...e, left: r(e.left), right: r(e.right) };
    case "unop": return { ...e, expr: r(e.expr) };
    case "implies": return { ...e, premises: e.premises.map(r), conclusion: r(e.conclusion) };
    case "app": return { ...e, args: e.args.map(r) };
    case "field": return { ...e, obj: r(e.obj) };
    case "toNat": return { ...e, expr: r(e.expr) };
    case "toReal": return { ...e, expr: r(e.expr) };
    case "index": return { ...e, arr: r(e.arr), idx: r(e.idx) };
    case "tupleLiteral": return { ...e, elems: e.elems.map(r) };
    case "tupleProj": return { ...e, obj: r(e.obj) };
    case "record": return { ...e, spread: e.spread ? r(e.spread) : null,
      fields: e.fields.map(fi => ({ ...fi, value: r(fi.value) })) };
    case "arrayLiteral": return { ...e, elems: e.elems.map(r) };
    case "if": return { ...e, cond: r(e.cond), then: r(e.then), else: r(e.else) };
    case "match": {
      const scr = r(e.scrutinee);
      return { ...e, scrutinee: scr, arms: e.arms.map(a => ({ ...a, body: r(a.body) })) };
    }
    case "forall": return { ...e, body: r(e.body) };
    case "exists": return { ...e, body: r(e.body) };
    case "let": return { ...e, value: r(e.value), body: r(e.body) };
    case "methodCall": return { ...e, obj: r(e.obj), args: e.args.map(r) };
    case "lambda": return { ...e, body: peepholeStmts(e.body, backend) };
  }
}

function peepholeStmt(s: Stmt, backend: Backend): Stmt {
  const cur = rewriteChildrenStmt(s, backend);
  const r = ruleMatchOnMapGetStmt(cur);
  return r !== null ? peepholeStmt(r, backend) : cur;
}

function rewriteChildrenStmt(s: Stmt, backend: Backend): Stmt {
  const re = (x: Expr) => peepholeExpr(x, backend);
  const rs = (x: Stmt[]) => peepholeStmts(x, backend);
  switch (s.kind) {
    case "let": return { ...s, value: re(s.value) };
    case "assign": return { ...s, value: re(s.value) };
    case "bind": return { ...s, value: re(s.value) };
    case "let-bind": return { ...s, value: re(s.value) };
    case "return": return { ...s, value: re(s.value) };
    case "break": case "continue": return s;
    case "if": return { ...s, cond: re(s.cond), then: rs(s.then), else: rs(s.else) };
    case "match": {
      const scr = re(s.scrutinee);
      return { ...s, scrutinee: scr, arms: s.arms.map(a => ({ ...a, body: rs(a.body) })) };
    }
    case "while": return { ...s, cond: re(s.cond), invariants: s.invariants.map(re), body: rs(s.body) };
    case "forin": return { ...s, bound: re(s.bound), invariants: s.invariants.map(re), body: rs(s.body) };
    case "ghostLet": return { ...s, value: re(s.value) };
    case "ghostAssign": return { ...s, value: re(s.value) };
    case "assert": return { ...s, expr: re(s.expr) };
  }
}

// ── Module entry ────────────────────────────────────────────

export function peepholeModule(mod: Module, backend: Backend = "dafny"): Module {
  return { ...mod, decls: mod.decls.map(d => peepholeDecl(d, backend)) };
}

function peepholeDecl(d: Decl, backend: Backend): Decl {
  const re = (x: Expr) => peepholeExpr(x, backend);
  switch (d.kind) {
    case "def":
      return { ...d, body: re(d.body),
        requires: d.requires.map(re), ensures: d.ensures.map(re),
        decreases: d.decreases ? re(d.decreases) : null };
    case "def-by-method":
      return { ...d, methodBody: peepholeStmts(d.methodBody, backend),
        requires: d.requires.map(re), ensures: d.ensures.map(re),
        decreases: d.decreases ? re(d.decreases) : null };
    case "method":
      return { ...d, body: peepholeStmts(d.body, backend),
        requires: d.requires.map(re), ensures: d.ensures.map(re),
        decreases: d.decreases ? re(d.decreases) : null };
    case "namespace": return { ...d, decls: d.decls.map(x => peepholeDecl(x, backend)) };
    case "class": return { ...d, methods: d.methods.map(m => peepholeDecl(m, backend) as typeof m) };
    case "const": return { ...d, value: re(d.value) };
    case "inductive":
    case "structure":
    case "type-alias":
    case "opaque-type":
    case "extern":
      return d;
  }
}
