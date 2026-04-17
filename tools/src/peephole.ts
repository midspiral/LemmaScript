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
import type { Expr, Stmt, Decl, Module, MatchArm, StmtMatchArm } from "./ir.js";

// ── Generic walkers (same shape as transform.ts) ─────────────

function mapExpr(e: Expr, f: (e: Expr) => Expr | null): Expr {
  const hit = f(e);
  if (hit) return hit;
  const r = (x: Expr) => mapExpr(x, f);
  switch (e.kind) {
    case "var": case "num": case "bool": case "str": case "constructor":
    case "emptyMap": case "emptySet": case "havoc": return e;
    case "binop": return { ...e, left: r(e.left), right: r(e.right) };
    case "unop": return { ...e, expr: r(e.expr) };
    case "implies": return { ...e, premises: e.premises.map(r), conclusion: r(e.conclusion) };
    case "app": return { ...e, args: e.args.map(r) };
    case "field": return { ...e, obj: r(e.obj) };
    case "toNat": return { ...e, expr: r(e.expr) };
    case "index": return { ...e, arr: r(e.arr), idx: r(e.idx) };
    case "record": return { ...e, spread: e.spread ? r(e.spread) : null,
      fields: e.fields.map(fi => ({ ...fi, value: r(fi.value) })) };
    case "arrayLiteral": return { ...e, elems: e.elems.map(r) };
    case "if": return { ...e, cond: r(e.cond), then: r(e.then), else: r(e.else) };
    case "match": {
      const scr = typeof e.scrutinee === "string" ? e.scrutinee : r(e.scrutinee);
      return { ...e, scrutinee: scr, arms: e.arms.map(a => ({ ...a, body: r(a.body) })) };
    }
    case "forall": return { ...e, body: r(e.body) };
    case "exists": return { ...e, body: r(e.body) };
    case "let": return { ...e, value: r(e.value), body: r(e.body) };
    case "methodCall": return { ...e, obj: r(e.obj), args: e.args.map(r) };
    case "lambda": return e;
  }
}

// (Note: peephole rules now bind once via let/var rather than substitute,
//  so semantics are preserved under any mutation. No substVar helpers needed.)

// ── Shape detection ──────────────────────────────────────────

type MethodCall = Extract<Expr, { kind: "methodCall" }>;

/** Detect map.get(k) — returns { obj, key, objTy } if so, else null. */
function isMapGet(e: Expr): { obj: Expr; key: Expr; objTy: MethodCall["objTy"] } | null {
  if (e.kind !== "methodCall" || e.objTy.kind !== "map" || e.method !== "get" || e.args.length !== 1) return null;
  return { obj: e.obj, key: e.args[0], objTy: e.objTy };
}

/** Parse Some-arm pattern like ".some _val" — returns binder name, or null for ".some _" or unparseable. */
function parseSomeBinder(pattern: string): string | null {
  if (!pattern.startsWith(".some")) return null;
  const rest = pattern.slice(5).trim();
  if (rest === "" || rest === "_") return null;
  return rest.split(/\s+/)[0];
}

/** Identify a Some/None match's arms. */
function getSomeNoneArms<A extends { pattern: string; body: any }>(arms: A[]): { someArm: A; noneArm: A; binder: string | null } | null {
  if (arms.length !== 2) return null;
  const someArm = arms.find(a => a.pattern.startsWith(".some"));
  const noneArm = arms.find(a => a.pattern === ".none");
  if (!someArm || !noneArm) return null;
  return { someArm, noneArm, binder: parseSomeBinder(someArm.pattern) };
}

// ── Expression rewrite rules ────────────────────────────────

/** Rule 1 (expr): match m.get(k) { Some(v) => sb, None => nb }
 *  → if k in m then (let v = m[k] in sb) else nb
 *  Bind once (let-expression) rather than substitute, so the verifier doesn't
 *  re-derive `k in m` at every use of v inside sb. */
function ruleMatchOnMapGetExpr(e: Expr): Expr | null {
  if (e.kind !== "match" || typeof e.scrutinee === "string") return null;
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
    (typeof m.scrutinee === "string" && m.scrutinee === e.name) ||
    (typeof m.scrutinee !== "string" && m.scrutinee.kind === "var" && m.scrutinee.name === e.name);
  if (!matchOnX) return null;
  const arms = getSomeNoneArms(m.arms);
  if (!arms) return null;
  // x must not appear in arm bodies (otherwise the binding is needed)
  if (containsVarRefExpr(arms.someArm.body, e.name) || containsVarRefExpr(arms.noneArm.body, e.name)) return null;
  const idx: Expr = { kind: "index", arr: get.obj, idx: get.key };
  const someBody: Expr = arms.binder
    ? { kind: "let", name: arms.binder, value: idx, body: arms.someArm.body }
    : arms.someArm.body;
  const has: Expr = { kind: "methodCall", obj: get.obj, objTy: get.objTy, method: "has", args: [get.key], monadic: false };
  return { kind: "if", cond: has, then: someBody, else: arms.noneArm.body };
}

function containsVarRefExpr(e: Expr, name: string): boolean {
  let found = false;
  mapExpr(e, x => {
    if (found) return x;
    if (x.kind === "var" && x.name === name) { found = true; return x; }
    return null;
  });
  return found;
}

function isBool(e: Expr, v: boolean): boolean {
  return e.kind === "bool" && e.value === v;
}

const EXPR_RULES = [
  ruleMatchOnMapGetExpr,
  ruleLetMatchOnMapGetExpr,
  ruleIfFalseElseTrue,
  ruleIfIdentity,
  ruleIfThenFalse,
  ruleIfTrueElse,
];

// ── Statement rewrite rules ──────────────────────────────────

/** Stmt rule 1: match m.get(k) { Some(v) => sb, None => nb }
 *  → if k in m { var v := m[k]; sb } else { nb }
 *  Bind once (var declaration) rather than substitute — substituting would
 *  re-evaluate m[k] at every use, changing semantics if the body mutates m. */
function ruleMatchOnMapGetStmt(s: Stmt): Stmt | null {
  if (s.kind !== "match" || typeof s.scrutinee === "string") return null;
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

const STMT_RULES = [ruleMatchOnMapGetStmt];

// ── Variable use detection ───────────────────────────────────

/** Conservative reference check: does any expression in this stmt mention `name`?
 *  Doesn't track shadowing — worst case, we miss an inlining opportunity.
 *  Used to gate let-inlining (only inline if the var is not used anywhere after). */
function containsVarRefStmt(s: Stmt, name: string): boolean {
  let found = false;
  const checkExpr = (e: Expr) => {
    if (found) return;
    mapExpr(e, x => {
      if (x.kind === "var" && x.name === name) { found = true; return x; }
      return null;
    });
  };
  const walk = (st: Stmt): void => {
    if (found) return;
    switch (st.kind) {
      case "let": case "assign": case "bind": case "let-bind":
      case "return": case "ghostLet": case "ghostAssign":
        checkExpr(st.value); return;
      case "assert": checkExpr(st.expr); return;
      case "break": case "continue": return;
      case "if":
        checkExpr(st.cond);
        st.then.forEach(walk); st.else.forEach(walk); return;
      case "match":
        if (typeof st.scrutinee === "string") {
          if (st.scrutinee === name) { found = true; return; }
        } else {
          checkExpr(st.scrutinee);
        }
        st.arms.forEach(a => a.body.forEach(walk));
        return;
      case "while":
        checkExpr(st.cond);
        st.invariants.forEach(checkExpr);
        st.body.forEach(walk);
        return;
      case "forin":
        checkExpr(st.bound);
        st.invariants.forEach(checkExpr);
        st.body.forEach(walk);
        return;
    }
  };
  walk(s);
  return found;
}

function containsVarRefStmts(stmts: Stmt[], name: string): boolean {
  return stmts.some(s => containsVarRefStmt(s, name));
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
    (typeof s2.scrutinee === "string" && s2.scrutinee === s1.name) ||
    (typeof s2.scrutinee !== "string" && s2.scrutinee.kind === "var" && s2.scrutinee.name === s1.name);
  if (!matchOnX) return null;
  const arms = getSomeNoneArms(s2.arms);
  if (!arms) return null;
  if (containsVarRefStmts(restStmts, s1.name)) return null;
  const idx: Expr = { kind: "index", arr: get.obj, idx: get.key };
  const valTy = get.objTy.kind === "map" ? get.objTy.value : { kind: "unknown" as const };
  const someBody: Stmt[] = arms.binder
    ? [{ kind: "let", name: arms.binder, type: valTy, mutable: false, value: idx }, ...arms.someArm.body]
    : arms.someArm.body;
  const has: Expr = { kind: "methodCall", obj: get.obj, objTy: get.objTy, method: "has", args: [get.key], monadic: false };
  return { kind: "if", cond: has, then: someBody, else: arms.noneArm.body };
}

/** Walk a statement list applying pair rules. */
function rewriteStmtListPairs(stmts: Stmt[]): Stmt[] {
  const result: Stmt[] = [];
  let i = 0;
  while (i < stmts.length) {
    if (i + 1 < stmts.length) {
      const merged = tryLetMatchOnMapGet(stmts[i], stmts[i + 1], stmts.slice(i + 2));
      if (merged) {
        // Recurse into the new stmt's children to peephole them too
        result.push(peepholeStmt(merged));
        i += 2;
        continue;
      }
    }
    result.push(stmts[i]);
    i++;
  }
  return result;
}

/** Peephole a statement list: per-stmt rules first, then pair rules. */
function peepholeStmts(stmts: Stmt[]): Stmt[] {
  return rewriteStmtListPairs(stmts.map(peepholeStmt));
}

// ── Bottom-up rewrite to fixed point at each node ───────────

function peepholeExpr(e: Expr): Expr {
  // Recurse into children first
  const rChildren = rewriteChildrenExpr(e);
  // Apply rules at this node, looping until no rule fires
  let cur = rChildren;
  for (let guard = 0; guard < 100; guard++) {
    let changed = false;
    for (const rule of EXPR_RULES) {
      const r = rule(cur);
      if (r !== null) {
        // Re-peephole the result (its children may now match new rules)
        cur = peepholeExpr(r);
        changed = true;
        break;
      }
    }
    if (!changed) break;
  }
  return cur;
}

function rewriteChildrenExpr(e: Expr): Expr {
  const r = peepholeExpr;
  switch (e.kind) {
    case "var": case "num": case "bool": case "str": case "constructor":
    case "emptyMap": case "emptySet": case "havoc": return e;
    case "binop": return { ...e, left: r(e.left), right: r(e.right) };
    case "unop": return { ...e, expr: r(e.expr) };
    case "implies": return { ...e, premises: e.premises.map(r), conclusion: r(e.conclusion) };
    case "app": return { ...e, args: e.args.map(r) };
    case "field": return { ...e, obj: r(e.obj) };
    case "toNat": return { ...e, expr: r(e.expr) };
    case "index": return { ...e, arr: r(e.arr), idx: r(e.idx) };
    case "record": return { ...e, spread: e.spread ? r(e.spread) : null,
      fields: e.fields.map(fi => ({ ...fi, value: r(fi.value) })) };
    case "arrayLiteral": return { ...e, elems: e.elems.map(r) };
    case "if": return { ...e, cond: r(e.cond), then: r(e.then), else: r(e.else) };
    case "match": {
      const scr = typeof e.scrutinee === "string" ? e.scrutinee : r(e.scrutinee);
      return { ...e, scrutinee: scr, arms: e.arms.map(a => ({ ...a, body: r(a.body) })) };
    }
    case "forall": return { ...e, body: r(e.body) };
    case "exists": return { ...e, body: r(e.body) };
    case "let": return { ...e, value: r(e.value), body: r(e.body) };
    case "methodCall": return { ...e, obj: r(e.obj), args: e.args.map(r) };
    case "lambda": return { ...e, body: peepholeStmts(e.body) };
  }
}

function peepholeStmt(s: Stmt): Stmt {
  const rChildren = rewriteChildrenStmt(s);
  let cur = rChildren;
  for (let guard = 0; guard < 100; guard++) {
    let changed = false;
    for (const rule of STMT_RULES) {
      const r = rule(cur);
      if (r !== null) {
        cur = peepholeStmt(r);
        changed = true;
        break;
      }
    }
    if (!changed) break;
  }
  return cur;
}

function rewriteChildrenStmt(s: Stmt): Stmt {
  const re = peepholeExpr;
  const rs = peepholeStmts;
  switch (s.kind) {
    case "let": return { ...s, value: re(s.value) };
    case "assign": return { ...s, value: re(s.value) };
    case "bind": return { ...s, value: re(s.value) };
    case "let-bind": return { ...s, value: re(s.value) };
    case "return": return { ...s, value: re(s.value) };
    case "break": case "continue": return s;
    case "if": return { ...s, cond: re(s.cond), then: rs(s.then), else: rs(s.else) };
    case "match": {
      const scr = typeof s.scrutinee === "string" ? s.scrutinee : re(s.scrutinee);
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

export function peepholeModule(mod: Module): Module {
  return { ...mod, decls: mod.decls.map(peepholeDecl) };
}

function peepholeDecl(d: Decl): Decl {
  switch (d.kind) {
    case "def":
      return { ...d, body: peepholeExpr(d.body),
        requires: d.requires.map(peepholeExpr), ensures: d.ensures.map(peepholeExpr),
        decreases: d.decreases ? peepholeExpr(d.decreases) : null };
    case "def-by-method":
      return { ...d, methodBody: peepholeStmts(d.methodBody),
        requires: d.requires.map(peepholeExpr), ensures: d.ensures.map(peepholeExpr),
        decreases: d.decreases ? peepholeExpr(d.decreases) : null };
    case "method":
      return { ...d, body: peepholeStmts(d.body),
        requires: d.requires.map(peepholeExpr), ensures: d.ensures.map(peepholeExpr) };
    case "namespace": return { ...d, decls: d.decls.map(peepholeDecl) };
    case "class": return { ...d, methods: d.methods.map(m => peepholeDecl(m) as typeof m) };
    case "const": return { ...d, value: peepholeExpr(d.value) };
    case "inductive":
    case "structure":
    case "type-alias":
      return d;
  }
}
