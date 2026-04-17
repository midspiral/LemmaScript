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

// ── Variable substitution ────────────────────────────────────

/** Replace var with replacement in expression, respecting binders. */
function substVarExpr(e: Expr, name: string, replacement: Expr): Expr {
  return mapExpr(e, x => {
    if (x.kind === "var" && x.name === name) return replacement;
    if (x.kind === "let" && x.name === name) {
      return { ...x, value: substVarExpr(x.value, name, replacement) };
    }
    if (x.kind === "forall" && x.var === name) return x;
    if (x.kind === "exists" && x.var === name) return x;
    return null;
  });
}

/** Replace var with replacement in a list of statements. */
function substVarStmts(stmts: Stmt[], name: string, replacement: Expr): Stmt[] {
  return stmts.map(s => substVarStmt(s, name, replacement));
}

function substVarStmt(s: Stmt, name: string, replacement: Expr): Stmt {
  const re = (e: Expr) => substVarExpr(e, name, replacement);
  switch (s.kind) {
    case "let":
      if (s.name === name) return { ...s, value: re(s.value) };
      return { ...s, value: re(s.value) };
    case "assign":
      return { ...s, value: re(s.value) };
    case "bind":
    case "let-bind":
      if (s.kind === "let-bind" && s.name === name) return { ...s, value: re(s.value) };
      return { ...s, value: re(s.value) };
    case "return": return { ...s, value: re(s.value) };
    case "break": case "continue": return s;
    case "if": return { ...s, cond: re(s.cond),
      then: substVarStmts(s.then, name, replacement),
      else: substVarStmts(s.else, name, replacement) };
    case "match": {
      const scr = typeof s.scrutinee === "string" ? s.scrutinee : re(s.scrutinee);
      return { ...s, scrutinee: scr,
        arms: s.arms.map(a => ({ ...a, body: substVarStmts(a.body, name, replacement) })) };
    }
    case "while": return { ...s, cond: re(s.cond), invariants: s.invariants.map(re),
      body: substVarStmts(s.body, name, replacement) };
    case "forin":
      if (s.idx === name) return { ...s, bound: re(s.bound), invariants: s.invariants.map(re), body: s.body };
      return { ...s, bound: re(s.bound), invariants: s.invariants.map(re),
        body: substVarStmts(s.body, name, replacement) };
    case "ghostLet":
      if (s.name === name) return { ...s, value: re(s.value) };
      return { ...s, value: re(s.value) };
    case "ghostAssign": return { ...s, value: re(s.value) };
    case "assert": return { ...s, expr: re(s.expr) };
  }
}

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

/** Rule 1 (expr): match m.get(k) { Some(v) => sb, None => nb } → if k in m then sb[v := m[k]] else nb */
function ruleMatchOnMapGetExpr(e: Expr): Expr | null {
  if (e.kind !== "match" || typeof e.scrutinee === "string") return null;
  const get = isMapGet(e.scrutinee);
  if (!get) return null;
  const arms = getSomeNoneArms(e.arms);
  if (!arms) return null;
  const idx: Expr = { kind: "index", arr: get.obj, idx: get.key };
  const someBody = arms.binder ? substVarExpr(arms.someArm.body, arms.binder, idx) : arms.someArm.body;
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

function isBool(e: Expr, v: boolean): boolean {
  return e.kind === "bool" && e.value === v;
}

const EXPR_RULES = [
  ruleMatchOnMapGetExpr,
  ruleIfFalseElseTrue,
  ruleIfIdentity,
  ruleIfThenFalse,
  ruleIfTrueElse,
];

// ── Statement rewrite rules ──────────────────────────────────

/** Stmt rule 1: match m.get(k) { Some(v) => sb, None => nb } → if k in m { sb[v := m[k]] } else { nb } */
function ruleMatchOnMapGetStmt(s: Stmt): Stmt | null {
  if (s.kind !== "match" || typeof s.scrutinee === "string") return null;
  const get = isMapGet(s.scrutinee);
  if (!get) return null;
  const arms = getSomeNoneArms(s.arms);
  if (!arms) return null;
  const idx: Expr = { kind: "index", arr: get.obj, idx: get.key };
  const someBody = arms.binder ? substVarStmts(arms.someArm.body, arms.binder, idx) : arms.someArm.body;
  const has: Expr = { kind: "methodCall", obj: get.obj, objTy: get.objTy, method: "has", args: [get.key], monadic: false };
  return { kind: "if", cond: has, then: someBody, else: arms.noneArm.body };
}

const STMT_RULES = [ruleMatchOnMapGetStmt];

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
    case "lambda": return { ...e, body: e.body.map(peepholeStmt) };
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
  const rs = (stmts: Stmt[]) => stmts.map(peepholeStmt);
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
      return { ...d, methodBody: d.methodBody.map(peepholeStmt),
        requires: d.requires.map(peepholeExpr), ensures: d.ensures.map(peepholeExpr),
        decreases: d.decreases ? peepholeExpr(d.decreases) : null };
    case "method":
      return { ...d, body: d.body.map(peepholeStmt),
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
