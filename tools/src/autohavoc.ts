/**
 * auto-havoc pass — validation mode.
 *
 * Rewrites every *unmodellable* expression in the Typed IR to a `havoc` node,
 * and drops unmodellable side-effecting statements. "Unmodellable" = the value
 * derives from something outside LemmaScript's model (an `unknown`-typed
 * receiver/result — e.g. `res.status()`, `req.body`, `JSON.parse(x)`,
 * `process.env.X ?? y`, `uuidv4()` — or an anonymous object literal).
 *
 * This is the abstraction policy for verifying *validation* properties: the
 * only thing that matters is that values reaching a contracted sink (an extern
 * with `//@ requires sanitizer(x)`) are dominated by the sanitizer guard.
 * Everything else is noise and is replaced by an arbitrary value.
 *
 * Soundness: `havoc` is a nondeterministic over-approximation — the verifier
 * assumes nothing about a havoc'd value — so this can only make a proof FAIL
 * (false positive), never spuriously pass. It uses havoc, never assume.
 * (Trust boundary: a real sink hidden inside an unmodellable call is invisible;
 * sinks must be the declared/annotated externs.)
 *
 * It runs after narrow, so any legitimate optional (`?.`, `??` on an
 * optional-typed value) is already a `someMatch`; a `nullish`/`optChain` that
 * survives to here is unmodellable and gets havoc'd.
 */

import type { TExpr, TStmt, TModule } from "./typedir.js";

/** A node whose own value can't be modeled and must become an arbitrary value.
 *  Leaves (var/literal/havoc) are never havoc'd — a reference to an already
 *  havoc'd variable is fine; only the *source* expression is replaced. */
function isBadNode(e: TExpr): boolean {
  switch (e.kind) {
    case "var": case "num": case "str": case "bool": case "havoc":
      return false;
    // A field/index is unmodellable when its *object* is opaque (`req.body`,
    // `process.env.X`). It is NOT unmodellable just because its own type is
    // `unknown`: a method reference on a known receiver (`path.includes`) has
    // `unknown` type yet emits fine — the method dispatch happens at emit on
    // the object's type, so havocing it would wreck a legitimate call.
    case "field": return e.obj.ty.kind === "unknown";
    case "index": return e.obj.ty.kind === "unknown";
    // anonymous object literal — Dafny has no model for it
    case "record": return e.ty.kind !== "user";
    // a call / nullish / opt-chain / conditional whose *result* is opaque
    default: return e.ty.kind === "unknown";
  }
}

/** Does the subtree (including lambda bodies) contain anything unmodellable?
 *  Used to havoc a *whole* call like `xs.map(v => ({...}))` whose receiver is
 *  modellable but whose lambda produces an unmodellable value — havocing the
 *  lambda interior would leave a nondeterministic `*` inside a pure lambda. */
function containsBad(e: TExpr): boolean {
  let found = false;
  const visit = (n: TExpr): void => {
    if (found) return;
    if (isBadNode(n)) { found = true; return; }
    forEachChildExpr(n, visit);
  };
  visit(e);
  return found;
}

function mustHavoc(e: TExpr): boolean {
  if (isBadNode(e)) return true;
  if (e.kind === "call" && e.args.some(a => a.kind === "lambda" && a.body.some(s => stmtContainsBad(s))))
    return true;
  return false;
}

// ── structural recursion helpers ────────────────────────────

function forEachChildExpr(e: TExpr, f: (c: TExpr) => void): void {
  switch (e.kind) {
    case "binop": f(e.left); f(e.right); return;
    case "unop": f(e.expr); return;
    case "call": f(e.fn); e.args.forEach(f); return;
    case "index": f(e.obj); f(e.idx); return;
    case "field": f(e.obj); return;
    case "record": if (e.spread) f(e.spread); e.fields.forEach(fl => f(fl.value)); return;
    case "arrayLiteral": e.elems.forEach(f); return;
    case "conditional": f(e.cond); f(e.then); f(e.else); return;
    case "optChain": f(e.obj); return;
    case "nullish": f(e.left); f(e.right); return;
    case "forall": case "exists": f(e.body); return;
    case "someMatch": f(e.scrutinee); f(e.someBody); f(e.noneBody); return;
    case "tagMatch": f(e.scrutinee); e.cases.forEach(c => f(c.body)); if (e.fallthrough) f(e.fallthrough); return;
    case "lambda": e.body.forEach(s => forEachChildExprInStmt(s, f)); return;
  }
}

function forEachChildExprInStmt(s: TStmt, f: (c: TExpr) => void): void {
  switch (s.kind) {
    case "let": case "ghostLet": f(s.init); return;
    case "assign": case "ghostAssign": f(s.value); return;
    case "return": f(s.value); return;
    case "expr": f(s.expr); return;
    case "assert": f(s.expr); return;
    case "if": f(s.cond); s.then.forEach(st => forEachChildExprInStmt(st, f)); s.else.forEach(st => forEachChildExprInStmt(st, f)); return;
    case "while": f(s.cond); s.body.forEach(st => forEachChildExprInStmt(st, f)); return;
    case "forof": f(s.iterable); s.body.forEach(st => forEachChildExprInStmt(st, f)); return;
    case "switch": f(s.expr); s.cases.forEach(c => c.body.forEach(st => forEachChildExprInStmt(st, f))); s.defaultBody.forEach(st => forEachChildExprInStmt(st, f)); return;
    case "someMatch": f(s.scrutinee); s.someBody.forEach(st => forEachChildExprInStmt(st, f)); s.noneBody.forEach(st => forEachChildExprInStmt(st, f)); return;
    case "tagMatch": f(s.scrutinee); s.cases.forEach(c => c.body.forEach(st => forEachChildExprInStmt(st, f))); s.fallthrough.forEach(st => forEachChildExprInStmt(st, f)); return;
  }
}

function stmtContainsBad(s: TStmt): boolean {
  let found = false;
  forEachChildExprInStmt(s, e => { if (containsBad(e)) found = true; });
  return found;
}

// ── rewrite ──────────────────────────────────────────────────

function rewriteExpr(e: TExpr): TExpr {
  if (mustHavoc(e)) return { kind: "havoc", ty: e.ty };
  switch (e.kind) {
    case "var": case "num": case "str": case "bool": case "havoc": return e;
    case "binop": return { ...e, left: rewriteExpr(e.left), right: rewriteExpr(e.right) };
    case "unop": return { ...e, expr: rewriteExpr(e.expr) };
    case "call": return { ...e, fn: rewriteExpr(e.fn), args: e.args.map(rewriteExpr) };
    case "index": return { ...e, obj: rewriteExpr(e.obj), idx: rewriteExpr(e.idx) };
    case "field": return { ...e, obj: rewriteExpr(e.obj) };
    case "record": return { ...e, spread: e.spread ? rewriteExpr(e.spread) : null,
      fields: e.fields.map(fl => ({ ...fl, value: rewriteExpr(fl.value) })) };
    case "arrayLiteral": return { ...e, elems: e.elems.map(rewriteExpr) };
    case "conditional": return { ...e, cond: rewriteExpr(e.cond), then: rewriteExpr(e.then), else: rewriteExpr(e.else) };
    case "optChain": return { ...e, obj: rewriteExpr(e.obj) };
    case "nullish": return { ...e, left: rewriteExpr(e.left), right: rewriteExpr(e.right) };
    case "forall": case "exists": return { ...e, body: rewriteExpr(e.body) };
    case "someMatch": return { ...e, scrutinee: rewriteExpr(e.scrutinee), someBody: rewriteExpr(e.someBody), noneBody: rewriteExpr(e.noneBody) };
    case "tagMatch": return { ...e, scrutinee: rewriteExpr(e.scrutinee),
      cases: e.cases.map(c => ({ ...c, body: rewriteExpr(c.body) })),
      fallthrough: e.fallthrough ? rewriteExpr(e.fallthrough) : null };
    case "lambda": return { ...e, body: rewriteStmts(e.body) };
  }
}

/** A condition in a boolean context. If it touches anything unmodellable
 *  (`!fs.existsSync(...)`), the whole condition becomes a nondeterministic
 *  `bool` — havocing a subexpression would leave a non-bool `*` under `!`/`if`.
 *  A fully modellable guard (`!validPath(x)`, `s === ""`) is left intact, so
 *  the verifier still reasons about it. */
function rewriteCond(e: TExpr): TExpr {
  if (containsBad(e)) return { kind: "havoc", ty: { kind: "bool" } };
  return rewriteExpr(e);
}

function rewriteStmts(stmts: TStmt[]): TStmt[] {
  const out: TStmt[] = [];
  for (const s of stmts) {
    // A side-effecting statement whose value is unmodellable (e.g.
    // `xs.forEach(...)`, `console.log(x)`) carries no verification content —
    // drop it. Value-binding statements keep their binding but havoc the RHS.
    if (s.kind === "expr" && mustHavoc(s.expr)) continue;
    out.push(rewriteStmt(s));
  }
  return out;
}

function rewriteStmt(s: TStmt): TStmt {
  switch (s.kind) {
    case "let": return { ...s, init: rewriteExpr(s.init) };
    case "ghostLet": return { ...s, init: rewriteExpr(s.init) };
    case "assign": return { ...s, value: rewriteExpr(s.value) };
    case "ghostAssign": return { ...s, value: rewriteExpr(s.value) };
    case "return": return { ...s, value: rewriteExpr(s.value) };
    case "expr": return { ...s, expr: rewriteExpr(s.expr) };
    case "assert": return { ...s, expr: rewriteExpr(s.expr) };
    case "if": return { ...s, cond: rewriteCond(s.cond), then: rewriteStmts(s.then), else: rewriteStmts(s.else) };
    case "while": return { ...s, cond: rewriteCond(s.cond), body: rewriteStmts(s.body) };
    case "forof": return { ...s, iterable: rewriteExpr(s.iterable), body: rewriteStmts(s.body) };
    case "switch": return { ...s, expr: rewriteExpr(s.expr),
      cases: s.cases.map(c => ({ ...c, body: rewriteStmts(c.body) })),
      defaultBody: rewriteStmts(s.defaultBody) };
    case "someMatch": return { ...s, scrutinee: rewriteExpr(s.scrutinee), someBody: rewriteStmts(s.someBody), noneBody: rewriteStmts(s.noneBody) };
    case "tagMatch": return { ...s, scrutinee: rewriteExpr(s.scrutinee),
      cases: s.cases.map(c => ({ ...c, body: rewriteStmts(c.body) })),
      fallthrough: rewriteStmts(s.fallthrough) };
    case "break": case "continue": case "throw": return s;
  }
}

/** Does any statement in the body contain a havoc expression? Havoc is only
 *  valid in Dafny `method`s (its `*` can't appear in a deterministic
 *  `function`), so a body we've havoc'd must be classified impure. */
function bodyHasHavoc(stmts: TStmt[]): boolean {
  let found = false;
  const visit = (e: TExpr): void => {
    if (found) return;
    if (e.kind === "havoc") { found = true; return; }
    forEachChildExpr(e, visit);
  };
  for (const s of stmts) forEachChildExprInStmt(s, visit);
  return found;
}

/** Apply the auto-havoc abstraction to functions opted in via `//@ autohavoc`
 *  (file-level or per-function). A no-op when nothing is annotated. When any
 *  function opts in, also drop module constants whose initializer is
 *  unmodellable (e.g. `const fs = require("fs")` pulled in by reachability). */
export function autoHavocModule(mod: TModule): TModule {
  if (!mod.functions.some(f => f.autohavoc)) return mod;
  return {
    ...mod,
    constants: mod.constants.filter(c => !containsBad(c.value)),
    functions: mod.functions.map(f => {
      if (!f.autohavoc) return f;
      const body = rewriteStmts(f.body);
      // Havoc forces Dafny `method` emission (`*` is invalid in a `function`).
      const isPure = f.isPure && !bodyHasHavoc(body);
      return { ...f, body, isPure, forcePure: f.forcePure && isPure };
    }),
  };
}
