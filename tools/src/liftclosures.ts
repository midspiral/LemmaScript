/**
 * liftClosures — lift a non-escaping, parameterless void thunk that captures and
 * mutates enclosing locals into a top-level routine (Raw IR → Raw IR, between
 * extract and resolve).
 *
 * A `const f = () => { …stmts… }` whose every use in the enclosing function is a
 * statement-position call `f()` is lifted to a function `f(...captures)` returning a
 * record of the captures it mutates; each call site threads the record back:
 *
 *   const f = () => { result.push(x); pending = [] };  f();
 *     →  function f(result, pending): FState { …; return { result, pending } }
 *        const s = f(result, pending); result = s.result; pending = s.pending;
 *
 * Sound because the mutable environment has a single owner (the enclosing function):
 * the captures' pre-values are passed in, the post-values come back in the record.
 * Anything that breaks single-ownership — the closure escaping, taking parameters,
 * recursing, or nesting another closure — is left untouched (it then hits the
 * existing multi-statement-lambda skip), never miscompiled.
 */

import { RawModule, RawFunction, RawStmt, RawExpr, RawLet } from "./rawir.js";
import { TypeDeclInfo } from "./types.js";

/** Array methods that mutate their receiver in place (vs. returning a new value). */
const MUTATORS = new Set(["push", "unshift", "pop", "shift", "splice", "sort", "reverse", "fill", "copyWithin", "add", "delete", "set", "clear"]);

// ── Raw IR traversal ─────────────────────────────────────────

function walkExpr(e: RawExpr, visit: (x: RawExpr) => void): void {
  visit(e);
  switch (e.kind) {
    case "binop": walkExpr(e.left, visit); walkExpr(e.right, visit); return;
    case "unop": case "nonNull": walkExpr(e.expr, visit); return;
    case "call": walkExpr(e.fn, visit); e.args.forEach(a => walkExpr(a, visit)); return;
    case "index": walkExpr(e.obj, visit); walkExpr(e.idx, visit); return;
    case "field": walkExpr(e.obj, visit); return;
    case "record": if (e.spread) walkExpr(e.spread, visit); e.fields.forEach(f => walkExpr(f.value, visit)); return;
    case "recordMerge": walkExpr(e.base, visit); walkExpr(e.override, visit); return;
    case "arrayLiteral": e.elems.forEach(x => walkExpr(x, visit)); return;
    case "conditional": walkExpr(e.cond, visit); walkExpr(e.then, visit); walkExpr(e.else, visit); return;
    case "optChain": walkExpr(e.obj, visit); e.chain.forEach(s => { if (s.kind === "call") s.args.forEach(a => walkExpr(a, visit)); else if (s.kind === "index") walkExpr(s.idx, visit); }); return;
    case "nullish": walkExpr(e.left, visit); walkExpr(e.right, visit); return;
    case "lambda": if (Array.isArray(e.body)) e.body.forEach(s => walkStmt(s, () => {}, visit)); else walkExpr(e.body, visit); return;
    case "forall": case "exists": walkExpr(e.body, visit); return;
    default: return;  // leaf: var, num, str, bool, result, havoc, emptyCollection
  }
}

function walkStmt(s: RawStmt, visitStmt: (s: RawStmt) => void, visitExpr: (x: RawExpr) => void): void {
  visitStmt(s);
  switch (s.kind) {
    case "let": walkExpr(s.init, visitExpr); return;
    case "assign": walkExpr(s.value, visitExpr); return;
    case "return": case "expr": walkExpr(s.kind === "return" ? s.value : s.expr, visitExpr); return;
    case "if": walkExpr(s.cond, visitExpr); s.then.forEach(t => walkStmt(t, visitStmt, visitExpr)); s.else.forEach(t => walkStmt(t, visitStmt, visitExpr)); return;
    case "while": walkExpr(s.cond, visitExpr); s.body.forEach(t => walkStmt(t, visitStmt, visitExpr)); return;
    case "forof": walkExpr(s.iterable, visitExpr); s.body.forEach(t => walkStmt(t, visitStmt, visitExpr)); return;
    case "switch": walkExpr(s.expr, visitExpr); s.cases.forEach(c => c.body.forEach(t => walkStmt(t, visitStmt, visitExpr))); s.defaultBody.forEach(t => walkStmt(t, visitStmt, visitExpr)); return;
    default: return;  // break/continue/throw/ghost*/assert — no captured-local refs of interest
  }
}

/** Root variable of an access path (`b.items` → `b`, `m.get(k)` receiver → `m`), or null. */
function rootVar(e: RawExpr): string | null {
  let cur: RawExpr = e;
  while (true) {
    if (cur.kind === "var") return cur.name;
    if (cur.kind === "field") cur = cur.obj;
    else if (cur.kind === "index") cur = cur.obj;
    else if (cur.kind === "nonNull") cur = cur.expr;
    else return null;
  }
}

// ── Names bound inside a block (so they aren't free) ─────────

function boundNames(stmts: RawStmt[], into: Set<string>): void {
  for (const s of stmts) {
    if (s.kind === "let" || s.kind === "ghostLet") into.add(s.name);
    if (s.kind === "if") { boundNames(s.then, into); boundNames(s.else, into); }
    if (s.kind === "while") boundNames(s.body, into);
    if (s.kind === "forof") { s.names.forEach(n => into.add(n)); boundNames(s.body, into); }
    if (s.kind === "switch") { s.cases.forEach(c => boundNames(c.body, into)); boundNames(s.defaultBody, into); }
  }
}

/** Free variable names referenced anywhere in a block. */
function freeVars(stmts: RawStmt[]): Set<string> {
  const bound = new Set<string>();
  boundNames(stmts, bound);
  const refs = new Set<string>();
  stmts.forEach(s => walkStmt(s, () => {}, e => { if (e.kind === "var" && !bound.has(e.name)) refs.add(e.name); }));
  return refs;
}

/** Capture roots mutated in a block: reassignment targets and in-place mutator receivers. */
function mutatedRoots(stmts: RawStmt[]): Set<string> {
  const out = new Set<string>();
  stmts.forEach(s => walkStmt(s,
    st => { if (st.kind === "assign") out.add(st.target); },
    e => {
      if (e.kind === "call" && e.fn.kind === "field" && MUTATORS.has(e.fn.field)) {
        const r = rootVar(e.fn.obj); if (r) out.add(r);
      }
    }));
  return out;
}

// ── The lift ─────────────────────────────────────────────────

function cap(s: string): string { return s.charAt(0).toUpperCase() + s.slice(1); }

/** Rewrite every `return …` in a void-thunk body to `return <state>`. */
function rewriteReturns(stmts: RawStmt[], state: RawExpr): RawStmt[] {
  return stmts.map(s => {
    if (s.kind === "return") return { ...s, value: state };
    if (s.kind === "if") return { ...s, then: rewriteReturns(s.then, state), else: rewriteReturns(s.else, state) };
    if (s.kind === "while") return { ...s, body: rewriteReturns(s.body, state) };
    if (s.kind === "forof") return { ...s, body: rewriteReturns(s.body, state) };
    if (s.kind === "switch") return { ...s, cases: s.cases.map(c => ({ ...c, body: rewriteReturns(c.body, state) })), defaultBody: rewriteReturns(s.defaultBody, state) };
    return s;
  });
}

function endsInReturn(stmts: RawStmt[]): boolean {
  const last = stmts[stmts.length - 1];
  return !!last && last.kind === "return";
}

interface LiftResult { fn: RawFunction; typeDecl: TypeDeclInfo; liftedName: string; recordName: string; captureOrder: string[]; mutated: string[]; }

/** Try to lift the closure bound by `decl` within enclosing `host`. Null ⇒ not liftable. */
function tryLift(decl: RawLet, host: RawFunction, taken: Set<string>): LiftResult | null {
  const lam = decl.init;
  if (lam.kind !== "lambda" || !Array.isArray(lam.body)) return null;
  if (lam.params.length !== 0) return null;                 // Slice 2: parameters
  const body = lam.body;

  // Nested closure inside the body → breaks the single-owner analysis. Refuse.
  let hasNestedLambda = false;
  body.forEach(s => walkStmt(s, () => {}, e => { if (e.kind === "lambda") hasNestedLambda = true; }));
  if (hasNestedLambda) return null;

  const fv = freeVars(body);
  if (fv.has(decl.name)) return null;                       // recursive self-reference

  // Captures = free vars that name an enclosing param or local.
  const typeOf = new Map<string, string>();
  for (const p of host.params) typeOf.set(p.name, p.tsType);
  host.body.forEach(s => { if (s.kind === "let" && s.name !== decl.name && s.tsType) typeOf.set(s.name, s.tsType); });

  const captureOrder: string[] = [];
  for (const name of fv) if (typeOf.has(name)) captureOrder.push(name);
  if (captureOrder.length === 0) return null;
  // A capture whose declared type we can't name as a string can't become a param. Refuse.
  if (captureOrder.some(c => !typeOf.get(c))) return null;

  const muts = mutatedRoots(body);
  const mutated = captureOrder.filter(c => muts.has(c));
  if (mutated.length === 0) return null;                    // nothing to thread → not this feature

  const liftedName = taken.has(decl.name) ? `${host.name}_${decl.name}` : decl.name;
  const recordName = (() => { let n = `${cap(decl.name)}State`; while (taken.has(n)) n = `${host.name}_${n}`; return n; })();
  taken.add(liftedName); taken.add(recordName);

  const stateRecord: RawExpr = { kind: "record", spread: null, fields: mutated.map(c => ({ name: c, value: { kind: "var", name: c } })) };
  let liftedBody = rewriteReturns(body, stateRecord);
  if (!endsInReturn(liftedBody)) liftedBody = [...liftedBody, { kind: "return", value: stateRecord, line: decl.line }];

  const params = captureOrder.map(c => ({ name: c, tsType: typeOf.get(c)! }));
  const fn: RawFunction = {
    name: liftedName, exported: false, typeParams: [],
    params, tsParams: params.map(p => ({ kind: "simple" as const, binds: [p.name] })),
    returnType: recordName, requires: [], ensures: [], contract: [], decreases: null,
    pure: false, autohavoc: host.autohavoc, typeAnnotations: [], body: liftedBody, line: decl.line,
  };
  const typeDecl: TypeDeclInfo = { name: recordName, kind: "record", fields: mutated.map(c => ({ name: c, tsType: typeOf.get(c)! })) };
  return { fn, typeDecl, liftedName, recordName, captureOrder, mutated };
}

/** Is `s` a statement-position call `f()`? */
function isThunkCall(s: RawStmt, name: string): boolean {
  return s.kind === "expr" && s.expr.kind === "call" && s.expr.fn.kind === "var" && s.expr.fn.name === name && s.expr.args.length === 0;
}

/** Replace each `f()` in a statement list (recursively) with the threaded call. */
function rewriteCalls(stmts: RawStmt[], name: string, L: LiftResult, fresh: () => string): RawStmt[] {
  const out: RawStmt[] = [];
  for (const s of stmts) {
    if (isThunkCall(s, name)) {
      const sv = fresh();
      out.push({ kind: "let", name: sv, mutable: false, tsType: L.recordName, init: { kind: "call", fn: { kind: "var", name: L.liftedName }, args: L.captureOrder.map(c => ({ kind: "var" as const, name: c })) }, line: s.line });
      for (const c of L.mutated) out.push({ kind: "assign", target: c, value: { kind: "field", obj: { kind: "var", name: sv }, field: c }, line: s.line });
      continue;
    }
    if (s.kind === "if") out.push({ ...s, then: rewriteCalls(s.then, name, L, fresh), else: rewriteCalls(s.else, name, L, fresh) });
    else if (s.kind === "while") out.push({ ...s, body: rewriteCalls(s.body, name, L, fresh) });
    else if (s.kind === "forof") out.push({ ...s, body: rewriteCalls(s.body, name, L, fresh) });
    else if (s.kind === "switch") out.push({ ...s, cases: s.cases.map(c => ({ ...c, body: rewriteCalls(c.body, name, L, fresh) })), defaultBody: rewriteCalls(s.defaultBody, name, L, fresh) });
    else out.push(s);
  }
  return out;
}

/** All uses of `name` in `host` outside its own declaration; true iff every one is a statement-call. */
function onlyCalledInStatements(host: RawFunction, name: string): boolean {
  let total = 0, calls = 0;
  // count statement-calls
  const countCalls = (stmts: RawStmt[]) => stmts.forEach(s => {
    if (isThunkCall(s, name)) calls++;
    if (s.kind === "if") { countCalls(s.then); countCalls(s.else); }
    if (s.kind === "while" || s.kind === "forof") countCalls(s.body);
    if (s.kind === "switch") { s.cases.forEach(c => countCalls(c.body)); countCalls(s.defaultBody); }
  });
  countCalls(host.body);
  // count every reference (excluding the closure's own `let` initializer)
  for (const s of host.body) {
    if (s.kind === "let" && s.init.kind === "lambda") continue;  // the decl itself
    walkStmt(s, () => {}, e => { if (e.kind === "var" && e.name === name) total++; });
  }
  return total > 0 && total === calls;
}

function liftInFunction(host: RawFunction, taken: Set<string>, addFn: (f: RawFunction) => void, addType: (t: TypeDeclInfo) => void): RawFunction {
  let body = host.body;
  let counter = 0;
  const fresh = () => `_lc${counter++}`;
  // Top-level closure declarations in this function, in order.
  for (const decl of host.body) {
    if (decl.kind !== "let" || decl.init.kind !== "lambda") continue;
    if (!onlyCalledInStatements(host, decl.name)) continue;     // escapes → leave it
    const L = tryLift(decl, host, taken);
    if (!L) continue;
    addFn(L.fn); addType(L.typeDecl);
    // Drop the closure `let`, rewrite its calls, and make mutated captures mutable.
    body = rewriteCalls(body.filter(s => s !== decl), decl.name, L, fresh)
      .map(s => (s.kind === "let" && L.mutated.includes(s.name)) ? { ...s, mutable: true } : s);
  }
  return { ...host, body };
}

export function liftClosures(mod: RawModule): RawModule {
  const taken = new Set<string>([...mod.functions.map(f => f.name), ...mod.typeDecls.map(t => t.name), ...mod.constants.map(c => c.name)]);
  const extraFns: RawFunction[] = [];
  const extraTypes: TypeDeclInfo[] = [];
  const functions = mod.functions.map(f => liftInFunction(f, taken, x => extraFns.push(x), t => extraTypes.push(t)));
  if (extraFns.length === 0) return mod;
  return { ...mod, typeDecls: [...mod.typeDecls, ...extraTypes], functions: [...extraFns, ...functions] };
}
