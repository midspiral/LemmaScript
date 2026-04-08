/**
 * Resolve — Raw IR → Typed IR.
 *
 * Uses linked environments (Scheme-style) for lexical scoping.
 * No mutation — each let extends the chain, lookup walks it.
 */

import type { RawExpr, RawStmt, RawFunction, RawModule } from "./rawir.js";
import type { Ty, TExpr, TStmt, TFunction, TModule, TParam, CallKind } from "./typedir.js";
import { parseTsType } from "./types.js";
import type { TypeDeclInfo } from "./types.js";
import { parseExpr } from "./specparser.js";

// ── Environment ──────────────────────────────────────────────

interface Env {
  name: string;
  ty: Ty;
  parent: Env | null;
}

function lookup(env: Env | null, name: string): Ty | undefined {
  if (!env) return undefined;
  return env.name === name ? env.ty : lookup(env.parent, name);
}

function extend(env: Env | null, name: string, ty: Ty): Env {
  return { name, ty, parent: env };
}

// ── Context ──────────────────────────────────────────────────

interface Ctx {
  env: Env | null;
  typeDecls: TypeDeclInfo[];
  overrides: Map<string, string>;
  allowResult: boolean;
  returnTy: Ty;
  pureFns: Set<string>;  // names of pure functions in this module
  inSpec: boolean;
  inLambda: boolean;
}

function withEnv(ctx: Ctx, env: Env | null): Ctx {
  return { ...ctx, env };
}

// ── TS type → Ty ─────────────────────────────────────────────

function resolveTsType(tsType: string, overrides: Map<string, string>, varName?: string): Ty {
  if (varName) {
    const o = overrides.get(varName);
    if (o) return parseTsType(o);
  }
  return parseTsType(tsType);
}

/** If expr is a string literal and targetTy is a user type, coerce the literal's type. */
function coerceStr(expr: TExpr, targetTy: Ty): TExpr {
  if (expr.kind === "str" && targetTy.kind === "user") return { ...expr, ty: targetTy };
  return expr;
}

// ── Helpers ──────────────────────────────────────────────────

/** Detect `v !== undefined` or `undefined !== v` where v: optional<T>. */
function narrowOptional(cond: RawExpr, env: Env | null): { varName: string; innerTy: Ty; inThen: boolean } | null {
  if (cond.kind !== "binop" || (cond.op !== "!==" && cond.op !== "===")) return null;
  // v !== undefined  OR  undefined !== v
  let varName: string | null = null;
  if (cond.left.kind === "var" && cond.right.kind === "var" && cond.right.name === "undefined") varName = cond.left.name;
  if (cond.right.kind === "var" && cond.left.kind === "var" && cond.left.name === "undefined") varName = cond.right.name;
  if (!varName) return null;
  const ty = lookup(env, varName);
  if (!ty || ty.kind !== "optional") return null;
  return { varName, innerTy: ty.inner, inThen: cond.op === "!==" };
}

/** TS reference types that become value types in Dafny/Lean — const bindings need mutable var. */
function isRefMutableInTS(ty: Ty): boolean {
  return ty.kind === "array" || ty.kind === "map" || ty.kind === "set";
}

function findDecl(ctx: Ctx, name: string): TypeDeclInfo | undefined {
  return ctx.typeDecls.find(d => d.name === name);
}

function getDiscriminant(ctx: Ctx, typeName: string): string | undefined {
  return findDecl(ctx, typeName)?.discriminant;
}

/** Infer quantifier variable type from usage in body.
 *  If the variable is used as a map/set key (e.g. map.has(k), map.get(k)),
 *  return the collection's key type. Otherwise return null (default to int). */
function inferQuantVarType(varName: string, body: RawExpr, ctx: Ctx): Ty | null {
  // Look for calls like map.has(k), map.get(k), or array.includes(k) where k is our variable
  if (body.kind === "call" && body.fn.kind === "field" &&
      (body.fn.field === "has" || body.fn.field === "get" || body.fn.field === "includes") &&
      body.args.length === 1 && body.args[0].kind === "var" && body.args[0].name === varName) {
    const objTy = lookup(ctx.env, body.fn.obj.kind === "var" ? body.fn.obj.name : "");
    if (objTy?.kind === "map") return objTy.key;
    if (objTy?.kind === "set") return objTy.elem;
    if (objTy?.kind === "array") return objTy.elem;
  }
  // Recurse into subexpressions
  if (body.kind === "binop") {
    return inferQuantVarType(varName, body.left, ctx) ?? inferQuantVarType(varName, body.right, ctx);
  }
  if (body.kind === "unop") return inferQuantVarType(varName, body.expr, ctx);
  if (body.kind === "call") {
    for (const a of body.args) { const r = inferQuantVarType(varName, a, ctx); if (r) return r; }
    return inferQuantVarType(varName, body.fn, ctx);
  }
  if (body.kind === "field") return inferQuantVarType(varName, body.obj, ctx);
  if (body.kind === "index") {
    return inferQuantVarType(varName, body.obj, ctx) ?? inferQuantVarType(varName, body.idx, ctx);
  }
  if (body.kind === "conditional") {
    return inferQuantVarType(varName, body.cond, ctx) ??
      inferQuantVarType(varName, body.then, ctx) ?? inferQuantVarType(varName, body.else, ctx);
  }
  if ((body.kind === "forall" || body.kind === "exists") && body.var !== varName) {
    return inferQuantVarType(varName, body.body, ctx);
  }
  if (body.kind === "arrayLiteral") {
    for (const el of body.elems) { const r = inferQuantVarType(varName, el, ctx); if (r) return r; }
  }
  if (body.kind === "record") {
    if (body.spread) { const r = inferQuantVarType(varName, body.spread, ctx); if (r) return r; }
    for (const f of body.fields) { const r = inferQuantVarType(varName, f.value, ctx); if (r) return r; }
  }
  return null;
}

function classifyCall(fn: RawExpr, ctx: Ctx): CallKind {
  if (fn.kind === "field" && fn.obj.kind === "var" && fn.obj.name === "Math") return "pure";
  if (fn.kind === "var" && (ctx.inSpec || ctx.inLambda) && ctx.pureFns.has(fn.name)) return "spec-pure";
  if (fn.kind === "var" && ctx.inSpec) {
    // Not a known pure function — could be external (Lean-defined spec helper).
    // Pass through as "pure" and let Lean catch any errors.
    return "pure";
  }
  if (fn.kind === "var") return "method";
  return "unknown";
}

// ── Resolve expressions ──────────────────────────────────────

function resolveExpr(e: RawExpr, ctx: Ctx): TExpr {
  switch (e.kind) {
    case "var":
      return { kind: "var", name: e.name, ty: lookup(ctx.env, e.name) ?? { kind: "unknown" } };

    case "num":
      return { kind: "num", value: e.value, ty: e.value >= 0 ? { kind: "nat" } : { kind: "int" } };

    case "str":
      return { kind: "str", value: e.value, ty: { kind: "string" } };

    case "bool":
      return { kind: "bool", value: e.value, ty: { kind: "bool" } };

    case "binop": {
      let left = resolveExpr(e.left, ctx);
      let right = resolveExpr(e.right, ctx);
      if (e.op === "===" || e.op === "!==") {
        left = coerceStr(left, right.ty);
        right = coerceStr(right, left.ty);
      }
      let ty: Ty = { kind: "unknown" };
      if (["===", "!==", ">=", "<=", ">", "<", "&&", "||"].includes(e.op)) ty = { kind: "bool" };
      else if (["+", "-", "*", "/", "%"].includes(e.op)) ty = left.ty;
      return { kind: "binop", op: e.op, left, right, ty };
    }

    case "unop": {
      const expr = resolveExpr(e.expr, ctx);
      return { kind: "unop", op: e.op, expr, ty: e.op === "!" ? { kind: "bool" } : expr.ty };
    }

    case "call": {
      const fn = resolveExpr(e.fn, ctx);
      const args = e.args.map(a => resolveExpr(a, ctx));
      let ty: Ty = { kind: "unknown" };
      // Infer return types for collection methods
      if (fn.kind === "field" && fn.obj.ty.kind === "map") {
        if (fn.field === "get") ty = ctx.inSpec ? fn.obj.ty.value : { kind: "optional", inner: fn.obj.ty.value };
        else if (fn.field === "has") ty = { kind: "bool" };
        else if (fn.field === "set") ty = fn.obj.ty;
      } else if (fn.kind === "field" && fn.obj.ty.kind === "set") {
        if (fn.field === "has") ty = { kind: "bool" };
        else if (fn.field === "add") ty = fn.obj.ty;
      } else if (fn.kind === "field" && fn.obj.ty.kind === "array") {
        if (fn.field === "includes") ty = { kind: "bool" };
      }
      return { kind: "call", fn, args, ty, callKind: classifyCall(e.fn, ctx) };
    }

    case "index": {
      const obj = resolveExpr(e.obj, ctx);
      const idx = resolveExpr(e.idx, ctx);
      return { kind: "index", obj, idx, ty: obj.ty.kind === "array" ? obj.ty.elem : { kind: "unknown" } };
    }

    case "field": {
      const obj = resolveExpr(e.obj, ctx);
      let isDiscriminant = false;
      let ty: Ty = { kind: "unknown" };

      if (e.field === "length" && (obj.ty.kind === "array" || obj.ty.kind === "string")) {
        ty = { kind: "nat" };
      } else if (e.field === "size" && (obj.ty.kind === "map" || obj.ty.kind === "set")) {
        ty = { kind: "nat" };
      } else if (obj.ty.kind === "user") {
        if (getDiscriminant(ctx, obj.ty.name) === e.field) isDiscriminant = true;
        const decl = findDecl(ctx, obj.ty.name);
        if (decl?.kind === "record") {
          const f = decl.fields?.find(f => f.name === e.field);
          if (f) ty = resolveTsType(f.tsType, ctx.overrides);
        }
      }

      return { kind: "field", obj, field: e.field, ty, isDiscriminant };
    }

    case "record": {
      const spread = e.spread ? resolveExpr(e.spread, ctx) : null;
      const ty = spread ? spread.ty : { kind: "unknown" as const };
      // Infer record type: from spread, or from return type context
      const recordTy = ty.kind === "user" ? ty : ctx.returnTy.kind === "user" ? ctx.returnTy : null;
      const decl = recordTy ? ctx.typeDecls.find(d => d.name === recordTy.name && d.kind === "record") : undefined;
      const fields = e.fields.map(f => {
        let value = resolveExpr(f.value, ctx);
        const fieldDecl = decl?.fields?.find(df => df.name === f.name);
        if (fieldDecl) value = coerceStr(value, parseTsType(fieldDecl.tsType));
        return { name: f.name, value };
      });
      return { kind: "record", spread, fields, ty: recordTy ?? ty };
    }

    case "result":
      if (!ctx.allowResult) throw new Error("\\result is only valid in ensures");
      return { kind: "result", ty: ctx.returnTy };

    case "forall": {
      const varTy: Ty = e.varType === "nat" ? { kind: "nat" }
        : inferQuantVarType(e.var, e.body, ctx) ?? { kind: "int" };
      return { kind: "forall", var: e.var, varTy, body: resolveExpr(e.body, withEnv(ctx, extend(ctx.env, e.var, varTy))), ty: { kind: "bool" } };
    }

    case "exists": {
      const varTy: Ty = e.varType === "nat" ? { kind: "nat" }
        : inferQuantVarType(e.var, e.body, ctx) ?? { kind: "int" };
      return { kind: "exists", var: e.var, varTy, body: resolveExpr(e.body, withEnv(ctx, extend(ctx.env, e.var, varTy))), ty: { kind: "bool" } };
    }

    case "arrayLiteral": {
      const elems = e.elems.map(el => resolveExpr(el, ctx));
      const elemTy: Ty = elems.length > 0 ? elems[0].ty : { kind: "unknown" };
      return { kind: "arrayLiteral", elems, ty: { kind: "array", elem: elemTy } };
    }

    case "lambda": {
      // Resolve lambda params — types from explicit annotation or unknown
      const params = e.params.map(p => ({
        name: p.name,
        ty: p.tsType ? parseTsType(p.tsType) : { kind: "unknown" as const },
      }));
      // Extend env with lambda params
      let lambdaEnv = ctx.env;
      for (const p of params) lambdaEnv = extend(lambdaEnv, p.name, p.ty);
      const lambdaCtx = { ...withEnv(ctx, lambdaEnv), inLambda: true };
      // Body: expression (wrap in return stmt) or statement block
      const body = Array.isArray(e.body)
        ? resolveBlock(e.body, lambdaCtx)
        : [{ kind: "return" as const, value: resolveExpr(e.body, lambdaCtx) }];
      return { kind: "lambda", params, body, ty: { kind: "unknown" } };
    }

    case "conditional": {
      const cond = resolveExpr(e.cond, ctx);
      let then_ = resolveExpr(e.then, ctx);
      let else_ = resolveExpr(e.else, ctx);
      then_ = coerceStr(then_, else_.ty);
      else_ = coerceStr(else_, then_.ty);
      const ty = then_.ty.kind !== "unknown" ? then_.ty : else_.ty;
      return { kind: "conditional", cond, then: then_, else: else_, ty };
    }

    case "emptyCollection": {
      const ty = parseTsType(e.tsType);
      return { kind: "arrayLiteral", elems: [], ty };
    }
  }
}

// ── Resolve specs ────────────────────────────────────────────

function resolveSpec(spec: string, ctx: Ctx): TExpr {
  return resolveExpr(parseExpr(spec), ctx);
}

function resolveSpecs(specs: string[], ctx: Ctx): TExpr[] {
  const result: TExpr[] = [];
  for (const spec of specs) {
    for (const clause of splitConj(parseExpr(spec))) {
      result.push(resolveExpr(clause, ctx));
    }
  }
  return result;
}

function splitConj(e: RawExpr): RawExpr[] {
  if (e.kind === "binop" && e.op === "&&") return [...splitConj(e.left), ...splitConj(e.right)];
  return [e];
}

// ── Resolve statements ───────────────────────────────────────

function resolveBlock(stmts: RawStmt[], ctx: Ctx): TStmt[] {
  const result: TStmt[] = [];
  let env = ctx.env;
  for (const s of stmts) {
    const [typed, nextEnv] = resolveStmt(s, withEnv(ctx, env));
    result.push(typed);
    env = nextEnv;
  }
  return result;
}

function resolveStmt(s: RawStmt, ctx: Ctx): [TStmt, Env | null] {
  switch (s.kind) {
    case "let": {
      const ty = resolveTsType(s.tsType, ctx.overrides, s.name);
      const init = coerceStr(resolveExpr(s.init, ctx), ty);
      // const collections are mutable in value-semantics world (TS mutates in place, Dafny/Lean reassign)
      const mutable = s.mutable || isRefMutableInTS(ty);
      return [{ kind: "let", name: s.name, ty, mutable, init }, extend(ctx.env, s.name, ty)];
    }

    case "assign": {
      const targetTy = lookup(ctx.env, s.target) ?? { kind: "unknown" as const };
      return [{ kind: "assign", target: s.target, value: coerceStr(resolveExpr(s.value, ctx), targetTy) }, ctx.env];
    }

    case "return":
      return [{ kind: "return", value: coerceStr(resolveExpr(s.value, ctx), ctx.returnTy) }, ctx.env];

    case "break":
      return [{ kind: "break" }, ctx.env];

    case "continue":
      return [{ kind: "continue" }, ctx.env];

    case "expr":
      return [{ kind: "expr", expr: resolveExpr(s.expr, ctx) }, ctx.env];

    case "if": {
      // Narrow optional<T> → T when checking !== undefined or undefined !==
      let thenCtx = ctx, elseCtx = ctx;
      const narrowed = narrowOptional(s.cond, ctx.env);
      if (narrowed) {
        const env = extend(ctx.env, narrowed.varName, narrowed.innerTy);
        if (narrowed.inThen) thenCtx = withEnv(ctx, env);
        else elseCtx = withEnv(ctx, env);
      }
      return [{ kind: "if", cond: resolveExpr(s.cond, ctx), then: resolveBlock(s.then, thenCtx), else: resolveBlock(s.else, elseCtx) }, ctx.env];
    }

    case "while": {
      const whileSpecCtx = { ...ctx, inSpec: true };
      return [{
        kind: "while",
        cond: resolveExpr(s.cond, ctx),
        invariants: resolveSpecs(s.invariants, whileSpecCtx),
        decreases: s.decreases ? resolveSpec(s.decreases, whileSpecCtx) : null,
        doneWith: s.doneWith ? resolveSpec(s.doneWith, whileSpecCtx) : null,
        body: resolveBlock(s.body, ctx),
      }, ctx.env];
    }

    case "forof": {
      const iterable = resolveExpr(s.iterable, ctx);
      const elemTy: Ty = iterable.ty.kind === "array" ? iterable.ty.elem
        : iterable.ty.kind === "set" ? iterable.ty.elem
        : { kind: "unknown" };
      const idxName = `_${s.varName}_idx`;
      const withIdx = extend(ctx.env, idxName, { kind: "nat" });
      const withElem = extend(withIdx, s.varName, elemTy);
      const bodyCtx = withEnv(ctx, withElem);
      return [{
        kind: "forof", varName: s.varName, varTy: elemTy, iterable,
        invariants: resolveSpecs(s.invariants, { ...bodyCtx, inSpec: true }),
        doneWith: s.doneWith ? resolveSpec(s.doneWith, { ...bodyCtx, inSpec: true }) : null,
        body: resolveBlock(s.body, bodyCtx),
      }, ctx.env];
    }

    case "switch":
      return [{
        kind: "switch", expr: resolveExpr(s.expr, ctx), discriminant: s.discriminant,
        cases: s.cases.map(c => ({ label: c.label, body: resolveBlock(c.body, ctx) })),
        defaultBody: resolveBlock(s.defaultBody, ctx),
      }, ctx.env];

    case "ghostLet": {
      const specCtx = { ...ctx, inSpec: true };
      // Handle new Set<T>() / new Map<K,V>() constructors
      const collMatch = s.init.match(/^new\s+(Set|Map)<(.+)>\(\)$/);
      const init = collMatch
        ? resolveExpr({ kind: "emptyCollection", collectionType: collMatch[1] as "Set" | "Map", tsType: `${collMatch[1]}<${collMatch[2]}>` }, specCtx)
        : resolveExpr(parseExpr(s.init), specCtx);
      const ty = s.tsType ? parseTsType(s.tsType) : init.ty;
      return [{ kind: "ghostLet", name: s.name, ty, init }, extend(ctx.env, s.name, ty)];
    }

    case "ghostAssign": {
      const specCtx = { ...ctx, inSpec: true };
      const value = resolveExpr(parseExpr(s.value), specCtx);
      return [{ kind: "ghostAssign", target: s.target, value }, ctx.env];
    }

    case "assert": {
      const specCtx = { ...ctx, inSpec: true };
      const expr = resolveExpr(parseExpr(s.expr), specCtx);
      return [{ kind: "assert", expr }, ctx.env];
    }
  }
}

// ── Pure / return-in-loop detection ──────────────────────────

/** Syntactic purity: no while, no for-of, no mutable let. */
function isSyntacticallyPure(stmts: RawStmt[]): boolean {
  for (const s of stmts) {
    switch (s.kind) {
      case "while": case "forof": return false;
      case "let": if (s.mutable) return false; break;
      case "if": if (!isSyntacticallyPure(s.then) || !isSyntacticallyPure(s.else)) return false; break;
      case "switch": if (!s.cases.every(c => isSyntacticallyPure(c.body)) || !isSyntacticallyPure(s.defaultBody)) return false; break;
    }
  }
  return true;
}

// ── Call graph ──────────────────────────────────────────────

/** Collect all same-file function calls from expressions (including inside lambdas). */
function collectCallsExpr(e: RawExpr, fns: Set<string>, out: Set<string>): void {
  switch (e.kind) {
    case "call":
      if (e.fn.kind === "var" && fns.has(e.fn.name)) out.add(e.fn.name);
      collectCallsExpr(e.fn, fns, out);
      for (const a of e.args) collectCallsExpr(a, fns, out);
      return;
    case "binop": collectCallsExpr(e.left, fns, out); collectCallsExpr(e.right, fns, out); return;
    case "unop": collectCallsExpr(e.expr, fns, out); return;
    case "field": collectCallsExpr(e.obj, fns, out); return;
    case "index": collectCallsExpr(e.obj, fns, out); collectCallsExpr(e.idx, fns, out); return;
    case "record":
      if (e.spread) collectCallsExpr(e.spread, fns, out);
      for (const f of e.fields) collectCallsExpr(f.value, fns, out);
      return;
    case "arrayLiteral": for (const el of e.elems) collectCallsExpr(el, fns, out); return;
    case "lambda":
      if (Array.isArray(e.body)) collectCallsStmts(e.body, fns, out);
      else collectCallsExpr(e.body, fns, out);
      return;
    case "forall": case "exists": collectCallsExpr(e.body, fns, out); return;
    case "conditional":
      collectCallsExpr(e.cond, fns, out);
      collectCallsExpr(e.then, fns, out);
      collectCallsExpr(e.else, fns, out);
      return;
  }
}

function collectCallsStmts(stmts: RawStmt[], fns: Set<string>, out: Set<string>): void {
  for (const s of stmts) {
    switch (s.kind) {
      case "let": collectCallsExpr(s.init, fns, out); break;
      case "assign": collectCallsExpr(s.value, fns, out); break;
      case "return": collectCallsExpr(s.value, fns, out); break;
      case "expr": collectCallsExpr(s.expr, fns, out); break;
      case "if":
        collectCallsExpr(s.cond, fns, out);
        collectCallsStmts(s.then, fns, out);
        collectCallsStmts(s.else, fns, out);
        break;
      case "while":
        collectCallsExpr(s.cond, fns, out);
        collectCallsStmts(s.body, fns, out);
        break;
      case "forof":
        collectCallsExpr(s.iterable, fns, out);
        collectCallsStmts(s.body, fns, out);
        break;
      case "switch":
        collectCallsExpr(s.expr, fns, out);
        for (const c of s.cases) collectCallsStmts(c.body, fns, out);
        collectCallsStmts(s.defaultBody, fns, out);
        break;
    }
  }
}

function computePureFns(functions: RawFunction[]): Set<string> {
  const allFnNames = new Set(functions.map(fn => fn.name));

  // Build call graph: fn → set of same-file functions it calls
  const callGraph = new Map<string, Set<string>>();
  for (const fn of functions) {
    const calls = new Set<string>();
    collectCallsStmts(fn.body, allFnNames, calls);
    callGraph.set(fn.name, calls);
  }

  // Seed: syntactically non-pure functions
  const nonPure = new Set(
    functions.filter(fn => !isSyntacticallyPure(fn.body)).map(fn => fn.name)
  );

  // Build reverse graph: fn → set of functions that call it
  const callers = new Map<string, Set<string>>();
  for (const name of allFnNames) callers.set(name, new Set());
  for (const [caller, callees] of callGraph) {
    for (const callee of callees) callers.get(callee)!.add(caller);
  }

  // Propagate impurity through reverse call graph
  const worklist = [...nonPure];
  while (worklist.length > 0) {
    const fn = worklist.pop()!;
    for (const caller of callers.get(fn) ?? []) {
      if (!nonPure.has(caller)) {
        nonPure.add(caller);
        worklist.push(caller);
      }
    }
  }

  return new Set(functions.map(fn => fn.name).filter(name => !nonPure.has(name)));
}

function hasReturnInLoop(stmts: RawStmt[]): boolean {
  for (const s of stmts) {
    if ((s.kind === "while" || s.kind === "forof") && containsReturn(s.body)) return true;
    if (s.kind === "if" && (hasReturnInLoop(s.then) || hasReturnInLoop(s.else))) return true;
    if (s.kind === "switch" && (s.cases.some(c => hasReturnInLoop(c.body)) || hasReturnInLoop(s.defaultBody))) return true;
  }
  return false;
}

function containsReturn(stmts: RawStmt[]): boolean {
  for (const s of stmts) {
    if (s.kind === "return") return true;
    if (s.kind === "if" && (containsReturn(s.then) || containsReturn(s.else))) return true;
    if ((s.kind === "while" || s.kind === "forof") && containsReturn(s.body)) return true;
    if (s.kind === "switch" && (s.cases.some(c => containsReturn(c.body)) || containsReturn(s.defaultBody))) return true;
  }
  return false;
}

// ── Resolve function / module ────────────────────────────────

function resolveFunction(fn: RawFunction, typeDecls: TypeDeclInfo[], pureFns: Set<string>): TFunction {
  if (hasReturnInLoop(fn.body)) {
    throw new Error(`${fn.name}: return inside a loop is not supported.`);
  }

  const overrides = new Map(fn.typeAnnotations.map(a => [a.name, a.type]));
  const params: TParam[] = fn.params.map(p => ({ name: p.name, ty: resolveTsType(p.tsType, overrides, p.name) }));
  const returnTy = resolveTsType(fn.returnType, overrides, "\\result");

  let env: Env | null = null;
  for (const p of params) env = extend(env, p.name, p.ty);

  const baseCtx: Ctx = { env, typeDecls, overrides, allowResult: false, returnTy, pureFns, inSpec: false, inLambda: false };
  const requiresCtx: Ctx = { ...baseCtx, inSpec: true };
  const ensuresCtx: Ctx = { ...baseCtx, allowResult: true, inSpec: true };

  return {
    name: fn.name, params, returnTy,
    requires: resolveSpecs(fn.requires, requiresCtx),
    ensures: resolveSpecs(fn.ensures, ensuresCtx),
    isPure: pureFns.has(fn.name),
    body: resolveBlock(fn.body, baseCtx),
  };
}

export function resolveModule(raw: RawModule): TModule {
  const pureFns = computePureFns(raw.functions);
  return {
    file: raw.file,
    typeDecls: raw.typeDecls,
    functions: raw.functions.map(fn => resolveFunction(fn, raw.typeDecls, pureFns)),
  };
}
