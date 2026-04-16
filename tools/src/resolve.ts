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

// ── Raw expression substitution ─────────────────────────────

let _synVarCounter = 0;

/**
 * Structural equality for raw field-access chains (var and field nodes only).
 * Exact within a single expression scope — raw IR has no bindings that could
 * cause name collisions (those are introduced by resolve, which runs after).
 */
function rawExprEquals(a: RawExpr, b: RawExpr): boolean {
  if (a.kind === "var" && b.kind === "var") return a.name === b.name;
  if (a.kind === "field" && b.kind === "field") return a.field === b.field && rawExprEquals(a.obj, b.obj);
  if (a.kind === "call" && b.kind === "call") return rawExprEquals(a.fn, b.fn) && a.args.length === b.args.length && a.args.every((arg, i) => rawExprEquals(arg, b.args[i]));
  if (a.kind === "index" && b.kind === "index") return rawExprEquals(a.obj, b.obj) && rawExprEquals(a.idx, b.idx);
  return false;
}

/** Return the root variable name of a field-access chain, or null. */
function rawChainRoot(e: RawExpr): string | null {
  if (e.kind === "var") return e.name;
  if (e.kind === "field") return rawChainRoot(e.obj);
  return null;
}

/**
 * Replace all occurrences of `target` in `expr` with `replacement`.
 * Only matches field-access chains (see rawExprEquals). Stops at lambda
 * boundaries that shadow the chain's root variable.
 */
function substituteRawExpr(expr: RawExpr, target: RawExpr, replacement: RawExpr): RawExpr {
  if (rawExprEquals(expr, target)) return replacement;
  const root = rawChainRoot(target);
  const sub = (e: RawExpr) => substituteRawExpr(e, target, replacement);
  switch (expr.kind) {
    case "var": case "num": case "str": case "bool": case "result":
    case "havoc": case "emptyCollection":
      return expr;
    case "binop":  return { ...expr, left: sub(expr.left), right: sub(expr.right) };
    case "unop":   return { ...expr, expr: sub(expr.expr) };
    case "call":   return { ...expr, fn: sub(expr.fn), args: expr.args.map(sub) };
    case "field":  return { ...expr, obj: sub(expr.obj) };
    case "index":  return { ...expr, obj: sub(expr.obj), idx: sub(expr.idx) };
    case "record":
      return { ...expr, spread: expr.spread ? sub(expr.spread) : null,
        fields: expr.fields.map(f => ({ ...f, value: sub(f.value) })) };
    case "arrayLiteral": return { ...expr, elems: expr.elems.map(sub) };
    case "conditional":  return { ...expr, cond: sub(expr.cond), then: sub(expr.then), else: sub(expr.else) };
    case "nonNull":      return { ...expr, expr: sub(expr.expr) };
    case "forall": case "exists":
      return { ...expr, body: sub(expr.body) };
    case "lambda":
      // Don't cross lambda boundaries that shadow the chain's root variable
      if (root && expr.params.some(p => p.name === root)) return expr;
      return { ...expr, body: Array.isArray(expr.body) ? expr.body : sub(expr.body) };
  }
}

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

interface NarrowedField {
  objName: string;
  fieldName: string;
  narrowedTy: Ty;
}

interface Ctx {
  env: Env | null;
  typeDecls: TypeDeclInfo[];
  overrides: Map<string, string>;
  allowResult: boolean;
  returnTy: Ty;
  pureFns: Set<string>;  // names of pure functions in this module
  fnParams: Map<string, Ty[]>;  // function name → parameter types
  fnReturns: Map<string, Ty>;  // function name → return type
  inSpec: boolean;
  inLambda: boolean;
  narrowedFields: NarrowedField[];  // field chain narrowing context for conditional then-branches
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

/** Wrap a resolved expression in Some() for optional coercion. */
function wrapSome(value: TExpr, optionalTy: Ty): TExpr {
  return {
    kind: "call", fn: { kind: "var", name: "Some", ty: optionalTy },
    args: [value], ty: optionalTy, callKind: "pure",
  };
}

/** Detect `v !== undefined` or `undefined !== v` where v: optional<T>.
 *  Handles simple variables, field access chains, and arbitrary expressions.
 *  When `fieldExpr` is returned for a simple field chain (obj.field), callers
 *  can narrow via `narrowedFields` context. For complex expressions (calls, etc.),
 *  callers should fall back to `substituteRawExpr`.
 *
 *  Does NOT recurse into `&&` — callers that need to detect optional checks
 *  inside `&&` conditions should check `cond.left` explicitly. */
function detectOptionalCheck(cond: RawExpr, ctx: Ctx): {
  varName: string; innerTy: Ty; inThen: boolean;
  fieldExpr?: RawExpr;       // set for field chains and complex expressions — needs substitution
  narrowedExpr?: TExpr;      // resolved optional expression — set for non-variable checks
} | null {
  if (cond.kind !== "binop" || (cond.op !== "!==" && cond.op !== "===")) return null;
  // Identify the expression being checked against undefined
  let optExpr: RawExpr | null = null;
  if (cond.right.kind === "var" && cond.right.name === "undefined") optExpr = cond.left;
  if (cond.left.kind === "var" && cond.left.name === "undefined") optExpr = cond.right;
  if (!optExpr) return null;

  // Simple variable — env lookup, no substitution needed
  if (optExpr.kind === "var") {
    const ty = lookup(ctx.env, optExpr.name);
    if (!ty || ty.kind !== "optional") return null;
    return { varName: optExpr.name, innerTy: ty.inner, inThen: cond.op === "!==" };
  }

  // Field access chain or arbitrary expression — resolve to check type, needs substitution
  const resolved = resolveExpr(optExpr, ctx);
  if (resolved.ty.kind === "optional") {
    const synVar = optExpr.kind === "field" ? `_narr${_synVarCounter++}` : `_opt${_synVarCounter++}`;
    return {
      varName: synVar, innerTy: resolved.ty.inner, inThen: cond.op === "!==",
      fieldExpr: optExpr, narrowedExpr: resolved,
    };
  }

  return null;
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

// ── Call resolution helpers ─────────────────────────────────

/** Infer lambda param types from array method context (map, filter, etc.).
 *  Returns updated rawArgs with inferred tsType on the first lambda param. */
function inferLambdaParamTypes(fn: TExpr, rawArgs: RawExpr[]): RawExpr[] {
  if (fn.kind === "field" && fn.obj.ty.kind === "array" &&
      ["map", "filter", "every", "some", "find"].includes(fn.field) &&
      rawArgs.length >= 1 && rawArgs[0].kind === "lambda" &&
      rawArgs[0].params.length >= 1 && !rawArgs[0].params[0].tsType) {
    const elemTy = fn.obj.ty.elem;
    const tsType = elemTy.kind === "user" ? elemTy.name
      : elemTy.kind === "string" ? "string"
      : elemTy.kind === "int" || elemTy.kind === "nat" ? "number"
      : elemTy.kind === "bool" ? "boolean" : undefined;
    if (tsType) {
      const lam = rawArgs[0];
      const updatedParams = [{ ...lam.params[0], tsType }, ...lam.params.slice(1)];
      return [{ ...lam, params: updatedParams }, ...rawArgs.slice(1)];
    }
  }
  return rawArgs;
}

/** Coerce call arguments: string literals → user types, non-optional → Some, pad missing optional args. */
function coerceCallArgs(args: TExpr[], fn: TExpr, ctx: Ctx): TExpr[] {
  if (fn.kind !== "var" || !ctx.fnParams.has(fn.name)) return args;
  const paramTys = ctx.fnParams.get(fn.name)!;
  args = args.map((a, i) => {
    if (i >= paramTys.length) return a;
    a = coerceStr(a, paramTys[i]);
    if (a.ty.kind !== "optional" && paramTys[i].kind === "optional") {
      return wrapSome(a, paramTys[i]);
    }
    return a;
  });
  // Pad missing optional args with None
  for (let i = args.length; i < paramTys.length; i++) {
    if (paramTys[i].kind === "optional") {
      args.push({ kind: "var" as const, name: "undefined", ty: paramTys[i] });
    }
  }
  return args;
}

/** Infer return type for collection/string method calls. */
function inferMethodReturnTy(fn: TExpr, args: TExpr[], ctx: Ctx): Ty {
  if (fn.kind !== "field") return { kind: "unknown" };
  const objTy = fn.obj.ty;
  if (objTy.kind === "map") {
    if (fn.field === "get") return ctx.inSpec ? objTy.value : { kind: "optional", inner: objTy.value };
    if (fn.field === "has") return { kind: "bool" };
    if (fn.field === "set" || fn.field === "delete") return objTy;
  } else if (objTy.kind === "set") {
    if (fn.field === "has") return { kind: "bool" };
    if (fn.field === "add" || fn.field === "delete") return objTy;
  } else if (objTy.kind === "array") {
    if (fn.field === "includes") return { kind: "bool" };
    if (fn.field === "indexOf") return { kind: "int" };
    if (fn.field === "shift") return objTy.elem;
    if (fn.field === "push" || fn.field === "concat") return objTy;
    if (fn.field === "filter") return objTy;
    if (fn.field === "every" || fn.field === "some") return { kind: "bool" };
    if (fn.field === "map" && args.length >= 1 && args[0].kind === "lambda") {
      const retTy = args[0].body.length > 0 && args[0].body[0].kind === "return"
        ? args[0].body[0].value.ty : { kind: "unknown" as const };
      return { kind: "array", elem: retTy };
    }
  } else if (objTy.kind === "string") {
    if (fn.field === "trim" || fn.field === "toLowerCase" || fn.field === "toUpperCase") return { kind: "string" };
    if (fn.field === "includes") return { kind: "bool" };
  }
  return { kind: "unknown" };
}

// ── Resolve expressions ──────────────────────────────────────

function resolveExpr(e: RawExpr, ctx: Ctx): TExpr {
  switch (e.kind) {
    case "var":
      if (e.name === "undefined") return { kind: "var", name: "undefined", ty: { kind: "void" } };
      return { kind: "var", name: e.name, ty: lookup(ctx.env, e.name) ?? { kind: "unknown" } };

    case "num":
      if (!Number.isInteger(e.value)) return { kind: "num", value: e.value, ty: { kind: "real" } };
      return { kind: "num", value: e.value, ty: e.value >= 0 ? { kind: "nat" } : { kind: "int" } };

    case "str":
      return { kind: "str", value: e.value, ty: { kind: "string" } };

    case "bool":
      return { kind: "bool", value: e.value, ty: { kind: "bool" } };

    case "nonNull": {
      const expr = resolveExpr(e.expr, ctx);
      // Unwrap optional type; for map.get()!, force to direct access type
      if (expr.kind === "call" && expr.fn.kind === "field" &&
          expr.fn.obj.ty.kind === "map" && expr.fn.field === "get") {
        return { ...expr, ty: expr.fn.obj.ty.value };
      }
      const ty = expr.ty.kind === "optional" ? expr.ty.inner : expr.ty;
      return { ...expr, ty };
    }

    case "binop": {
      let left = resolveExpr(e.left, ctx);
      // && narrowing: if left is "x !== undefined", narrow x for right side.
      // Field chains are excluded — resolve can't substitute in sub-expressions;
      // transform's emitOptionalMatch handles field chains in statement contexts.
      let rightCtx = ctx;
      let rawRight = e.right;
      if (e.op === "&&") {
        const narrowed = detectOptionalCheck(e.left, ctx);
        if (narrowed && narrowed.inThen && !narrowed.fieldExpr) {
          rightCtx = withEnv(ctx, extend(ctx.env, narrowed.varName, narrowed.innerTy));
        }
      }
      let right = resolveExpr(rawRight, rightCtx);
      if (e.op === "===" || e.op === "!==") {
        left = coerceStr(left, right.ty);
        right = coerceStr(right, left.ty);
      }
      let ty: Ty = { kind: "unknown" };
      if (["===", "!==", ">=", "<=", ">", "<", "in"].includes(e.op)) ty = { kind: "bool" };
      else if (e.op === "&&") ty = right.ty;
      else if (e.op === "||" && left.ty.kind === "optional") {
        // || undefined is identity for optionals — keep the optional type
        ty = (e.right.kind === "var" && e.right.name === "undefined") ? left.ty : left.ty.inner;
      }
      else if (e.op === "||") ty = right.ty;
      else if (["+", "-", "*", "/", "%"].includes(e.op)) {
        ty = (left.ty.kind === "real" || right.ty.kind === "real") ? { kind: "real" } : left.ty;
      }
      return { kind: "binop", op: e.op, left, right, ty };
    }

    case "unop": {
      const expr = resolveExpr(e.expr, ctx);
      return { kind: "unop", op: e.op, expr, ty: e.op === "!" ? { kind: "bool" } : expr.ty };
    }

    case "call": {
      const fn = resolveExpr(e.fn, ctx);
      const rawArgs = inferLambdaParamTypes(fn, e.args);
      // For .push() on a typed array, resolve args with element type context
      let argCtx = ctx;
      if (fn.kind === "field" && fn.obj.ty.kind === "array" && fn.field === "push" &&
          fn.obj.ty.elem.kind === "user") {
        argCtx = { ...ctx, returnTy: fn.obj.ty.elem };
      }
      const args = coerceCallArgs(rawArgs.map(a => resolveExpr(a, argCtx)), fn, ctx);
      let ty = inferMethodReturnTy(fn, args, ctx);
      // For same-file function calls, use the known return type
      if (ty.kind === "unknown" && fn.kind === "var" && ctx.fnReturns.has(fn.name)) {
        ty = ctx.fnReturns.get(fn.name)!;
      }
      return { kind: "call", fn, args, ty, callKind: classifyCall(e.fn, ctx) };
    }

    case "index": {
      const obj = resolveExpr(e.obj, ctx);
      const idx = resolveExpr(e.idx, ctx);
      const idxTy = obj.ty.kind === "array" ? obj.ty.elem
        : obj.ty.kind === "map" ? { kind: "optional" as const, inner: obj.ty.value }
        : { kind: "unknown" as const };
      return { kind: "index", obj, idx, ty: idxTy };
    }

    case "field": {
      const obj = resolveExpr(e.obj, ctx);
      let isDiscriminant = false;
      let ty: Ty = { kind: "unknown" };

      // Check narrowed field context (from conditional optional checks on field chains)
      if (obj.kind === "var" && ctx.narrowedFields.length > 0) {
        const nf = ctx.narrowedFields.find(n => n.objName === obj.name && n.fieldName === e.field);
        if (nf) ty = nf.narrowedTy;
      }

      if (ty.kind === "unknown" && e.field === "length" && (obj.ty.kind === "array" || obj.ty.kind === "string")) {
        ty = { kind: "nat" };
      } else if (ty.kind === "unknown" && e.field === "size" && (obj.ty.kind === "map" || obj.ty.kind === "set")) {
        ty = { kind: "nat" };
      } else if (ty.kind === "unknown" && obj.ty.kind === "user") {
        if (getDiscriminant(ctx, obj.ty.name) === e.field) isDiscriminant = true;
        const decl = findDecl(ctx, obj.ty.name);
        if (decl?.kind === "record") {
          const f = decl.fields?.find(f => f.name === e.field);
          if (f) ty = f.type!;
        }
        // Also resolve fields from discriminated-union variants
        if (ty.kind === "unknown" && decl?.kind === "discriminated-union" && decl.variants) {
          for (const variant of decl.variants) {
            const f = variant.fields.find(f => f.name === e.field);
            if (f) { ty = f.type!; break; }
          }
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
      // Clear returnTy for field values — it applies to THIS record, not nested ones
      const fieldCtx = recordTy ? { ...ctx, returnTy: { kind: "unknown" as const } as Ty } : ctx;
      const fields = e.fields.map(f => {
        const fieldDecl = decl?.fields?.find(df => df.name === f.name);
        // Propagate declared field type into context so nested records resolve
        // their union variant correctly (e.g., { kind: 'Idle' } → EffectMode.Idle)
        const valueCtx = (fieldDecl?.type?.kind === "user")
          ? { ...fieldCtx, returnTy: fieldDecl.type }
          : fieldCtx;
        let value = resolveExpr(f.value, valueCtx);
        if (fieldDecl) {
          const declTy = fieldDecl.type!;
          value = coerceStr(value, declTy);
          // Empty {} for map-typed fields → empty map (arrayLiteral with map type → emptyMap in transform)
          if (value.kind === "record" && value.fields.length === 0 && !value.spread && declTy.kind === "map") {
            value = { kind: "arrayLiteral", elems: [], ty: declTy };
          }
          // Coerce non-optional to optional: wrap in Some (only when value type is concrete)
          if (declTy.kind === "optional" && value.ty.kind !== "optional" && value.ty.kind !== "void" && value.ty.kind !== "unknown") {
            value = wrapSome(value, declTy);
          }
        }
        return { name: f.name, value };
      });
      return { kind: "record", spread, fields, ty: recordTy ?? ty };
    }

    case "result":
      if (!ctx.allowResult) throw new Error("\\result is only valid in ensures");
      return { kind: "result", ty: ctx.returnTy };

    case "forall": {
      const varTy: Ty = e.varType !== "int" ? parseTsType(e.varType)
        : inferQuantVarType(e.var, e.body, ctx) ?? { kind: "int" };
      return { kind: "forall", var: e.var, varTy, body: resolveExpr(e.body, withEnv(ctx, extend(ctx.env, e.var, varTy))), ty: { kind: "bool" } };
    }

    case "exists": {
      const varTy: Ty = e.varType !== "int" ? parseTsType(e.varType)
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

      let narrowedVar: string | undefined;
      let thenCtx = ctx;
      let rawThen = e.then;

      // Phase 1: Optional truthiness — cond itself is optional (e.g. opt ? X : Y)
      if (cond.ty.kind === "optional") {
        const innerTy = cond.ty.inner;
        if (e.cond.kind === "var") {
          narrowedVar = e.cond.name;
          thenCtx = withEnv(ctx, extend(ctx.env, e.cond.name, innerTy));
        } else {
          narrowedVar = `_opt${_synVarCounter++}`;
          rawThen = substituteRawExpr(e.then, e.cond, { kind: "var", name: narrowedVar });
          thenCtx = withEnv(ctx, extend(ctx.env, narrowedVar, innerTy));
        }
      }

      // Phase 2/3: Explicit check — v !== undefined, or && with optional check.
      // Resolve only narrows the type environment; transform handles all structural
      // narrowing (match generation, variable binding, && splitting).
      let narrowedExprResolved: TExpr | undefined;
      if (!narrowedVar) {
        const narrowed = detectOptionalCheck(e.cond, ctx)
          ?? (e.cond.kind === "binop" && e.cond.op === "&&" ? detectOptionalCheck(e.cond.left, ctx) : null);
        if (narrowed && narrowed.inThen) {
          if (!narrowed.fieldExpr) {
            // Simple var: extend env only — transform will detect and generate match
            thenCtx = withEnv(thenCtx, extend(thenCtx.env, narrowed.varName, narrowed.innerTy));
          } else if (narrowed.fieldExpr.kind === "field" && narrowed.fieldExpr.obj.kind === "var") {
            // Simple field chain (obj.field): narrow via field context — no substitution
            thenCtx = {
              ...thenCtx,
              narrowedFields: [...thenCtx.narrowedFields, {
                objName: (narrowed.fieldExpr.obj as { kind: "var"; name: string }).name,
                fieldName: (narrowed.fieldExpr as { kind: "field"; field: string }).field,
                narrowedTy: narrowed.innerTy,
              }],
            };
          } else {
            // Complex expression (call result, deep chain, etc.): transform can't detect these,
            // so keep old behavior — substitute + narrowedVar + narrowedExpr
            narrowedVar = narrowed.varName;
            narrowedExprResolved = narrowed.narrowedExpr ?? resolveExpr(narrowed.fieldExpr, ctx);
            rawThen = substituteRawExpr(e.then, narrowed.fieldExpr, { kind: "var", name: narrowed.varName });
            thenCtx = withEnv(thenCtx, extend(thenCtx.env, narrowed.varName, narrowed.innerTy));
          }
        }
      }

      let then_ = resolveExpr(rawThen, thenCtx);
      let else_ = resolveExpr(e.else, ctx);
      then_ = coerceStr(then_, else_.ty);
      else_ = coerceStr(else_, then_.ty);
      let ty = then_.ty.kind !== "unknown" ? then_.ty : else_.ty;
      // When one branch is undefined, result is optional
      if (then_.ty.kind === "void" && else_.ty.kind !== "void" && else_.ty.kind !== "unknown") {
        ty = { kind: "optional", inner: else_.ty };
      } else if (else_.ty.kind === "void" && then_.ty.kind !== "void" && then_.ty.kind !== "unknown") {
        ty = { kind: "optional", inner: then_.ty };
      }
      // When narrowedExpr is set AND a branch is void, the match produces Optional
      if (narrowedExprResolved && (then_.ty.kind === "void" || else_.ty.kind === "void") && ty.kind !== "optional") {
        ty = { kind: "optional", inner: ty };
      }
      return { kind: "conditional", cond, then: then_, else: else_, ty, narrowedVar, narrowedExpr: narrowedExprResolved };
    }

    case "emptyCollection": {
      const ty = parseTsType(e.tsType);
      const elems = e.initElems ? e.initElems.map(el => resolveExpr(el, ctx)) : [];
      return { kind: "arrayLiteral", elems, ty };
    }

    case "havoc":
      return { kind: "havoc", ty: resolveTsType(e.tsType, ctx.overrides) };
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
    // Flow narrowing: if (x === undefined) { return } narrows x for rest of block.
    // Field chains are excluded — resolve can't substitute in statement lists;
    // transform's emitOptionalMatch handles field chains in statement contexts.
    if (s.kind === "if" && s.then.length > 0 && s.then[s.then.length - 1].kind === "return" && s.else.length === 0) {
      const narrowed = detectOptionalCheck(s.cond, withEnv(ctx, env));
      if (narrowed && !narrowed.inThen && !narrowed.fieldExpr) {
        env = extend(env, narrowed.varName, narrowed.innerTy);
      }
    }
  }
  return result;
}

function resolveStmt(s: RawStmt, ctx: Ctx): [TStmt, Env | null] {
  switch (s.kind) {
    case "let": {
      const declTy = resolveTsType(s.tsType, ctx.overrides, s.name);
      // Propagate declared type as returnTy so nested record expressions
      // resolve union variants correctly (e.g., EffectState → mode: EffectMode → { kind: 'Idle' })
      const initCtx = declTy.kind === "user" ? { ...ctx, returnTy: declTy } : ctx;
      const init = coerceStr(resolveExpr(s.init, initCtx), declTy);
      // Map indexing: TS says T, but access can fail → use Optional<T> from init
      const ty = (declTy.kind !== "optional" && init.ty.kind === "optional") ? init.ty : declTy;
      // const collections are mutable in value-semantics world (TS mutates in place, Dafny/Lean reassign)
      const mutable = s.mutable || isRefMutableInTS(ty);
      return [{ kind: "let", name: s.name, ty, mutable, init }, extend(ctx.env, s.name, ty)];
    }

    case "assign": {
      const targetTy = lookup(ctx.env, s.target) ?? { kind: "unknown" as const };
      return [{ kind: "assign", target: s.target, value: coerceStr(resolveExpr(s.value, ctx), targetTy) }, ctx.env];
    }

    case "return": {
      let value = coerceStr(resolveExpr(s.value, ctx), ctx.returnTy);
      // Wrap non-optional return value in Some when function returns optional
      // Skip if already optional, void, or undefined (which maps to None)
      const isUndef = value.kind === "var" && value.name === "undefined";
      if (ctx.returnTy.kind === "optional" && value.ty.kind !== "optional" && !isUndef) {
        value = wrapSome(value, ctx.returnTy);
      }
      return [{ kind: "return", value }, ctx.env];
    }

    case "break":
      return [{ kind: "break" }, ctx.env];

    case "continue":
      return [{ kind: "continue" }, ctx.env];

    case "expr":
      return [{ kind: "expr", expr: resolveExpr(s.expr, ctx) }, ctx.env];

    case "if": {
      // Narrow optional<T> → T when checking !== undefined or undefined !==.
      // Also checks left side of && conditions: if (x !== undefined && ...) { ... }
      // Field chains are excluded — resolve can't substitute in statement bodies;
      // transform's emitOptionalMatch handles field chains in statement contexts.
      let thenCtx = ctx, elseCtx = ctx;
      const narrowed = detectOptionalCheck(s.cond, ctx)
        ?? (s.cond.kind === "binop" && s.cond.op === "&&" ? detectOptionalCheck(s.cond.left, ctx) : null);
      if (narrowed && !narrowed.fieldExpr) {
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
      // Determine element types for each destructured name
      const nameTypes: Ty[] = [];
      let env = ctx.env;
      if (s.names.length === 1) {
        // Single name: element type from array/set
        const elemTy: Ty = iterable.ty.kind === "array" ? iterable.ty.elem
          : iterable.ty.kind === "set" ? iterable.ty.elem
          : { kind: "unknown" };
        nameTypes.push(elemTy);
      } else if (s.names.length >= 2 && iterable.ty.kind === "map") {
        // Map destructuring: [key, value]
        nameTypes.push(iterable.ty.key, iterable.ty.value);
      } else {
        // General tuple destructuring: all unknown
        for (const _ of s.names) nameTypes.push({ kind: "unknown" });
      }
      const idxName = `_${s.names[0]}_idx`;
      env = extend(env, idxName, { kind: "nat" });
      for (let j = 0; j < s.names.length; j++) {
        env = extend(env, s.names[j], nameTypes[j] ?? { kind: "unknown" });
      }
      const bodyCtx = withEnv(ctx, env);
      return [{
        kind: "forof", names: s.names, nameTypes, iterable,
        invariants: resolveSpecs(s.invariants, { ...bodyCtx, inSpec: true }),
        doneWith: s.doneWith ? resolveSpec(s.doneWith, { ...bodyCtx, inSpec: true }) : null,
        body: resolveBlock(s.body, bodyCtx),
      }, ctx.env];
    }

    case "throw":
      return [{ kind: "throw" }, ctx.env];

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
      case "let": if (s.mutable || s.init.kind === "havoc") return false; break;
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
  // //@ pure functions are always considered pure — never taint callers
  const forcePure = new Set(functions.filter(fn => fn.pure).map(fn => fn.name));

  // Build call graph: fn → set of same-file functions it calls
  const callGraph = new Map<string, Set<string>>();
  for (const fn of functions) {
    const calls = new Set<string>();
    collectCallsStmts(fn.body, allFnNames, calls);
    callGraph.set(fn.name, calls);
  }

  // Seed: syntactically non-pure functions (skip //@ pure)
  const nonPure = new Set(
    functions.filter(fn => !forcePure.has(fn.name) && !isSyntacticallyPure(fn.body)).map(fn => fn.name)
  );

  // Build reverse graph: fn → set of functions that call it
  const callers = new Map<string, Set<string>>();
  for (const name of allFnNames) callers.set(name, new Set());
  for (const [caller, callees] of callGraph) {
    for (const callee of callees) callers.get(callee)!.add(caller);
  }

  // Propagate impurity through reverse call graph (skip //@ pure)
  const worklist = [...nonPure];
  while (worklist.length > 0) {
    const fn = worklist.pop()!;
    for (const caller of callers.get(fn) ?? []) {
      if (!nonPure.has(caller) && !forcePure.has(caller)) {
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

function resolveFunction(
  fn: RawFunction, typeDecls: TypeDeclInfo[], pureFns: Set<string>,
  fnParams: Map<string, Ty[]> = new Map(), fnReturns: Map<string, Ty> = new Map(),
  opts?: { thisBinding?: { name: string; ty: Ty }; forcePure?: boolean }
): TFunction {

  const overrides = new Map(fn.typeAnnotations.map(a => [a.name, a.type]));
  const params: TParam[] = fn.params.map(p => ({ name: p.name, ty: resolveTsType(p.tsType, overrides, p.name) }));
  const returnTy = resolveTsType(fn.returnType, overrides, "\\result");

  let env: Env | null = null;
  if (opts?.thisBinding) env = extend(env, opts.thisBinding.name, opts.thisBinding.ty);
  for (const p of params) env = extend(env, p.name, p.ty);

  const baseCtx: Ctx = { env, typeDecls, overrides, allowResult: false, returnTy, pureFns, fnParams, fnReturns, inSpec: false, inLambda: false, narrowedFields: [] };
  const requiresCtx: Ctx = { ...baseCtx, inSpec: true };
  const ensuresCtx: Ctx = { ...baseCtx, allowResult: true, inSpec: true };

  // Apply type parameter constraints from //@ type T (==) annotations
  const typeParams = fn.typeParams.map(tp => {
    const constraint = overrides.get(tp);
    return constraint ? `${tp}${constraint}` : tp;
  });

  return {
    name: fn.name, typeParams, params, returnTy,
    requires: resolveSpecs(fn.requires, requiresCtx),
    ensures: resolveSpecs(fn.ensures, ensuresCtx),
    decreases: fn.decreases ? resolveSpec(fn.decreases, requiresCtx) : null,
    isPure: opts?.forcePure !== undefined ? opts.forcePure : pureFns.has(fn.name),
    forcePure: fn.pure,
    body: resolveBlock(fn.body, baseCtx),
  };
}

function resolveClass(cls: import("./rawir.js").RawClass, typeDecls: TypeDeclInfo[], pureFns: Set<string>, fnParams: Map<string, Ty[]> = new Map(), fnReturns: Map<string, Ty> = new Map()): import("./typedir.js").TClass {
  const fields = cls.fields.map(f => ({ name: f.name, ty: parseTsType(f.tsType) }));
  // Create a synthetic record type for 'this' so field access resolves
  const thisType: Ty = { kind: "user", name: cls.name };
  const thisDecl: TypeDeclInfo = { name: cls.name, kind: "record", fields: cls.fields.map(f => ({ name: f.name, tsType: f.tsType, type: parseTsType(f.tsType) })) };
  const allTypeDecls = [...typeDecls, thisDecl];

  const methods = cls.methods.map(fn =>
    resolveFunction(fn, allTypeDecls, pureFns, fnParams, fnReturns, {
      thisBinding: { name: "this", ty: thisType },
      forcePure: false,  // class methods are never pure (they access this)
    })
  );

  return { name: cls.name, fields, methods };
}

/** Pre-compute Ty on all TypeDeclInfo fields/variants/aliases.
 *  Called once per module so consumers can read field.type instead of re-parsing tsType. */
function precomputeFieldTypes(typeDecls: TypeDeclInfo[]) {
  for (const d of typeDecls) {
    if (d.fields) for (const f of d.fields) f.type = parseTsType(f.tsType);
    if (d.variants) for (const v of d.variants) for (const f of v.fields) f.type = parseTsType(f.tsType);
    if (d.aliasOf && !d.aliasOfTy) d.aliasOfTy = parseTsType(d.aliasOf);
  }
}

export function resolveModule(raw: RawModule): TModule {
  precomputeFieldTypes(raw.typeDecls);
  const pureFns = computePureFns(raw.functions);
  // Pre-compute function parameter and return types
  const fnParams = new Map<string, Ty[]>();
  const fnReturns = new Map<string, Ty>();
  for (const fn of raw.functions) {
    const overrides = new Map(fn.typeAnnotations.map(a => [a.name, a.type]));
    fnParams.set(fn.name, fn.params.map(p => resolveTsType(p.tsType, overrides, p.name)));
    fnReturns.set(fn.name, resolveTsType(fn.returnType, overrides, "\\result"));
  }
  const emptyCtx: Ctx = { env: null, typeDecls: raw.typeDecls, overrides: new Map(), allowResult: false, returnTy: { kind: "int" }, pureFns, fnParams, fnReturns, inSpec: false, inLambda: false, narrowedFields: [] };
  const constants = (raw.constants ?? []).map(c => ({
    name: c.name,
    ty: parseTsType(c.tsType),
    value: resolveExpr(c.value, emptyCtx),
  }));

  return {
    file: raw.file,
    typeDecls: raw.typeDecls,
    constants,
    functions: raw.functions.map(fn => resolveFunction(fn, raw.typeDecls, pureFns, fnParams, fnReturns)),
    classes: (raw.classes ?? []).map(cls => resolveClass(cls, raw.typeDecls, pureFns, fnParams, fnReturns)),
  };
}
