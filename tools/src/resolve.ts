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

// ── Access paths ─────────────────────────────────────────────

/** Pure access path — a chain of field accesses rooted at a variable.
 *  E.g. `a.b.c` → { rootVar: "a", fields: ["b", "c"] }. Empty fields
 *  means the path is just the var itself. */
interface AccessPath {
  rootVar: string;
  fields: string[];
}

function asRawAccessPath(e: RawExpr): AccessPath | null {
  if (e.kind === "var") return { rootVar: e.name, fields: [] };
  if (e.kind === "field") {
    const inner = asRawAccessPath(e.obj);
    if (!inner) return null;
    return { rootVar: inner.rootVar, fields: [...inner.fields, e.field] };
  }
  return null;
}

function accessPathsEqual(a: AccessPath, b: AccessPath): boolean {
  return a.rootVar === b.rootVar && a.fields.length === b.fields.length &&
    a.fields.every((f, i) => f === b.fields[i]);
}

// ── Context ──────────────────────────────────────────────────

interface NarrowedPath {
  path: AccessPath;
  narrowedTy: Ty;
}

/** A `k in m` atom known to hold in the current scope. Both sides are pure
 *  access paths (var or field chain) so we can compare by path equality.
 *  Produced by scanning function requires, enclosing `if (k in m)` branches,
 *  `//@ assert k in m` statements, and while-loop invariants. Consumed in
 *  the index case (resolve.ts:~447) to return `obj.ty.value` (non-optional)
 *  instead of `Option<V>` when the access is provably safe. */
interface NarrowedIndex {
  obj: AccessPath;
  idx: AccessPath;
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
  narrowedPaths: NarrowedPath[];  // pure access path narrowing for conditional then-branches
  narrowedIndices: NarrowedIndex[];  // `k in m` atoms known-true in this scope
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

/** Detect optional checks: `v !== undefined` (positive narrows then-branch),
 *  `v === undefined` (negative narrows else-branch), or `!v` (equivalent to
 *  `=== undefined`).
 *  Returns:
 *    - simple var: `varName` set, `fieldExpr` unset
 *    - complex (field chain or call): `fieldExpr` set, `varName` empty
 *    - inThen: true for `!==` (truthy), false for `===` and `!v` (falsy).
 *  Does NOT recurse into `&&`. */
function detectOptionalCheck(cond: RawExpr, ctx: Ctx): {
  varName: string; innerTy: Ty; inThen: boolean;
  fieldExpr?: RawExpr;
} | null {
  // `!v` where v is optional — same shape as `v === undefined` (inThen: false).
  if (cond.kind === "unop" && cond.op === "!") {
    const inner = classifyOptExpr(cond.expr, ctx);
    return inner ? { ...inner, inThen: false } : null;
  }
  if (cond.kind !== "binop" || (cond.op !== "!==" && cond.op !== "===")) {
    // Bare optional truthiness: `if (v)` where v: T | undefined — same as `v !== undefined`.
    const inner = classifyOptExpr(cond, ctx);
    return inner ? { ...inner, inThen: true } : null;
  }
  // Identify the expression being checked against undefined
  let optExpr: RawExpr | null = null;
  if (cond.right.kind === "var" && cond.right.name === "undefined") optExpr = cond.left;
  if (cond.left.kind === "var" && cond.left.name === "undefined") optExpr = cond.right;
  if (!optExpr) return null;
  const inner = classifyOptExpr(optExpr, ctx);
  return inner ? { ...inner, inThen: cond.op === "!==" } : null;
}

/** Classify an expression as a simple var or field-chain optional, returning
 *  the shape needed by detectOptionalCheck (sans inThen). */
function classifyOptExpr(e: RawExpr, ctx: Ctx): { varName: string; innerTy: Ty; fieldExpr?: RawExpr } | null {
  if (e.kind === "var") {
    const ty = lookup(ctx.env, e.name);
    if (!ty || ty.kind !== "optional") return null;
    return { varName: e.name, innerTy: ty.inner };
  }
  const resolved = resolveExpr(e, ctx);
  if (resolved.ty.kind !== "optional") return null;
  return { varName: "", innerTy: resolved.ty.inner, fieldExpr: e };
}

/** Collect all optional narrowings from an early-return condition.
 *  Handles single checks (x === undefined) and compound || chains
 *  (x === undefined || y === undefined). */
function collectEarlyReturnNarrowings(cond: RawExpr, ctx: Ctx): { varName: string; innerTy: Ty }[] {
  if (cond.kind === "binop" && cond.op === "||") {
    return [...collectEarlyReturnNarrowings(cond.left, ctx), ...collectEarlyReturnNarrowings(cond.right, ctx)];
  }
  const narrowed = detectOptionalCheck(cond, ctx);
  if (narrowed && !narrowed.inThen && !narrowed.fieldExpr) {
    return [{ varName: narrowed.varName, innerTy: narrowed.innerTy }];
  }
  return [];
}

/** TExpr → AccessPath. Counterpart to `asRawAccessPath` for resolved trees.
 *  Used by `extractInAtoms` when pulling atoms out of typed spec expressions. */
function asTExprAccessPath(e: TExpr): AccessPath | null {
  if (e.kind === "var") return { rootVar: e.name, fields: [] };
  if (e.kind === "field") {
    const inner = asTExprAccessPath(e.obj);
    if (!inner) return null;
    return { rootVar: inner.rootVar, fields: [...inner.fields, e.field] };
  }
  return null;
}

/** Walk `e` collecting top-level `k in m` atoms where both sides are pure
 *  access paths and the right side is map-typed. Descends through `&&` only.
 *  Does NOT descend into `==>`, `||`, negation, `forall`, or `exists` — in
 *  those positions an atom is only conditionally known (or a premise, not a
 *  conclusion), so treating it as always-true in the enclosing scope would
 *  be unsound. */
function extractInAtoms(e: TExpr): NarrowedIndex[] {
  if (e.kind === "binop" && e.op === "in" && e.right.ty.kind === "map") {
    const obj = asTExprAccessPath(e.right);
    const idx = asTExprAccessPath(e.left);
    if (obj && idx) return [{ obj, idx }];
    return [];
  }
  if (e.kind === "binop" && e.op === "&&") {
    return [...extractInAtoms(e.left), ...extractInAtoms(e.right)];
  }
  return [];
}

/** Extract `k in m` atoms that hold when `e` is *false*. Currently only
 *  strips an outer `!` and hands the inner to `extractInAtoms`; that covers
 *  `if (!(k in m)) ...` for the else-branch and early-return patterns.
 *  De Morgan over `||` / nested `!(a && b)` not handled yet. */
function extractInAtomsNegated(e: TExpr): NarrowedIndex[] {
  if (e.kind === "unop" && e.op === "!") return extractInAtoms(e.expr);
  return [];
}

/** Extend a Ctx with `k in m` atoms. Deduplicates against existing atoms. */
function withInAtoms(ctx: Ctx, atoms: NarrowedIndex[]): Ctx {
  if (atoms.length === 0) return ctx;
  const existing = ctx.narrowedIndices;
  const added: NarrowedIndex[] = [];
  for (const a of atoms) {
    if (!existing.some(e => accessPathsEqual(e.obj, a.obj) && accessPathsEqual(e.idx, a.idx))) {
      added.push(a);
    }
  }
  if (added.length === 0) return ctx;
  return { ...ctx, narrowedIndices: [...existing, ...added] };
}

/** Walk an `&&` chain of `e !== undefined` checks, returning a Ctx with all
 *  narrowings applied. Earlier checks are in scope for later checks (so the
 *  right side of `&&` sees the left side's narrowings). */
function collectAndChainNarrowings(cond: RawExpr, ctx: Ctx): Ctx {
  if (cond.kind === "binop" && cond.op === "&&") {
    const leftCtx = collectAndChainNarrowings(cond.left, ctx);
    return collectAndChainNarrowings(cond.right, leftCtx);
  }
  const n = detectOptionalCheck(cond, ctx);
  if (!n || !n.inThen) return ctx;
  if (!n.fieldExpr) {
    return withEnv(ctx, extend(ctx.env, n.varName, n.innerTy));
  }
  const path = asRawAccessPath(n.fieldExpr);
  if (path) {
    return { ...ctx, narrowedPaths: [...ctx.narrowedPaths, { path, narrowedTy: n.innerTy }] };
  }
  return ctx;
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
    if (fn.field === "includes" || fn.field === "startsWith") return { kind: "bool" };
  }
  return { kind: "unknown" };
}

/** Look up the type of `field` on `objTy`. Returns `unknown` if not found. */
function lookupFieldTy(objTy: Ty, field: string, ctx: Ctx): { ty: Ty; isDiscriminant: boolean } {
  if (field === "length" && (objTy.kind === "array" || objTy.kind === "string")) {
    return { ty: { kind: "nat" }, isDiscriminant: false };
  }
  if (field === "size" && (objTy.kind === "map" || objTy.kind === "set")) {
    return { ty: { kind: "nat" }, isDiscriminant: false };
  }
  if (objTy.kind === "user") {
    const baseTyName = objTy.name.includes("<") ? objTy.name.slice(0, objTy.name.indexOf("<")) : objTy.name;
    const isDiscriminant = getDiscriminant(ctx, baseTyName) === field;
    const decl = findDecl(ctx, baseTyName);
    if (decl?.kind === "record") {
      const f = decl.fields?.find(f => f.name === field);
      if (f) return { ty: f.type!, isDiscriminant };
    }
    if (decl?.kind === "discriminated-union" && decl.variants) {
      for (const variant of decl.variants) {
        const f = variant.fields.find(f => f.name === field);
        if (f) return { ty: f.type!, isDiscriminant };
      }
    }
    return { ty: { kind: "unknown" }, isDiscriminant };
  }
  return { ty: { kind: "unknown" }, isDiscriminant: false };
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
      // && and ==> narrowing: left-side optional checks narrow the right side.
      // (For ==>, the premise is assumed in the conclusion — same principle.)
      let rightCtx = ctx;
      let rawRight = e.right;
      if (e.op === "&&" || e.op === "==>") {
        rightCtx = collectAndChainNarrowings(e.left, ctx);
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
      // Propagate parameter types to arguments for record literal resolution
      // (enables inline discriminated union construction in function arguments)
      const paramTypes = fn.kind === "var" && ctx.fnParams.has(fn.name) ? ctx.fnParams.get(fn.name)! : null;
      const args = coerceCallArgs(rawArgs.map((a, i) => {
        let aCtx = argCtx;
        if (paramTypes && i < paramTypes.length && paramTypes[i].kind === "user") {
          aCtx = { ...aCtx, returnTy: paramTypes[i] };
        }
        return resolveExpr(a, aCtx);
      }), fn, ctx);
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
      // Map bracket access: default to Option<V>. But if the enclosing scope has a
      // known `k in m` atom matching (obj, idx) — from requires, assert, an enclosing
      // `if (k in m)`, or a loop invariant — narrow to V. Parallels how `narrowedPaths`
      // narrows `obj.field.field` under optional-undefined checks.
      let idxTy: Ty;
      if (obj.ty.kind === "array") {
        idxTy = obj.ty.elem;
      } else if (obj.ty.kind === "map") {
        const objPath = asTExprAccessPath(obj);
        const idxPath = asTExprAccessPath(idx);
        const narrowed = objPath && idxPath && ctx.narrowedIndices.some(
          n => accessPathsEqual(n.obj, objPath) && accessPathsEqual(n.idx, idxPath)
        );
        idxTy = narrowed ? obj.ty.value : { kind: "optional" as const, inner: obj.ty.value };
      } else {
        idxTy = { kind: "unknown" as const };
      }
      return { kind: "index", obj, idx, ty: idxTy };
    }

    case "field": {
      const obj = resolveExpr(e.obj, ctx);
      let isDiscriminant = false;
      let ty: Ty = { kind: "unknown" };

      // Check narrowed path context (from conditional optional checks).
      // Applies when the current field-access forms a pure access path AND
      // that path is in the narrowedPaths list.
      if (ctx.narrowedPaths.length > 0) {
        const myPath = asRawAccessPath(e);
        if (myPath) {
          const np = ctx.narrowedPaths.find(n => accessPathsEqual(n.path, myPath));
          if (np) ty = np.narrowedTy;
        }
      }

      if (ty.kind === "unknown") {
        const lookup = lookupFieldTy(obj.ty, e.field, ctx);
        ty = lookup.ty;
        isDiscriminant = lookup.isDiscriminant;
      }

      return { kind: "field", obj, field: e.field, ty, isDiscriminant };
    }

    case "nullish": {
      // left ?? right — result type is left's inner (when left is optional)
      // or just left's type, unified with right's type.
      const left = resolveExpr(e.left, ctx);
      const right = resolveExpr(e.right, ctx);
      const ty: Ty = left.ty.kind === "optional" ? left.ty.inner : left.ty;
      return { kind: "nullish", left, right, ty };
    }

    case "optChain": {
      // obj?.<chain> — obj has type Option<T>; we walk the chain stepping
      // through types from T. The final result is Option<finalStepTy>
      // (collapsed: if finalStepTy is already optional, we don't double-wrap).
      // Narrow rewrites this to a someMatch with the chain applied to the binder.
      const obj = resolveExpr(e.obj, ctx);
      let stepInTy = obj.ty.kind === "optional" ? obj.ty.inner : obj.ty;
      const chain: import("./typedir.js").TChainStep[] = [];
      for (const step of e.chain) {
        if (step.kind === "field") {
          const fieldTy = lookupFieldTy(stepInTy, step.name, ctx).ty;
          chain.push({ kind: "field", name: step.name, ty: fieldTy });
          stepInTy = fieldTy;
        } else if (step.kind === "index") {
          const idx = resolveExpr(step.idx, ctx);
          const idxTy: Ty = stepInTy.kind === "array" ? stepInTy.elem
            : stepInTy.kind === "map" ? { kind: "optional", inner: stepInTy.value }
            : { kind: "unknown" };
          chain.push({ kind: "index", idx, ty: idxTy });
          stepInTy = idxTy;
        } else {
          // call: prev step yielded a callable (typically a method via field).
          // Build a fake fn TExpr from prev steps to reuse inferMethodReturnTy.
          const args = step.args.map(a => resolveExpr(a, ctx));
          const lastField = chain.length > 0 && chain[chain.length - 1].kind === "field"
            ? chain[chain.length - 1] as { kind: "field"; name: string; ty: Ty } : null;
          let callTy: Ty = { kind: "unknown" };
          let callKind: CallKind = "unknown";
          if (lastField) {
            // Build a synthetic field TExpr with the prior step's input type as obj
            // so inferMethodReturnTy can dispatch on the receiver type.
            const priorInTy = chain.length >= 2 ? chain[chain.length - 2].ty
              : (obj.ty.kind === "optional" ? obj.ty.inner : obj.ty);
            const fakeObj: TExpr = { kind: "var", name: "_chain_recv", ty: priorInTy };
            const fakeFn: TExpr = { kind: "field", obj: fakeObj, field: lastField.name, ty: lastField.ty };
            callTy = inferMethodReturnTy(fakeFn, args, ctx);
            callKind = "method";
          }
          chain.push({ kind: "call", args, ty: callTy, callKind });
          stepInTy = callTy;
        }
      }
      const finalTy = stepInTy;
      const ty: Ty = finalTy.kind === "optional" ? finalTy : { kind: "optional", inner: finalTy };
      return { kind: "optChain", obj, chain, ty };
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
      // \result desugars to a regular var so all the variable-narrowing
      // machinery (env lookup, optional checks, path matching) just works.
      // The env in ensuresCtx is pre-seeded with "\result" → returnTy.
      if (!ctx.allowResult) throw new Error("\\result is only valid in ensures");
      return { kind: "var", name: "\\result", ty: lookup(ctx.env, "\\result") ?? ctx.returnTy };

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

      // Type narrowing for the then/else branches. Following TS, we narrow
      // simple vars and any pure access path (`a.b.c.d`) — but not expressions
      // with method calls or index ops (bind-first required).
      // For &&-chains, all positive checks narrow the then-branch; earlier
      // checks are in scope when resolving later ones.
      let thenCtx = collectAndChainNarrowings(e.cond, ctx);
      let elseCtx = ctx;

      // Truthiness — cond itself is optional (`opt ? a : b`), only for simple vars.
      if (cond.ty.kind === "optional" && e.cond.kind === "var") {
        thenCtx = withEnv(thenCtx, extend(thenCtx.env, e.cond.name, cond.ty.inner));
      }

      // Single === undefined check narrows the else-branch.
      const single = detectOptionalCheck(e.cond, ctx);
      if (single && !single.inThen && !single.fieldExpr) {
        elseCtx = withEnv(elseCtx, extend(elseCtx.env, single.varName, single.innerTy));
      }
      if (!single && e.cond.kind === "binop" && e.cond.op === "||") {
        for (const n of collectEarlyReturnNarrowings(e.cond, ctx)) {
          elseCtx = withEnv(elseCtx, extend(elseCtx.env, n.varName, n.innerTy));
        }
      }
      // Map-index narrowing: `k in m` in the cond narrows the then-branch; `!(k in m)`
      // narrows the else-branch. Parallel to the if-statement hook in resolveStmt.
      thenCtx = withInAtoms(thenCtx, extractInAtoms(cond));
      elseCtx = withInAtoms(elseCtx, extractInAtomsNegated(cond));

      let then_ = resolveExpr(e.then, thenCtx);
      let else_ = resolveExpr(e.else, elseCtx);
      then_ = coerceStr(then_, else_.ty);
      else_ = coerceStr(else_, then_.ty);
      let ty = then_.ty.kind !== "unknown" ? then_.ty : else_.ty;
      if (then_.ty.kind === "void" && else_.ty.kind !== "void" && else_.ty.kind !== "unknown") {
        ty = { kind: "optional", inner: else_.ty };
      } else if (else_.ty.kind === "void" && then_.ty.kind !== "void" && then_.ty.kind !== "unknown") {
        ty = { kind: "optional", inner: then_.ty };
      }
      return { kind: "conditional", cond, then: then_, else: else_, ty };
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
  let narrowedIndices = ctx.narrowedIndices;
  for (const s of stmts) {
    const currentCtx = { ...ctx, env, narrowedIndices };
    const [typed, nextEnv] = resolveStmt(s, currentCtx);
    result.push(typed);
    env = nextEnv;
    // Flow narrowing: if (x === undefined) { return } narrows x for rest of block.
    // Also handles compound: if (x === undefined || y === undefined) { return }
    // Field chains are excluded — resolve can't substitute in statement lists;
    // transform's emitOptionalMatch handles field chains in statement contexts.
    if (s.kind === "if" && s.then.length > 0 && s.then[s.then.length - 1].kind === "return" && s.else.length === 0) {
      const narrowings = collectEarlyReturnNarrowings(s.cond, withEnv(ctx, env));
      for (const n of narrowings) {
        env = extend(env, n.varName, n.innerTy);
      }
      // Map-index narrowing: `if (!(k in m)) return;` means `k in m` holds in rest.
      if (typed.kind === "if") {
        const addedAtoms = extractInAtomsNegated(typed.cond);
        if (addedAtoms.length > 0) {
          narrowedIndices = withInAtoms({ ...ctx, narrowedIndices }, addedAtoms).narrowedIndices;
        }
      }
    }
    // Assert narrowing: `//@ assert k in m` adds atoms for the rest of the block.
    if (typed.kind === "assert") {
      const addedAtoms = extractInAtoms(typed.expr);
      if (addedAtoms.length > 0) {
        narrowedIndices = withInAtoms({ ...ctx, narrowedIndices }, addedAtoms).narrowedIndices;
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
      // For &&-chains, all positive optional checks narrow the then-branch;
      // earlier checks are in scope when resolving later ones.
      // Single-check === undefined narrows the else-branch.
      let thenCtx = collectAndChainNarrowings(s.cond, ctx);
      let elseCtx = ctx;
      const single = detectOptionalCheck(s.cond, ctx);
      if (single && !single.inThen && !single.fieldExpr) {
        elseCtx = withEnv(ctx, extend(ctx.env, single.varName, single.innerTy));
      }
      // Narrow map index access across `k in m` / `!(k in m)` in the cond:
      // positive atoms (from `k in m` or &&-chains containing it) → then-branch;
      // negated atoms (from `!(k in m)`) → else-branch.
      const resolvedCond = resolveExpr(s.cond, ctx);
      thenCtx = withInAtoms(thenCtx, extractInAtoms(resolvedCond));
      elseCtx = withInAtoms(elseCtx, extractInAtomsNegated(resolvedCond));
      return [{ kind: "if", cond: resolvedCond, then: resolveBlock(s.then, thenCtx), else: resolveBlock(s.else, elseCtx) }, ctx.env];
    }

    case "while": {
      const whileSpecCtx = { ...ctx, inSpec: true };
      const resolvedInvariants = resolveSpecs(s.invariants, whileSpecCtx);
      // Invariants hold at the top of the body, so any `k in m` atoms among them
      // narrow map index access in the body.
      const bodyCtx = withInAtoms(ctx, resolvedInvariants.flatMap(extractInAtoms));
      return [{
        kind: "while",
        cond: resolveExpr(s.cond, ctx),
        invariants: resolvedInvariants,
        decreases: s.decreases ? resolveSpec(s.decreases, whileSpecCtx) : null,
        doneWith: s.doneWith ? resolveSpec(s.doneWith, whileSpecCtx) : null,
        body: resolveBlock(s.body, bodyCtx),
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

  const baseCtx: Ctx = { env, typeDecls, overrides, allowResult: false, returnTy, pureFns, fnParams, fnReturns, inSpec: false, inLambda: false, narrowedPaths: [], narrowedIndices: [] };
  const requiresCtx: Ctx = { ...baseCtx, inSpec: true };
  const ensuresCtx: Ctx = { ...baseCtx, env: extend(env, "\\result", returnTy), allowResult: true, inSpec: true };

  // Apply type parameter constraints from //@ type T (==) annotations
  const typeParams = fn.typeParams.map(tp => {
    const constraint = overrides.get(tp);
    return constraint ? `${tp}${constraint}` : tp;
  });

  // Resolve requires first so we can extract any `k in m` atoms and seed them
  // into the body context and the ensures context — they hold for the whole
  // body (pure fns) and for post-state references in the ensures (map params
  // aren't mutated through their binding in the Dafny translation).
  const resolvedRequires = resolveSpecs(fn.requires, requiresCtx);
  const requiresAtoms = resolvedRequires.flatMap(extractInAtoms);
  const bodyCtx = withInAtoms(baseCtx, requiresAtoms);
  const ensuresCtxNarrowed = withInAtoms(ensuresCtx, requiresAtoms);

  return {
    name: fn.name, typeParams, params, returnTy,
    requires: resolvedRequires,
    ensures: resolveSpecs(fn.ensures, ensuresCtxNarrowed),
    decreases: fn.decreases ? resolveSpec(fn.decreases, requiresCtx) : null,
    isPure: opts?.forcePure !== undefined ? opts.forcePure : pureFns.has(fn.name),
    forcePure: fn.pure,
    body: resolveBlock(fn.body, bodyCtx),
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
  const emptyCtx: Ctx = { env: null, typeDecls: raw.typeDecls, overrides: new Map(), allowResult: false, returnTy: { kind: "int" }, pureFns, fnParams, fnReturns, inSpec: false, inLambda: false, narrowedPaths: [], narrowedIndices: [] };
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
