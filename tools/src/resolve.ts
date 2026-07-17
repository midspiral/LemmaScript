/**
 * Resolve — Raw IR → Typed IR.
 *
 * Uses linked environments (Scheme-style) for lexical scoping.
 * No mutation — each let extends the chain, lookup walks it.
 */

import type { RawExpr, RawStmt, RawFunction, RawModule } from "./rawir.js";
import type { Ty, TExpr, TStmt, TFunction, TModule, TParam, CallKind } from "./typedir.js";
import { isBigInt, tyEqual, isTerminatorKind } from "./typedir.js";
import { parseTsType, tyToCanonical } from "./types.js";
import type { TypeDeclInfo } from "./types.js";
import { parseExpr } from "./specparser.js";
import { freshName } from "./names.js";

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
function envKeys(env: Env | null): string[] {
  const out: string[] = [];
  let e = env;
  while (e) { out.push(e.name); e = e.parent; }
  return out;
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
  externs: Map<string, { flat: string; params: Ty[]; returnTy: Ty }>;  // qualified name → declared signature (from `//@ extern`)
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

/** Find the synth array-union TypeDecl named `name` (discriminant `__isArray__`). */
function findSynthArrayUnion(name: string, typeDecls: TypeDeclInfo[]): TypeDeclInfo | null {
  const decl = typeDecls.find(d => d.name === name);
  if (decl?.kind === "discriminated-union" && decl.discriminant === "__isArray__") return decl;
  return null;
}

/** Coerce `value` to `targetTy` at an assignment-position. Mirrors TS subtyping
 *  for the two upcast shapes LS synthesizes:
 *    - `T` into `optional<T>` slot  → wrap with `Some(...)`
 *    - `T[]` into a synth `T[] | U` slot → wrap with `ArrayBranch(...)`
 *    - `U`   into a synth `T[] | U` slot → wrap with `NonArrayBranch(...)`
 *  Returns `value` unchanged if no coercion applies (types already match,
 *  source is unknown, or no rule matches). */
function coerceToTargetTy(value: TExpr, targetTy: Ty, typeDecls: TypeDeclInfo[]): TExpr {
  if (value.ty.kind === "unknown" || value.ty.kind === "void") return value;
  if (targetTy.kind === "optional" && value.ty.kind !== "optional") {
    return wrapSome(value, targetTy);
  }
  if (targetTy.kind === "user") {
    const synth = findSynthArrayUnion(targetTy.name, typeDecls);
    if (synth && synth.variants && synth.variants.length === 2) {
      const arrVariant = synth.variants.find(v => v.name === "ArrayBranch");
      const nonVariant = synth.variants.find(v => v.name === "NonArrayBranch");
      if (value.ty.kind === "array" && arrVariant) {
        return { kind: "call", fn: { kind: "var", name: "ArrayBranch", ty: targetTy },
          args: [value], ty: targetTy, callKind: "pure" };
      }
      if (value.ty.kind !== "array" && nonVariant) {
        return { kind: "call", fn: { kind: "var", name: "NonArrayBranch", ty: targetTy },
          args: [value], ty: targetTy, callKind: "pure" };
      }
    }
  }
  return value;
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
  if (e.kind === "result") {
    const ty = lookup(ctx.env, "\\result");
    if (!ty || ty.kind !== "optional") return null;
    return { varName: "\\result", innerTy: ty.inner };
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
  const direct = ctx.typeDecls.find(d => d.name === name);
  if (direct) return direct;
  // Dotted names (e.g. `Agent.Info`, `Permission.Ruleset`): fall back to the
  // last segment, so `//@ declare-type Info { ... }` matches a reference to
  // `Agent.Info` without forcing the user to repeat the namespace.
  const dotIdx = name.lastIndexOf(".");
  if (dotIdx >= 0) return ctx.typeDecls.find(d => d.name === name.slice(dotIdx + 1));
  return undefined;
}

/** Expand alias-kind typeDecls when the alias target is structural (array,
 *  map, set, optional, or another user type). Primitive-typed aliases like
 *  `type TaskId = number` stay as `user("TaskId")` so the generated Dafny
 *  preserves the alias name. Recursive through compound types; cycle-safe. */
function expandAlias(ty: Ty, typeDecls: TypeDeclInfo[], seen: Set<string> = new Set()): Ty {
  if (ty.kind === "user") {
    if (seen.has(ty.name)) return ty;
    let decl = typeDecls.find(d => d.name === ty.name);
    if (!decl && ty.name.includes(".")) {
      const tail = ty.name.slice(ty.name.lastIndexOf(".") + 1);
      decl = typeDecls.find(d => d.name === tail);
    }
    if (decl?.kind === "alias" && decl.aliasOfTy) {
      const target = decl.aliasOfTy;
      if (target.kind === "array" || target.kind === "map" || target.kind === "set" || target.kind === "optional" || target.kind === "user") {
        return expandAlias(target, typeDecls, new Set([...seen, ty.name]));
      }
    }
    return ty;
  }
  if (ty.kind === "optional") return { kind: "optional", inner: expandAlias(ty.inner, typeDecls, seen) };
  if (ty.kind === "array") return { kind: "array", elem: expandAlias(ty.elem, typeDecls, seen) };
  if (ty.kind === "tuple") return { kind: "tuple", elems: ty.elems.map(e => expandAlias(e, typeDecls, seen)) };
  if (ty.kind === "set") return { kind: "set", elem: expandAlias(ty.elem, typeDecls, seen) };
  if (ty.kind === "map") return { kind: "map", key: expandAlias(ty.key, typeDecls, seen), value: expandAlias(ty.value, typeDecls, seen) };
  return ty;
}

function getDiscriminant(ctx: Ctx, typeName: string): string | undefined {
  return findDecl(ctx, typeName)?.discriminant;
}

// ── Equality hazard: structural in the proof vs reference at runtime ─────────
// `===`/`!==` is modeled as Dafny structural equality, but the SAME TypeScript
// runs `===` as JS *reference* equality on objects/arrays. The two agree only
// when the operand is a primitive at runtime: number / string / bool, or a
// string-union enum (which runs as a plain string). Records, discriminated
// unions, arrays, maps, sets, and unresolved generics are reference-compared at
// runtime, so a structural proof over them is unsound. Returns true for those.
function refEqHazard(ty: Ty, typeDecls: TypeDeclInfo[]): boolean {
  if (ty.kind === "array" || ty.kind === "map" || ty.kind === "set" || ty.kind === "tuple") return true;
  if (ty.kind === "user") {
    let decl = typeDecls.find(d => d.name === ty.name);
    if (!decl && ty.name.includes(".")) {
      const tail = ty.name.slice(ty.name.lastIndexOf(".") + 1);
      decl = typeDecls.find(d => d.name === tail);
    }
    if (!decl) return true;                          // generic type parameter / unknown → assume reference
    if (decl.kind === "string-union") return false;  // runs as a JS string → `===` is structural
    if (decl.kind === "alias") return decl.aliasOfTy ? refEqHazard(decl.aliasOfTy, typeDecls) : false;
    return true;                                     // record / discriminated-union → reference at runtime
  }
  return false;                                      // primitives, optional, unknown, fn, void
}

const _warnedRefEq = new Set<string>();
function warnRefEq(op: string, l: Ty, r: Ty): void {
  const label = (t: Ty) => t.kind === "user" ? t.name : t.kind;
  const msg = `'${op}' compares non-primitive operands (${label(l)} ${op} ${label(r)}): structural equality in the proof, but reference equality when this TypeScript runs. Sound only if operands are primitives or a canonical (string/number) encoding; otherwise compare via an explicit structural equals.`;
  if (_warnedRefEq.has(msg)) return;
  _warnedRefEq.add(msg);
  console.error(`WARNING: ${msg}`);
}

/** A type ts-morph handed us that LemmaScript hasn't modeled: contains
 *  `unknown` (TS `any`), or a `user` type whose name isn't a known declaration
 *  (an opaque expanded union like `"AssistantMsg | ToolMsg"` that ts-morph
 *  produced by expanding an alias LS shadows via declare-type). Used by
 *  `case "let"` to decide when LS's own `init.ty` is the better source of
 *  structure. */
function isUnmodeledTy(ty: Ty, typeDecls: TypeDeclInfo[]): boolean {
  if (ty.kind === "unknown") return true;
  if (ty.kind === "optional") return isUnmodeledTy(ty.inner, typeDecls);
  if (ty.kind === "array") return isUnmodeledTy(ty.elem, typeDecls);
  if (ty.kind === "tuple") return ty.elems.some(e => isUnmodeledTy(e, typeDecls));
  if (ty.kind === "set") return isUnmodeledTy(ty.elem, typeDecls);
  if (ty.kind === "map") return isUnmodeledTy(ty.key, typeDecls) || isUnmodeledTy(ty.value, typeDecls);
  if (ty.kind === "user") {
    const base = ty.name.includes("<") ? ty.name.slice(0, ty.name.indexOf("<")) : ty.name;
    return !typeDecls.some(d => d.name === base);
  }
  return false;
}

/** A `user` type that resolves to a string-union declare-type — runs as a plain
 *  string at runtime, so it's a refinement of `string`, not an opaque blob. */
function isStringUnionTy(ty: Ty, typeDecls: TypeDeclInfo[]): boolean {
  if (ty.kind !== "user") return false;
  const base = ty.name.includes("<") ? ty.name.slice(0, ty.name.indexOf("<")) : ty.name;
  return typeDecls.some(d => d.name === base && d.kind === "string-union");
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
  if (fn.kind === "field" && fn.obj.kind === "var" && fn.obj.name === "Array" && fn.field === "isArray") return "pure";
  if (fn.kind === "var" && (ctx.inSpec || ctx.inLambda) && ctx.pureFns.has(fn.name)) return "spec-pure";
  // Bare-name `//@ extern` declarations are emitted as `function {:axiom}` —
  // pure from the verifier's perspective. Classify them as pure so callers
  // don't get lifted to statement-level binds (which would force lambdas to
  // become multi-statement, illegal in Dafny).
  if (fn.kind === "var" && ctx.externs.has(fn.name)) return "pure";
  if (fn.kind === "var" && ctx.inSpec) {
    // Not a known pure function — could be external (Lean-defined spec helper).
    // Pass through as "pure" and let Lean catch any errors.
    return "pure";
  }
  if (fn.kind === "var") return "method";
  return "unknown";
}

// ── Call resolution helpers ─────────────────────────────────

/** Infer lambda param types from array method context (map, filter, etc.)
 *  AND from function-typed parameters of named callees (e.g., a `Comparator =
 *  (a, b) => bool` parameter propagates `string, string` to the lambda's
 *  inline params). Returns updated rawArgs with inferred tsType. */
function tyToTsStr(ty: Ty): string | undefined {
  if (ty.kind === "user") return ty.name;
  if (ty.kind === "string") return "string";
  if (ty.kind === "int" || ty.kind === "nat") return "number";
  if (ty.kind === "bool") return "boolean";
  // Optional element (e.g. a `.filter` over a `T | undefined`-typed map result):
  // type the callback param so its `x !== undefined` check narrows correctly.
  if (ty.kind === "optional") { const inner = tyToTsStr(ty.inner); return inner ? `${inner} | undefined` : undefined; }
  return undefined;
}
function inferLambdaParamTypes(fn: TExpr, rawArgs: RawExpr[], ctx?: Ctx): RawExpr[] {
  // sort's comparator takes two params, both the element type.
  if (fn.kind === "field" && fn.obj.ty.kind === "array" && fn.field === "sort" &&
      rawArgs.length >= 1 && rawArgs[0].kind === "lambda" && rawArgs[0].params.length >= 1) {
    const tsType = tyToTsStr(fn.obj.ty.elem);
    if (tsType) {
      const lam = rawArgs[0];
      const updatedParams = lam.params.map(p => (p.tsType ? p : { ...p, tsType }));
      return [{ ...lam, params: updatedParams }, ...rawArgs.slice(1)];
    }
  }
  // reduce's callback is (acc, elem): acc from the init arg's type, elem from the array.
  if (fn.kind === "field" && fn.obj.ty.kind === "array" && fn.field === "reduce" && ctx &&
      rawArgs.length >= 2 && rawArgs[0].kind === "lambda" && rawArgs[0].params.length >= 2) {
    const accTs = tyToTsStr(resolveExpr(rawArgs[1], ctx).ty);
    const elemTs = tyToTsStr(fn.obj.ty.elem);
    if (accTs && elemTs) {
      const lam = rawArgs[0];
      const updatedParams = lam.params.map((p, i) =>
        p.tsType || i > 1 ? p : { ...p, tsType: i === 0 ? accTs : elemTs });
      return [{ ...lam, params: updatedParams }, ...rawArgs.slice(1)];
    }
  }
  if (fn.kind === "field" && fn.obj.ty.kind === "array" &&
      ["map", "filter", "every", "some", "find", "findLast", "findIndex", "findLastIndex"].includes(fn.field) &&
      rawArgs.length >= 1 && rawArgs[0].kind === "lambda" &&
      rawArgs[0].params.length >= 1 && !rawArgs[0].params[0].tsType) {
    const elemTy = fn.obj.ty.elem;
    const tsType = tyToTsStr(elemTy);
    if (tsType) {
      const lam = rawArgs[0];
      const updatedParams = [{ ...lam.params[0], tsType }, ...lam.params.slice(1)];
      return [{ ...lam, params: updatedParams }, ...rawArgs.slice(1)];
    }
  }
  // Named-callee propagation: when an argument position expects a function
  // type, infer the lambda's param types from that function type. Aliases
  // (e.g., `Comparator`) are expanded via the typeDecls.
  if (fn.kind === "var" && ctx?.fnParams.has(fn.name)) {
    const paramTys = ctx.fnParams.get(fn.name)!;
    return rawArgs.map((a, i) => {
      if (a.kind !== "lambda" || i >= paramTys.length) return a;
      let pTy = paramTys[i];
      if (pTy.kind === "user") {
        const decl = ctx.typeDecls.find(d => d.name === (pTy as any).name);
        if (decl?.kind === "alias" && decl.aliasOfTy) pTy = decl.aliasOfTy;
        else if (decl?.kind === "alias" && decl.aliasOf) pTy = parseTsType(decl.aliasOf);
      }
      if (pTy.kind !== "fn") return a;
      const updatedParams = a.params.map((p, idx) =>
        p.tsType || idx >= pTy.params.length ? p : { ...p, tsType: tyToTsStr(pTy.params[idx]) });
      return { ...a, params: updatedParams };
    });
  }
  return rawArgs;
}

/** A defined-check filter predicate: `(x) => x !== undefined` (expression or
 *  single-return body). Detected on the raw IR before narrowing rewrites it. */
function isDefinedCheckRawLambda(raw: RawExpr): boolean {
  if (raw.kind !== "lambda" || raw.params.length !== 1) return false;
  const p = raw.params[0].name;
  const body = Array.isArray(raw.body)
    ? (raw.body.length === 1 && raw.body[0].kind === "return" ? raw.body[0].value : null)
    : raw.body;
  if (!body || body.kind !== "binop" || body.op !== "!==") return false;
  const isParam = (x: RawExpr) => x.kind === "var" && x.name === p;
  const isUndef = (x: RawExpr) => x.kind === "var" && x.name === "undefined";
  return (isParam(body.left) && isUndef(body.right)) || (isParam(body.right) && isUndef(body.left));
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
  // `Array.isArray(x)` always returns boolean. narrow.ts recognizes this call as
  // a discriminator predicate when `x` has type of a synthesized array-union.
  if (fn.obj.kind === "var" && fn.obj.name === "Array" && fn.field === "isArray") {
    return { kind: "bool" };
  }
  // Math.* numeric builtins: abs/min/max preserve the operand's numeric type
  // (real if any operand is real); floor/ceil/round/trunc return an integer.
  if (fn.obj.kind === "var" && fn.obj.name === "Math") {
    if (fn.field === "abs" && args.length === 1) return args[0].ty;
    if ((fn.field === "min" || fn.field === "max") && args.length >= 1)
      return args.some(a => a.ty.kind === "real") ? { kind: "real" } : args[0].ty;
    if (["floor", "ceil", "round", "trunc"].includes(fn.field)) return { kind: "int" };
  }
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
    if (fn.field === "pop") return { kind: "optional", inner: objTy.elem };
    if (fn.field === "push" || fn.field === "unshift" || fn.field === "concat") return objTy;
    if (fn.field === "sort") return objTy;
    if (fn.field === "filter") return objTy;
    if (fn.field === "every" || fn.field === "some") return { kind: "bool" };
    if (fn.field === "reduce" && args.length === 2) return args[1].ty;
    if (fn.field === "find" || fn.field === "findLast") return { kind: "optional", inner: objTy.elem };
    if (fn.field === "findIndex" || fn.field === "findLastIndex") return { kind: "int" };
    if (fn.field === "flat" && objTy.elem.kind === "array") return { kind: "array", elem: objTy.elem.elem };
    if (fn.field === "slice") return objTy;
    if (fn.field === "join" && objTy.elem.kind === "string") return { kind: "string" };
    if (fn.field === "map" && args.length >= 1 && args[0].kind === "lambda") {
      const lam = args[0];
      // Prefer the lambda's declared return type (handles multi-statement bodies
      // where body[0] is an `if`, not a `return`); fall back to the body's return.
      const retTy: Ty = lam.ty.kind === "fn" ? lam.ty.result
        : lam.body.length > 0 && lam.body[0].kind === "return" ? lam.body[0].value.ty : { kind: "unknown" };
      return { kind: "array", elem: retTy };
    }
  } else if (objTy.kind === "string") {
    if (fn.field === "trim" || fn.field === "trimEnd" || fn.field === "trimStart" || fn.field === "toLowerCase" || fn.field === "toUpperCase") return { kind: "string" };
    if (fn.field === "slice" || fn.field === "substring") return { kind: "string" };
    if (fn.field === "split") return { kind: "array", elem: { kind: "string" } };
    if (fn.field === "includes" || fn.field === "startsWith" || fn.field === "endsWith") return { kind: "bool" };
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

// Fresh-binder counter for the someMatches synthesized by object-spread merge.
let mergeBinder = 0;

/** Expand `{ ...base, ...override }` into a faithful field-wise merge. Driven by
 *  the result record type's fields: an override field wins when present, else the
 *  base's field shows through. Optional fields decide presence at runtime
 *  (`Some?`); an `Option`-typed override is the whole merge guarded by its tag. */
function resolveRecordMerge(base: RawExpr, override: RawExpr, ctx: Ctx): TExpr {
  const tbase = resolveExpr(base, ctx);
  const tover = resolveExpr(override, ctx);
  const overInner = tover.ty.kind === "optional" ? tover.ty.inner : tover.ty;
  // Result record type: prefer the override's (an optional override still merges
  // into its inner type), else the base's.
  const rTy = overInner.kind === "user" ? overInner
            : tbase.ty.kind === "user" ? tbase.ty : null;
  const decl = rTy ? ctx.typeDecls.find(d => d.name === rTy.name && d.kind === "record") : undefined;
  if (!rTy || !decl?.fields) {
    throw new Error(`object spread merge { ...a, ...b } needs a known record type for both operands ` +
      `(base: ${tyToCanonical(tbase.ty)}, override: ${tyToCanonical(tover.ty)})`);
  }
  if (tbase.ty.kind === "optional") {
    throw new Error(`object spread merge with an optional base operand is not supported (base: ${tyToCanonical(tbase.ty)})`);
  }
  const userTy = rTy;
  const fields = decl.fields;
  // Build the merged literal from concrete base/override values, both : userTy.
  const merged = (bv: TExpr, ov: TExpr): TExpr => ({
    kind: "record", spread: null, ty: userTy,
    fields: fields.map(f => {
      const ft = f.type!;
      const ovf: TExpr = { kind: "field", obj: ov, field: f.name, ty: ft };
      if (ft.kind !== "optional") return { name: f.name, value: ovf };  // required: override always provides
      // optional: override field wins iff present, else base's field
      const bvf: TExpr = { kind: "field", obj: bv, field: f.name, ty: ft };
      const binder = freshName(`_m${mergeBinder++}`);
      // someBody is the unwrapped present value; transform re-wraps each arm in
      // the backend's Some constructor (Dafny `Some`, Lean `Option.some`).
      return { name: f.name, value: {
        kind: "someMatch", scrutinee: ovf, binder, binderTy: ft.inner,
        someBody: { kind: "var", name: binder, ty: ft.inner }, noneBody: bvf, ty: ft,
      } };
    }),
  });
  if (tover.ty.kind === "optional") {
    // override may be absent (undefined spreads nothing) → base unchanged
    const binder = freshName(`_mo${mergeBinder++}`);
    return {
      kind: "someMatch", scrutinee: tover, binder, binderTy: userTy,
      someBody: merged(tbase, { kind: "var", name: binder, ty: userTy }), noneBody: tbase, ty: userTy,
    };
  }
  return merged(tbase, tover);
}

/** `rec[k]` where `rec` is a record and `k` an enum of its field names. A *named*
 *  string-union key is a datatype → `match k { case f => rec.f }`; an *inline*
 *  union (`"a" | "b"`, a bare string carrying its members) → an equality chain
 *  `if k === "a" then rec.a else …`. Either way the chain/match covers exactly
 *  the key's values, so a subset key stays sound. Returns null if the shape
 *  doesn't apply (caller falls back to plain index). */
function tryRecordIndexByEnum(obj: TExpr, idx: TExpr, ctx: Ctx): TExpr | null {
  const objTy = obj.ty, keyTy = idx.ty;
  if (objTy.kind !== "user") return null;
  const rec = ctx.typeDecls.find(d => d.name === objTy.name && d.kind === "record");
  if (!rec?.fields) return null;
  const fieldByName = new Map(rec.fields.map(f => [f.name, f]));
  const fieldTy = (v: string): Ty => fieldByName.get(v)!.type ?? { kind: "unknown" };
  const field = (v: string): TExpr => ({ kind: "field", obj, field: v, ty: fieldTy(v) });

  // The key's members, and whether it's a datatype (named) or a bare string (inline).
  let values: string[] | null = null;
  let datatype: string | null = null;
  if (keyTy.kind === "user") {
    const keyEnum = ctx.typeDecls.find(d => d.name === keyTy.name && d.kind === "string-union");
    if (keyEnum?.values?.length) { values = keyEnum.values; datatype = keyEnum.name; }
  } else if (keyTy.kind === "string" && keyTy.values?.length) {
    values = keyTy.values;
  }
  if (!values || !values.every(v => fieldByName.has(v))) return null;  // key isn't a subset of fields

  if (datatype) {
    return {
      kind: "tagMatch", scrutinee: idx, typeName: datatype,
      cases: values.map(v => ({ variant: v, body: field(v) })), fallthrough: null, ty: fieldTy(values[0]),
    };
  }
  // Inline union: fold right into an equality chain, last member as the bare else.
  let expr: TExpr = field(values[values.length - 1]);
  for (let i = values.length - 2; i >= 0; i--) {
    expr = {
      kind: "conditional", ty: fieldTy(values[i]), then: field(values[i]), else: expr,
      cond: { kind: "binop", op: "===", left: idx, right: { kind: "str", value: values[i], ty: { kind: "string" } }, ty: { kind: "bool" } },
    };
  }
  return expr;
}

function resolveExpr(e: RawExpr, ctx: Ctx): TExpr {
  switch (e.kind) {
    case "var":
      if (e.name === "undefined") return { kind: "var", name: "undefined", ty: { kind: "void" } };
      return { kind: "var", name: e.name, ty: lookup(ctx.env, e.name) ?? { kind: "unknown" } };

    case "num":
      if (!Number.isInteger(e.value)) return { kind: "num", value: e.value, ty: { kind: "real" } };
      if (e.big) return { kind: "num", value: e.value, ty: { kind: "int", big: true } };
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
        // Spec (`//@`) comparisons are proof-only, so they can't diverge at
        // runtime; only warn on executable code.
        if (!ctx.inSpec && refEqHazard(left.ty, ctx.typeDecls) && refEqHazard(right.ty, ctx.typeDecls)) {
          warnRefEq(e.op, left.ty, right.ty);
        }
      }
      let ty: Ty = { kind: "unknown" };
      // <==> is bool like the comparisons; unlike ==>, neither side narrows
      // the other (no premise to assume).
      if (["===", "!==", ">=", "<=", ">", "<", "in", "<==>"].includes(e.op)) ty = { kind: "bool" };
      else if (e.op === "&&") ty = right.ty;
      else if (e.op === "||" && left.ty.kind === "optional") {
        // || undefined is identity for optionals — keep the optional type
        ty = (e.right.kind === "var" && e.right.name === "undefined") ? left.ty : left.ty.inner;
      }
      else if (e.op === "||") ty = right.ty;
      else if (e.op === "/") {
        // `number / number` is real (floating-point) division: 3 / 2 === 1.5,
        // never 1 — an integer quotient requires an explicit Math.floor (which
        // lowers to JSFloorDiv). But `bigint / bigint` is genuinely integer
        // division in JS (3n / 2n === 1n), so keep it integer.
        ty = (isBigInt(left.ty) || isBigInt(right.ty)) ? { kind: "int", big: true } : { kind: "real" };
      }
      else if (["+", "-", "*", "%"].includes(e.op)) {
        ty = (left.ty.kind === "real" || right.ty.kind === "real") ? { kind: "real" } : left.ty;
      }
      return { kind: "binop", op: e.op, left, right, ty };
    }

    case "unop": {
      const expr = resolveExpr(e.expr, ctx);
      const ty: Ty = e.op === "!" ? { kind: "bool" } : e.op === "typeof" ? { kind: "string" } : expr.ty;
      return { kind: "unop", op: e.op, expr, ty };
    }

    case "call": {
      // perm(a, b): spec-only permutation predicate — true iff `a` and `b` are
      // reorderings of each other (equal as multisets). Lowers to the `Perm`
      // preamble (Dafny `multiset(a) == multiset(b)`; Lean `a.toList ~ b.toList`).
      // It has no runtime counterpart, so it is rejected outside `//@` specs.
      if (e.fn.kind === "var" && e.fn.name === "perm" && e.args.length === 2) {
        if (!ctx.inSpec) throw new Error("perm(a, b) may only be used in //@ specifications");
        const a = resolveExpr(e.args[0], ctx);
        const b = resolveExpr(e.args[1], ctx);
        if (a.ty.kind !== "array" || b.ty.kind !== "array")
          throw new Error(`perm(a, b) requires two array arguments (got ${a.ty.kind} and ${b.ty.kind})`);
        const fn: TExpr = { kind: "var", name: "Perm", ty: { kind: "unknown" } };
        return { kind: "call", fn, args: [a, b], ty: { kind: "bool" }, callKind: "pure" };
      }
      // new Set(arr): build a deduplicated set from the array's elements (extract
      // marks the array form `__setFromArray`). Lowers to the SetFromSeq preamble
      // (Dafny `set x | x in s`); size/membership are then set semantics.
      if (e.fn.kind === "var" && e.fn.name === "__setFromArray" && e.args.length === 1) {
        const arr = resolveExpr(e.args[0], ctx);
        if (arr.ty.kind !== "array")
          throw new Error(`new Set(...) expects an array argument (got ${arr.ty.kind})`);
        const fn: TExpr = { kind: "var", name: "SetFromSeq", ty: { kind: "unknown" } };
        return { kind: "call", fn, args: [arr], ty: { kind: "set", elem: arr.ty.elem }, callKind: "pure" };
      }
      // Extern dispatch: `NS.method(args)` where NS.method is declared via
      // `//@ extern`. Rewrite into a flat-name call (`NS_method(args)`) so the
      // rest of the pipeline sees an ordinary pure function. The extern's
      // declaration is emitted alongside the file as `function {:axiom} ...`.
      if (e.fn.kind === "field" && e.fn.obj.kind === "var") {
        const qualified = `${e.fn.obj.name}.${e.fn.field}`;
        const ext = ctx.externs.get(qualified);
        if (ext) {
          const args = e.args.map(a => resolveExpr(a, ctx));
          const fn: TExpr = { kind: "var", name: ext.flat, ty: { kind: "unknown" } };
          return { kind: "call", fn, args, ty: ext.returnTy, callKind: "pure" };
        }
      }
      const fn = resolveExpr(e.fn, ctx);
      const rawArgs = inferLambdaParamTypes(fn, e.args, ctx);
      // For .push() on a typed array, resolve args with element type context
      let argCtx = ctx;
      if (fn.kind === "field" && fn.obj.ty.kind === "array" && fn.field === "push" &&
          fn.obj.ty.elem.kind === "user") {
        argCtx = { ...ctx, returnTy: fn.obj.ty.elem };
      }
      // Propagate parameter types to arguments for record literal resolution
      // (enables inline discriminated union construction in function arguments)
      const paramTypes = fn.kind === "var" && ctx.fnParams.has(fn.name) ? ctx.fnParams.get(fn.name)! : null;
      let args = coerceCallArgs(rawArgs.map((a, i) => {
        let aCtx = argCtx;
        if (paramTypes && i < paramTypes.length && paramTypes[i].kind === "user") {
          aCtx = { ...aCtx, returnTy: paramTypes[i] };
        }
        return resolveExpr(a, aCtx);
      }), fn, ctx);
      // Array method `.with(i, v)`: coerce the value arg to the element type
      // so `arr[i] = v` on `(T|null)[]` wraps `T` → `Some(T)` (and similarly
      // for synth array-unions). Same shape as the record-field coercion
      // below: assigning a narrower value into a wider slot.
      if (fn.kind === "field" && fn.field === "with" && fn.obj.ty.kind === "array" && args.length === 2) {
        args = [args[0], coerceToTargetTy(args[1], fn.obj.ty.elem, ctx.typeDecls)];
      }
      let ty = inferMethodReturnTy(fn, args, ctx);
      // For same-file function calls, use the known return type
      if (ty.kind === "unknown" && fn.kind === "var" && ctx.fnReturns.has(fn.name)) {
        ty = ctx.fnReturns.get(fn.name)!;
      }
      // filterMap: `seqOfOption.filter(x => x !== undefined)` (a defined-check,
      // typically with an `x is T` type guard) drops the Nones AND unwraps to
      // seq<T>. Rewrite to a synthetic `filterSome` call lowered to the proven
      // SeqFilterSome preamble (a plain `Map(.value, Filter(.Some?))` wouldn't
      // verify — `.value` is partial).
      if (e.fn.kind === "field" && e.fn.field === "filter" && e.args.length === 1
          && isDefinedCheckRawLambda(e.args[0])
          && fn.kind === "field" && fn.obj.ty.kind === "array" && fn.obj.ty.elem.kind === "optional") {
        return { kind: "call", fn: { ...fn, field: "filterSome" }, args: [], ty: { kind: "array", elem: fn.obj.ty.elem.inner }, callKind: "method" };
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
      } else if (obj.ty.kind === "tuple") {
        // Tuple projection: the position must be a literal — a tuple has a
        // distinct type per slot, so a runtime index has no single result type
        // and no backend projection (`t.0`/`t.1`) exists for it.
        const elems = obj.ty.elems;
        if (idx.kind !== "num" || !Number.isInteger(idx.value) || idx.value < 0 || idx.value >= elems.length) {
          throw new Error(`tuple index must be an integer literal in [0, ${elems.length}); got ${tyToCanonical(idx.ty)} index into ${tyToCanonical(obj.ty)}`);
        }
        idxTy = elems[idx.value];
      } else if (obj.ty.kind === "map") {
        const objPath = asTExprAccessPath(obj);
        const idxPath = asTExprAccessPath(idx);
        const narrowed = objPath && idxPath && ctx.narrowedIndices.some(
          n => accessPathsEqual(n.obj, objPath) && accessPathsEqual(n.idx, idxPath)
        );
        idxTy = narrowed ? obj.ty.value : { kind: "optional" as const, inner: obj.ty.value };
      } else {
        const recIdx = tryRecordIndexByEnum(obj, idx, ctx);
        if (recIdx) return recIdx;
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
      const ty: Ty = left.ty.kind === "optional" ? left.ty.inner : left.ty;
      // The default shares the result type, so coerce a string literal to a
      // string-union enum (e.g. `availableLevels[0] ?? "off"`).
      const right = coerceStr(resolveExpr(e.right, ctx), ty);
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
          // Build a fake fn TExpr from prev steps to reuse inferMethodReturnTy
          // and inferLambdaParamTypes — without the latter, a lambda arg buried
          // inside `obj?.filter(r => ...)` gets `int`-typed params instead of
          // the array's element type.
          const lastField = chain.length > 0 && chain[chain.length - 1].kind === "field"
            ? chain[chain.length - 1] as { kind: "field"; name: string; ty: Ty } : null;
          let callTy: Ty = { kind: "unknown" };
          let callKind: CallKind = "unknown";
          let rawArgs = step.args;
          if (lastField) {
            const priorInTy = chain.length >= 2 ? chain[chain.length - 2].ty
              : (obj.ty.kind === "optional" ? obj.ty.inner : obj.ty);
            const fakeObj: TExpr = { kind: "var", name: "_chain_recv", ty: priorInTy };
            const fakeFn: TExpr = { kind: "field", obj: fakeObj, field: lastField.name, ty: lastField.ty };
            rawArgs = inferLambdaParamTypes(fakeFn, rawArgs);
            const args = rawArgs.map(a => resolveExpr(a, ctx));
            callTy = inferMethodReturnTy(fakeFn, args, ctx);
            callKind = "method";
            chain.push({ kind: "call", args, ty: callTy, callKind });
            stepInTy = callTy;
            continue;
          }
          const args = rawArgs.map(a => resolveExpr(a, ctx));
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
      // Record literal in map-typed context (e.g. `const M: Record<string, V> = {a: ...}`):
      // attach the map type so transform/emit can produce a map literal.
      if (!spread && ctx.returnTy.kind === "map") {
        const mapTy = ctx.returnTy;
        const fieldCtx = { ...ctx, returnTy: mapTy.value };
        const fields = e.fields.map(f => ({ name: f.name, value: resolveExpr(f.value, fieldCtx) }));
        return { kind: "record", spread: null, fields, ty: mapTy };
      }
      // Infer record type: from spread, or from return type context. Unwrap
      // an outer Optional when looking at returnTy — `return {...} : null`
      // has ctx.returnTy = Option<T>, but the record literal's natural type is T.
      const returnTyUnwrapped = ctx.returnTy.kind === "optional" ? ctx.returnTy.inner : ctx.returnTy;
      const recordTy = ty.kind === "user" ? ty : returnTyUnwrapped.kind === "user" ? returnTyUnwrapped : null;
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
          // Assignment-position upcasts: T → Option<T>, T[] → ArrayBranch(T[]),
          // U → NonArrayBranch(U). Handles both optional fields and fields
          // typed as a synth array-union (`T[] | U`).
          value = coerceToTargetTy(value, declTy, ctx.typeDecls);
        }
        return { name: f.name, value };
      });
      return { kind: "record", spread, fields, ty: recordTy ?? ty };
    }

    case "recordMerge":
      return resolveRecordMerge(e.base, e.override, ctx);

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
      // Expected-tuple context: type each element against its own slot type and
      // produce a tuple literal (`[1, "a"]: [number, string]`).
      if (ctx.returnTy.kind === "tuple") {
        const slots = ctx.returnTy.elems;
        const elems = e.elems.map((el, i) => {
          const slot = slots[i];
          const r = resolveExpr(el, slot ? { ...ctx, returnTy: slot } : ctx);
          return slot ? coerceStr(r, slot) : r;
        });
        return { kind: "arrayLiteral", elems, ty: { kind: "tuple", elems: elems.map(x => x.ty) } };
      }
      // Thread the expected element type into each element, so a record/union
      // literal in an array resolves to its named datatype rather than an
      // anonymous tuple (mirrors return-position and call-argument records, which
      // get their type via ctx.returnTy). Only narrow when the context type is an
      // array; otherwise leave ctx untouched.
      const expectedElem = ctx.returnTy.kind === "array" ? ctx.returnTy.elem : null;
      const elemCtx = expectedElem ? { ...ctx, returnTy: expectedElem } : ctx;
      const elems = e.elems.map(el => {
        const r = resolveExpr(el, elemCtx);
        // Coerce a bare string-literal element to a string-union enum (e.g.
        // `["off", …]: ModelThinkingLevel[]`), like return/arg positions.
        return expectedElem ? coerceStr(r, expectedElem) : r;
      });
      const elemTy: Ty = elems.length > 0 ? elems[0].ty : { kind: "unknown" };
      // No expected collection type: infer array vs tuple from the elements —
      // heterogeneous element types can't be a homogeneous seq, so they form a
      // tuple (`[1, "a"]` → `(int, string)`); otherwise a seq.
      if (!expectedElem && elems.length >= 2 && !elems.every(x => tyEqual(x.ty, elemTy))) {
        return { kind: "arrayLiteral", elems, ty: { kind: "tuple", elems: elems.map(x => x.ty) } };
      }
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
      // Set returnTy to the lambda's own return annotation (not the enclosing
      // function's), so return-position record literals in the body resolve to
      // their named type rather than an anonymous tuple.
      const lambdaReturnTy: Ty = e.returnTsType ? parseTsType(e.returnTsType) : { kind: "unknown" };
      const lambdaCtx = { ...withEnv(ctx, lambdaEnv), inLambda: true, returnTy: lambdaReturnTy };
      // Body: expression (wrap in return stmt) or statement block
      const body = Array.isArray(e.body)
        ? resolveBlock(e.body, lambdaCtx)
        : [{ kind: "return" as const, value: resolveExpr(e.body, lambdaCtx) }];
      // Carry the lambda's type as a fn type when its return is known, so chained
      // array methods (`.map(...).filter(...)`) can infer downstream element types.
      const lamTy: Ty = e.returnTsType
        ? { kind: "fn", params: params.map(p => p.ty), result: lambdaReturnTy }
        : { kind: "unknown" };
      return { kind: "lambda", params, body, ty: lamTy };
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
      } else if (then_.ty.kind === "optional" && else_.ty.kind !== "optional" && else_.ty.kind !== "unknown") {
        // Asymmetric optional: one branch returns Option<T>, the other returns T.
        // Widen to Option<T> so callers/return-coercion see the wider type.
        ty = then_.ty;
      } else if (else_.ty.kind === "optional" && then_.ty.kind !== "optional" && then_.ty.kind !== "unknown") {
        ty = else_.ty;
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
    // Any terminator counts (return/throw/break/continue — same set as narrow's
    // isTerminating): each exits the current block, so the rest of the block
    // only runs when the guard was false.
    // Field chains are excluded — resolve can't substitute in statement lists;
    // transform's emitOptionalMatch handles field chains in statement contexts.
    if (s.kind === "if" && s.then.length > 0 && isTerminatorKind(s.then[s.then.length - 1].kind) && s.else.length === 0) {
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
      // No source annotation → infer type from initializer (resolved first).
      if (s.tsType === null) {
        const init = resolveExpr(s.init, ctx);
        const ty = init.ty;
        const mutable = s.mutable || isRefMutableInTS(ty);
        return [{ kind: "let", name: s.name, ty, mutable, init }, extend(ctx.env, s.name, ty)];
      }
      // expandAlias unwraps an array/collection alias (`type Board = number[]`)
      // to its underlying type, so array methods / index-assignment on the
      // local dispatch correctly (params get the same treatment, see makeParams).
      const declTy = expandAlias(resolveTsType(s.tsType, ctx.overrides, s.name), ctx.typeDecls);
      // Propagate declared type as returnTy so nested record expressions resolve
      // union variants correctly (e.g., EffectState → mode: EffectMode → { kind:
      // 'Idle' }). Arrays too, so `const xs: Foo[] = [{...}]` threads the element
      // type into the array literal (see the arrayLiteral case).
      const initCtx = (declTy.kind === "user" || declTy.kind === "array") ? { ...ctx, returnTy: declTy } : ctx;
      const init = coerceStr(resolveExpr(s.init, initCtx), declTy);
      let ty: Ty;
      if (isUnmodeledTy(declTy, ctx.typeDecls) && !isUnmodeledTy(init.ty, ctx.typeDecls)) {
        // ts-morph's declared type is opaque to us (an expanded union it made
        // by inlining an alias we shadow via declare-type, or any-laden), but
        // LS resolved the initializer to something concrete. Take the structure
        // from `init.ty`, keeping only the optionality ts-morph reported.
        ty = declTy.kind === "optional" && init.ty.kind !== "optional"
          ? { kind: "optional", inner: init.ty }
          : init.ty;
      } else if (declTy.kind === "string" && isStringUnionTy(init.ty, ctx.typeDecls) && !ctx.overrides.has(s.name)) {
        // ts-morph widened a string-union to `string`; keep the initializer's
        // datatype so `local === "lit"` lowers to a discriminant test.
        ty = init.ty;
      } else if ((declTy.kind === "int" || declTy.kind === "nat") && init.ty.kind === "real" && !ctx.overrides.has(s.name)) {
        // TS infers `number` (→ int/nat) for an expression LS computes as `real`
        // (e.g. `a / b`, now real division). `number` can't tell them apart, so
        // trust the real-valued initializer — unless the user pinned the type.
        ty = init.ty;
      } else {
        // Map indexing: TS says T, but access can fail → use Optional<T> from init
        ty = (declTy.kind !== "optional" && init.ty.kind === "optional") ? init.ty : declTy;
      }
      // const collections are mutable in value-semantics world (TS mutates in place, Dafny/Lean reassign)
      const mutable = s.mutable || isRefMutableInTS(ty);
      return [{ kind: "let", name: s.name, ty, mutable, init }, extend(ctx.env, s.name, ty)];
    }

    case "assign": {
      const targetTy = lookup(ctx.env, s.target) ?? { kind: "unknown" as const };
      let value = coerceStr(resolveExpr(s.value, ctx), targetTy);
      // Auto-wrap non-optional value in Some when target is optional
      const isUndef = value.kind === "var" && value.name === "undefined";
      if (targetTy.kind === "optional" && value.ty.kind !== "optional" && value.ty.kind !== "unknown" && !isUndef) {
        value = wrapSome(value, targetTy);
      }
      return [{ kind: "assign", target: s.target, value }, ctx.env];
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
      } else if (s.names.length >= 2 && iterable.ty.kind === "array" && iterable.ty.elem.kind === "tuple") {
        // Array of tuples: bind each name to its slot type.
        const elems = iterable.ty.elem.elems;
        for (let i = 0; i < s.names.length; i++) nameTypes.push(elems[i] ?? { kind: "unknown" });
      } else {
        // General tuple destructuring: all unknown
        for (const _ of s.names) nameTypes.push({ kind: "unknown" });
      }
      // Must match the freshened counter transform mints for this loop, so a
      // spec referencing the loop index resolves to the same name.
      const idxName = freshName(`_${s.names[0]}_idx`);
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
      return [{ kind: "assert", expr, assumed: s.assumed }, ctx.env];
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
    case "recordMerge":
      collectCallsExpr(e.base, fns, out);
      collectCallsExpr(e.override, fns, out);
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
  externs: Map<string, { flat: string; params: Ty[]; returnTy: Ty }> = new Map(),
  moduleConstants: Map<string, Ty> = new Map(),
  opts?: { thisBinding?: { name: string; ty: Ty }; forcePure?: boolean }
): TFunction {

  const overrides = new Map(fn.typeAnnotations.map(a => [a.name, a.type]));
  const params: TParam[] = fn.params.map(p => ({ name: p.name, ty: expandAlias(resolveTsType(p.tsType, overrides, p.name), typeDecls) }));
  const returnTy = expandAlias(resolveTsType(fn.returnType, overrides, "\\result"), typeDecls);

  let env: Env | null = null;
  // Module-level constants are in scope for every function body. Added before
  // params so a param named the same as a const would shadow it (param wins).
  for (const [name, ty] of moduleConstants) env = extend(env, name, ty);
  if (opts?.thisBinding) env = extend(env, opts.thisBinding.name, opts.thisBinding.ty);
  for (const p of params) env = extend(env, p.name, p.ty);

  const baseCtx: Ctx = { env, typeDecls, overrides, allowResult: false, returnTy, pureFns, fnParams, fnReturns, externs, inSpec: false, inLambda: false, narrowedPaths: [], narrowedIndices: [] };
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
    autohavoc: fn.autohavoc,
    body: resolveBlock(fn.body, bodyCtx),
  };
}

function resolveClass(cls: import("./rawir.js").RawClass, typeDecls: TypeDeclInfo[], pureFns: Set<string>, fnParams: Map<string, Ty[]> = new Map(), fnReturns: Map<string, Ty> = new Map(), externs: Map<string, { flat: string; params: Ty[]; returnTy: Ty }> = new Map(), moduleConstants: Map<string, Ty> = new Map()): import("./typedir.js").TClass {
  const fields = cls.fields.map(f => ({ name: f.name, ty: parseTsType(f.tsType) }));
  // Create a synthetic record type for 'this' so field access resolves
  const thisType: Ty = { kind: "user", name: cls.name };
  const thisDecl: TypeDeclInfo = { name: cls.name, kind: "record", fields: cls.fields.map(f => ({ name: f.name, tsType: f.tsType, type: parseTsType(f.tsType) })) };
  const allTypeDecls = [...typeDecls, thisDecl];

  const methods = cls.methods.map(fn =>
    resolveFunction(fn, allTypeDecls, pureFns, fnParams, fnReturns, externs, moduleConstants, {
      thisBinding: { name: "this", ty: thisType },
      forcePure: false,  // class methods are never pure (they access this)
    })
  );

  return { name: cls.name, fields, methods };
}

/** Pre-compute Ty on all TypeDeclInfo fields/variants/aliases.
 *  Called once per module so consumers can read field.type instead of re-parsing tsType. */
function precomputeFieldTypes(typeDecls: TypeDeclInfo[]) {
  precomputeFieldTypesInner(typeDecls);
  // Expand alias references inside record/variant field types so downstream
  // code doesn't have to follow `user("Ruleset")` indirection at every lookup.
  for (const d of typeDecls) {
    if (d.fields) for (const f of d.fields) if (f.type) f.type = expandAlias(f.type, typeDecls);
    if (d.variants) for (const v of d.variants) for (const f of v.fields) if (f.type) f.type = expandAlias(f.type, typeDecls);
  }
}

function precomputeFieldTypesInner(typeDecls: TypeDeclInfo[]) {
  for (const d of typeDecls) {
    if (d.fields) for (const f of d.fields) f.type = parseTsType(f.tsType);
    if (d.variants) for (const v of d.variants) for (const f of v.fields) f.type = parseTsType(f.tsType);
    if (d.aliasOf && !d.aliasOfTy) d.aliasOfTy = parseTsType(d.aliasOf);
  }
}

export function resolveModule(raw: RawModule): TModule {
  _warnedRefEq.clear();
  precomputeFieldTypes(raw.typeDecls);
  const pureFns = computePureFns(raw.functions);
  // Pre-compute function parameter and return types
  const fnParams = new Map<string, Ty[]>();
  const fnReturns = new Map<string, Ty>();
  for (const fn of raw.functions) {
    const overrides = new Map(fn.typeAnnotations.map(a => [a.name, a.type]));
    fnParams.set(fn.name, fn.params.map(p => expandAlias(resolveTsType(p.tsType, overrides, p.name), raw.typeDecls)));
    fnReturns.set(fn.name, expandAlias(resolveTsType(fn.returnType, overrides, "\\result"), raw.typeDecls));
  }
  // Externs: resolve param/return types once. For bare-name externs (no dot),
  // also register in fnReturns so ordinary `foo(args)` calls get the right
  // return type at resolution; dotted externs are handled in resolveExpr's
  // call case via the externs map directly.
  const externs = new Map<string, { flat: string; params: Ty[]; returnTy: Ty }>();
  // First pass: register signatures so spec resolution (below) can reference
  // them — including the extern referring to itself, or specs that mention
  // sibling externs.
  for (const ext of raw.externs ?? []) {
    const params = ext.params.map(p => parseTsType(p.tsType));
    const returnTy = parseTsType(ext.returnType);
    externs.set(ext.qualified, { flat: ext.flat, params, returnTy });
    if (!ext.qualified.includes(".")) fnReturns.set(ext.qualified, returnTy);
  }
  // Second pass: resolve the lifted `requires`/`ensures` strings in each
  // extern's own param scope. `\result` is in scope under `ensures`.
  const tExterns = (raw.externs ?? []).map(ext => {
    const sig = externs.get(ext.qualified)!;
    let env: Env | null = null;
    for (let i = 0; i < ext.params.length; i++) {
      env = extend(env, ext.params[i].name, sig.params[i]);
    }
    const baseCtx: Ctx = { env, typeDecls: raw.typeDecls, overrides: new Map(), allowResult: false, returnTy: sig.returnTy, pureFns, fnParams, fnReturns, externs, inSpec: true, inLambda: false, narrowedPaths: [], narrowedIndices: [] };
    const ensuresCtx: Ctx = { ...baseCtx, env: extend(env, "\\result", sig.returnTy), allowResult: true };
    const requires = ext.requires.map(s => {
      try { return resolveSpec(s, baseCtx); } catch { return null; }
    }).filter((e): e is TExpr => e !== null);
    const ensures = ext.ensures.map(s => {
      try { return resolveSpec(s, ensuresCtx); } catch { return null; }
    }).filter((e): e is TExpr => e !== null);
    return {
      qualified: ext.qualified,
      flat: ext.flat,
      typeParams: ext.typeParams,
      params: ext.params.map((p, i) => ({ name: p.name, ty: sig.params[i] })),
      returnTy: sig.returnTy,
      requires,
      ensures,
    };
  });
  const emptyCtx: Ctx = { env: null, typeDecls: raw.typeDecls, overrides: new Map(), allowResult: false, returnTy: { kind: "int" }, pureFns, fnParams, fnReturns, externs, inSpec: false, inLambda: false, narrowedPaths: [], narrowedIndices: [] };
  const constants = (raw.constants ?? []).map(c => {
    const ty = expandAlias(parseTsType(c.tsType), raw.typeDecls);
    // Propagate the declared type into the value's resolution context so that
    // record literals on map-typed constants (e.g. `Record<string, number>`)
    // get their `ty` set to `map<...>` rather than `user("...")`.
    const valueCtx: Ctx = { ...emptyCtx, returnTy: ty };
    return { name: c.name, ty, value: resolveExpr(c.value, valueCtx) };
  });
  const moduleConstants = new Map<string, Ty>(constants.map(c => [c.name, c.ty]));

  return {
    file: raw.file,
    typeDecls: raw.typeDecls,
    externs: tExterns,
    constants,
    functions: raw.functions.map(fn => resolveFunction(fn, raw.typeDecls, pureFns, fnParams, fnReturns, externs, moduleConstants)),
    classes: (raw.classes ?? []).map(cls => resolveClass(cls, raw.typeDecls, pureFns, fnParams, fnReturns, externs, moduleConstants)),
  };
}
