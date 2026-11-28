/**
 * Resolve — Raw IR → Typed IR.
 *
 * Uses linked environments (Scheme-style) for lexical scoping.
 * No mutation — each let extends the chain, lookup walks it.
 */

import type { RawExpr, RawStmt, RawFunction, RawModule } from "./rawir.js";
import type { Ty, TExpr, TStmt, TFunction, TModule, TParam, CallKind } from "./typedir.js";
import { isBigInt, optAbsent, tyEqual, isTerminatorKind } from "./typedir.js";
import { parseTsType, tyToCanonical } from "./types.js";
import type { TypeDeclInfo } from "./types.js";
import { parseExpr } from "./specparser.js";
import { freshName } from "./names.js";
import { recognizeBuiltin, builtinSpec, callbackArgumentTypes, callbackBaseArity } from "./builtins.js";
import { declOf, declOfKind, declOfDotted, declOfTy, tyBaseName, remainingVariant } from "./typedecls.js";
import { presentFact, variantFact, isArrayFact, typeofStringFact, excludesUndefined } from "./condition-facts.js";

// ── Environment ──────────────────────────────────────────────

interface Env {
  name: string;
  ty: Ty;
  /** Original declared storage type before flow narrowing (preserved across `refine`). */
  storageTy?: Ty;
  parent: Env | null;
  /** Callback bindings are lexical, so a nested declaration shadows them in
   *  exactly the same way as ordinary parameters. */
  onRead?: () => void;
  /** Hygienic backend name when a parameter is referenced before initialization. */
  emittedName?: string;
  value?: TExpr;
  argumentPack?: { length: number; at: (index: number) => TExpr };
}

function binding(env: Env | null, name: string): Env | undefined {
  if (!env) return undefined;
  return env.name === name ? env : binding(env.parent, name);
}

function lookup(env: Env | null, name: string): Ty | undefined {
  if (!env) return undefined;
  return env.name === name ? env.ty : lookup(env.parent, name);
}

function storageLookup(env: Env | null, name: string): Ty | undefined {
  const entry = binding(env, name);
  return entry ? (entry.storageTy ?? entry.ty) : undefined;
}

function extend(env: Env | null, name: string, ty: Ty): Env {
  return { name, ty, storageTy: ty, parent: env };
}
/** A quantified variable that reuses the name of a binding in scope is emitted
 *  under a fresh name, so no later pass confuses it with that binding. */
function quantified(env: Env | null, name: string, ty: Ty): Env {
  const frame = extend(env, name, ty);
  if (binding(env, name)) frame.emittedName = freshName(name);
  return frame;
}
/** Shadow a binding with a narrowed type, keeping its callback state.
 *  Dropping that state would let the body reference a renamed parameter by its
 *  source name, which can silently bind an outer variable. The spread is exact
 *  because refine always follows a read of the same variable, and that read is
 *  what sets `emittedName`; the `argumentPack`/`value` getters are evaluated
 *  once, but they belong to rest and beyond-arity frames, whose types (`unknown`,
 *  `void`) are never narrowed. */
function refine(env: Env | null, name: string, ty: Ty): Env {
  let entry = binding(env, name);
  if (!entry) for (let e = env; e; e = e.parent) {
    if (e.emittedName === name) { entry = e; break; }
  }
  return { ...entry, name: entry?.name ?? name, ty, storageTy: entry?.storageTy ?? entry?.ty ?? ty, parent: env };
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
  if (e.kind === "result") return { rootVar: "\\result", fields: [] };
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
  variant?: string;   // union variant the path is narrowed to (discriminant check)
}

/** A `k in m` atom known to hold in the current scope. Both sides are pure
 *  access paths (var or field chain) so we can compare by path equality.
 *  Produced by scanning function requires, enclosing `if (k in m)` branches,
 *  `//@ assert k in m` statements, and while-loop invariants. Consumed in
 *  the `index` case of `resolveExprInner` to return `obj.ty.value` (non-optional)
 *  instead of `Option<V>` when the access is provably safe. */
interface NarrowedIndex {
  obj: AccessPath;
  idx: AccessPath;
}

interface ExternSignature {
  flat: string;
  params: Ty[];
  returnTy: Ty;
  impure: boolean;
}

interface Ctx {
  env: Env | null;
  typeDecls: TypeDeclInfo[];
  typeParams: ReadonlySet<string>;  // function/extern generic type parameter names in scope
  overrides: Map<string, string>;
  allowResult: boolean;
  returnTy: Ty;
  pureFns: Set<string>;  // names of pure functions in this module
  fnParams: Map<string, Ty[]>;  // function name → parameter types
  fnReturns: Map<string, Ty>;  // function name → return type
  externs: Map<string, ExternSignature>;  // qualified name → declared signature (from `//@ extern`)
  inSpec: boolean;
  inLambda: boolean;
  narrowedPaths: NarrowedPath[];  // pure access path narrowing for conditional then-branches
  narrowedIndices: NarrowedIndex[];  // `k in m` atoms known-true in this scope
  forofCounts: Map<string, number>;  // per-function for-of loops seen, by head name
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

/** Infer a conditional's result type after its branches have been resolved or
 *  contextually coerced. `void` is `undefined`, `null` is `null`; mixing both
 *  sentinels yields `nullish<T>` so `null !== undefined` is preserved (#304). */
function conditionalResultTy(thenTy: Ty, elseTy: Ty): Ty {
  if ((thenTy.kind === "int" || thenTy.kind === "nat") &&
      (elseTy.kind === "int" || elseTy.kind === "nat")) {
    return { ...thenTy, kind: thenTy.kind === "int" || elseTy.kind === "int" ? "int" : "nat" };
  }
  const hasNull = (t: Ty) => t.kind === "null" || t.kind === "nullish" || (t.kind === "optional" && optAbsent(t) === "null");
  const hasUndef = (t: Ty) => t.kind === "void" || t.kind === "nullish" || (t.kind === "optional" && optAbsent(t) === "undefined");
  const payloadOf = (t: Ty): Ty | null =>
    t.kind === "void" || t.kind === "null" || t.kind === "unknown" ? null
      : (t.kind === "optional" || t.kind === "nullish") ? t.inner : t;
  const bothNull = hasNull(thenTy) || hasNull(elseTy);
  const bothUndef = hasUndef(thenTy) || hasUndef(elseTy);
  if (bothNull || bothUndef) {
    const p1 = payloadOf(thenTy);
    const p2 = payloadOf(elseTy);
    const inner = p1 ?? p2;
    if (inner) {
      if (bothNull && bothUndef) return { kind: "nullish", inner };
      if (bothNull) return { kind: "optional", inner, absent: "null" };
      return { kind: "optional", inner };
    }
    if (bothNull && bothUndef) return { kind: "nullish", inner: { kind: "void" } };
  }
  return thenTy.kind !== "unknown" ? thenTy : elseTy;
}

/** Contextually type string literals as string-union constructors. Ternary branches inherit
 *  the ternary's target, and an optional/nullish target contributes its payload type —
 *  the caller adds the Some/Value wrapper only after the payload has been coerced. */
function coerceStr(expr: TExpr, targetTy: Ty, typeDecls: TypeDeclInfo[]): TExpr {
  const payloadTy = (targetTy.kind === "optional" || targetTy.kind === "nullish") ? targetTy.inner : targetTy;
  if (expr.kind === "str" && payloadTy.kind === "user") {
    const enumTy = expandAlias(payloadTy, typeDecls);
    // A synthesized string/array union has a string payload, not a constructor
    // for each literal. Leave it for coerceToTargetTy to inject into its branch.
    if (enumTy.kind === "user" && declOfDotted(typeDecls, enumTy.name)?.kind === "string-union")
      return { ...expr, ty: payloadTy };
  }
  if (expr.kind === "conditional") {
    const then_ = coerceStr(expr.then, payloadTy, typeDecls);
    const else_ = coerceStr(expr.else, payloadTy, typeDecls);
    return { ...expr, then: then_, else: else_, ty: conditionalResultTy(then_.ty, else_.ty) };
  }
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

/** Wrap a resolved non-nullish value in Nullish.Value(...) for Nullish<T> coercion. */
function wrapNullishValue(value: TExpr, nullishTy: Ty): TExpr {
  return {
    kind: "call", fn: { kind: "var", name: "NullishValue", ty: nullishTy },
    args: [value], ty: nullishTy, callKind: "pure",
  };
}

/** Find the synth array-union TypeDecl named `name` (discriminant `__isArray__`). */
function findSynthArrayUnion(name: string, typeDecls: TypeDeclInfo[]): TypeDeclInfo | null {
  const decl = declOf(typeDecls, name);
  if (decl?.kind === "discriminated-union" && decl.discriminant === "__isArray__") return decl;
  return null;
}

/** Coerce `value` to `targetTy` at an assignment-position. Contextually types
 *  real literals, then mirrors TS subtyping for the upcast shapes LS synthesizes:
 *    - `T` into `optional<T>` slot  → wrap with `Some(...)`
 *    - `T` / `Option<T>` / `null` / `undefined` into `nullish<T>` slot → `Nullish<T>`
 *    - `fromNullish` into `optional<T>` slot → `__nullishToOption(...)`
 *    - `T[]` into a synth `T[] | U` slot → wrap with `ArrayBranch(...)`
 *    - `U`   into a synth `T[] | U` slot → wrap with `NonArrayBranch(...)`
 *  Returns `value` unchanged if no coercion applies (types already match,
 *  source is unknown, or no rule matches). */
function coerceToTargetTy(value: TExpr, targetTy: Ty, typeDecls: TypeDeclInfo[]): TExpr {
  value = coerceStr(value, targetTy, typeDecls);
  // Real targets also type integer literals, including negative literals and
  // conditional arms. Coerce optional/nullish payloads before adding wrappers.
  const payloadTy = (targetTy.kind === "optional" || targetTy.kind === "nullish") ? targetTy.inner : targetTy;
  if (payloadTy.kind === "real") {
    if (value.kind === "num") {
      value = { ...value, ty: payloadTy };
    } else if (value.kind === "unop" && value.op === "-" && value.expr.kind === "num") {
      value = { ...value, expr: { ...value.expr, ty: payloadTy }, ty: payloadTy };
    } else if (value.kind === "conditional") {
      const then_ = coerceToTargetTy(value.then, payloadTy, typeDecls);
      const else_ = coerceToTargetTy(value.else, payloadTy, typeDecls);
      value = { ...value, then: then_, else: else_, ty: conditionalResultTy(then_.ty, else_.ty) };
    }
  }
  if (targetTy.kind === "nullish") {
    if (value.ty.kind === "unknown") return value;
    if (value.kind === "var" && (value.name === "undefined" || value.name === "null")) {
      return { ...value, ty: targetTy };
    }
    if (value.ty.kind === "void") return { kind: "var", name: "undefined", ty: targetTy };
    if (value.ty.kind === "null") return { kind: "var", name: "null", ty: targetTy };
    if (value.ty.kind === "nullish") return value;
    if (value.ty.kind === "optional") {
      // Partially narrowed fromNullish already lives in Nullish<T> storage.
      if (value.ty.fromNullish) return { ...value, ty: targetTy };
      const helper = optAbsent(value.ty) === "null" ? "__optNullToNullish" : "__optUndefToNullish";
      return {
        kind: "call",
        fn: { kind: "var", name: helper, ty: targetTy },
        args: [value],
        ty: targetTy,
        callKind: "pure",
      };
    }
    if (value.kind === "conditional") {
      const then_ = coerceToTargetTy(value.then, targetTy, typeDecls);
      const else_ = coerceToTargetTy(value.else, targetTy, typeDecls);
      return { ...value, then: then_, else: else_, ty: targetTy };
    }
    return wrapNullishValue(value, targetTy);
  }
  if (value.ty.kind === "unknown" || value.ty.kind === "void" || value.ty.kind === "null") return value;
  if (targetTy.kind === "optional") {
    if (value.ty.kind === "nullish" || (value.ty.kind === "optional" && value.ty.fromNullish)) {
      return {
        kind: "call",
        fn: { kind: "var", name: "__nullishToOption", ty: targetTy },
        args: [value],
        ty: targetTy,
        callKind: "pure",
      };
    }
    if (value.ty.kind !== "optional") {
      return wrapSome(value, targetTy);
    }
  }
  if (targetTy.kind === "user") {
    if (value.ty.kind === "user" && value.ty.name === targetTy.name) return value;
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

/** A negated presence check on a bare var (`v === undefined` / `!v`), via
 *  the shared condition analyzer (§4) on the *resolved* condition. Narrows
 *  the else-branch (or the rest of the block, after an early return). */
function negatedVarPresence(cond: TExpr): { varName: string; innerTy: Ty } | null {
  const f = presentFact(cond);
  if (f && f.negated && f.scrutinee.kind === "var") {
    return { varName: f.scrutinee.name, innerTy: f.innerTy };
  }
  return null;
}

/** Collect all optional narrowings from an early-return condition.
 *  Handles single checks (x === undefined) and compound || chains
 *  (x === undefined || y === undefined). */
/** Extract field-path or optional-chain narrowings guaranteed after an early
 *  return (`if (d.b === undefined) return;` or `if (b?.tag !== 1) return;`, #354). */
function collectEarlyReturnPathNarrowings(cond: TExpr, ctx: Ctx): NarrowedPath[] {
  if (cond.kind === "binop" && cond.op === "||") {
    return [
      ...collectEarlyReturnPathNarrowings(cond.left, ctx),
      ...collectEarlyReturnPathNarrowings(cond.right, ctx),
    ];
  }
  // Negated field-path presence: `d.b === undefined` or `!d.b`
  const f = presentFact(cond);
  if (f && f.negated && f.scrutinee.kind === "field") {
    const path = asTExprAccessPath(f.scrutinee);
    if (path) return [{ path, narrowedTy: f.innerTy }];
  }
  // Optional-chain comparison with non-undefined: `b?.tag !== 1` or `1 !== b?.tag`
  // If `b` were undefined, `b?.tag` is undefined !== 1 (true -> returns early),
  // so after the early return `b` is definitely present.
  if (cond.kind === "binop" && cond.op === "!==") {
    const [ocSide, otherSide] = cond.left.kind === "optChain"
      ? [cond.left, cond.right]
      : cond.right.kind === "optChain"
        ? [cond.right, cond.left]
        : [null, null];
    if (ocSide && otherSide && excludesUndefined(otherSide, ctx.typeDecls, ctx.typeParams) &&
        ocSide.obj.ty.kind === "optional") {
      const path = asTExprAccessPath(ocSide.obj);
      if (path) return [{ path, narrowedTy: ocSide.obj.ty.inner }];
    }
  }
  // Bare negated optional chain `!b?.flag` or `b?.tag === undefined`
  if (cond.kind === "unop" && cond.op === "!" && cond.expr.kind === "optChain" && cond.expr.obj.ty.kind === "optional") {
    const path = asTExprAccessPath(cond.expr.obj);
    if (path) return [{ path, narrowedTy: cond.expr.obj.ty.inner }];
  }
  if (cond.kind === "binop" && cond.op === "===") {
    const [ocSide, otherSide] = cond.left.kind === "optChain"
      ? [cond.left, cond.right]
      : cond.right.kind === "optChain"
        ? [cond.right, cond.left]
        : [null, null];
    if (ocSide && otherSide && otherSide.kind === "var" && otherSide.name === "undefined" &&
        ocSide.obj.ty.kind === "optional") {
      const path = asTExprAccessPath(ocSide.obj);
      if (path) return [{ path, narrowedTy: ocSide.obj.ty.inner }];
    }
  }
  return [];
}

function collectEarlyReturnNarrowings(cond: TExpr): { varName: string; innerTy: Ty }[] {
  if (cond.kind === "binop" && cond.op === "||") {
    return [...collectEarlyReturnNarrowings(cond.left), ...collectEarlyReturnNarrowings(cond.right)];
  }
  const n = negatedVarPresence(cond);
  return n ? [n] : [];
}

/** Return the payload type of `variant` on a synth array-union (`__isArray__`),
 *  or null for non-synth types. */
function synthVariantPayloadTy(ty: Ty, variant: string, ctx: Ctx): Ty | null {
  if (ty.kind !== "user") return null;
  const decl = findSynthArrayUnion(ty.name, ctx.typeDecls);
  const f = decl?.variants?.find(v => v.name === variant)?.fields[0];
  return f ? (f.type ?? parseTsType(f.tsType)) : null;
}

/** Narrow a pure access path to a union variant in `ctx`. For synth array-unions
 *  (`__isArray__`), also narrows the path's flow type to the branch's payload
 *  type so array/string methods and checked projections fire uniformly. */
function applyVariantNarrowing(ctx: Ctx, path: AccessPath, unionTy: Ty, variant: string): Ctx {
  const payload = synthVariantPayloadTy(unionTy, variant, ctx);
  if (payload) {
    const nextPaths = [...ctx.narrowedPaths, { path, narrowedTy: payload, variant }];
    if (path.fields.length === 0) {
      return { ...withEnv(ctx, refine(ctx.env, path.rootVar, payload)), narrowedPaths: nextPaths };
    }
    return { ...ctx, narrowedPaths: nextPaths };
  }
  return { ...ctx, narrowedPaths: [...ctx.narrowedPaths, { path, narrowedTy: unionTy, variant }] };
}

/** Synth array-union branch guaranteed by `Array.isArray(path)`, `!Array.isArray(path)`,
 *  or `typeof path === "string"` when `cond` evaluates to `truth`. */
function synthVariantWhen(
  cond: TExpr,
  truth: boolean,
  ctx: Ctx,
): { path: AccessPath; unionTy: Ty; variant: "ArrayBranch" | "NonArrayBranch" } | null {
  if (cond.kind === "unop" && cond.op === "!") return synthVariantWhen(cond.expr, !truth, ctx);
  const condCtx = { decls: ctx.typeDecls, oc: { n: 0 } };
  const arr = isArrayFact(cond, condCtx);
  if (arr) {
    const path = asTExprAccessPath(arr.scrutinee);
    if (!path) return null;
    return { path, unionTy: arr.scrutinee.ty, variant: truth ? "ArrayBranch" : "NonArrayBranch" };
  }
  const tof = typeofStringFact(cond, condCtx);
  if (tof) {
    const path = asTExprAccessPath(tof.scrutinee);
    if (!path) return null;
    return { path, unionTy: tof.scrutinee.ty, variant: truth ? "NonArrayBranch" : "ArrayBranch" };
  }
  return null;
}

/** Innermost narrowed union variant recorded for `path` in `ctx.narrowedPaths`. */
function lookupNarrowedVariant(path: AccessPath, ctx: Ctx): string | undefined {
  for (let i = ctx.narrowedPaths.length - 1; i >= 0; i--) {
    const cand = ctx.narrowedPaths[i]!;
    if (cand.variant && accessPathsEqual(cand.path, path)) return cand.variant;
  }
  return undefined;
}

/** Project narrowed union arguments to nominal records expected by a callee
 *  (`helper(sh)` → `helper({ n: sh.n })`), using `ctx.narrowedPaths` so it works
 *  uniformly on live storage and after reassignment. */
function projectStructuralCallArgs(args: TExpr[], paramTypes: Ty[], ctx: Ctx): TExpr[] {
  return args.map((arg, i) => {
    if (i >= paramTypes.length || arg.ty.kind !== "user") return arg;
    const targetTy = paramTypes[i];
    if (targetTy.kind !== "user") return arg;
    const targetDecl = declOfKind(ctx.typeDecls, targetTy.name, "record");
    if (!targetDecl?.fields) return arg;
    const argPath = asTExprAccessPath(arg);
    if (!argPath) return arg;
    const variantName = lookupNarrowedVariant(argPath, ctx);
    if (!variantName) return arg;
    const unionDecl = declOfKind(ctx.typeDecls, tyBaseName(arg.ty.name), "discriminated-union");
    const variant = unionDecl?.variants?.find(v => v.name === variantName);
    if (!variant) return arg;
    const matched: { targetName: string; sourceName: string; ty: Ty }[] = [];
    for (const tf of targetDecl.fields) {
      const sf = variant.fields.find(f => f.name === tf.name);
      const tfTy = tf.type ?? parseTsType(tf.tsType);
      const sfTy = sf ? (sf.type ?? parseTsType(sf.tsType)) : undefined;
      if (!sf || !sfTy || !tyEqual(sfTy, tfTy)) return arg;
      matched.push({ targetName: tf.name, sourceName: sf.name, ty: sfTy });
    }
    return {
      kind: "record" as const,
      spread: null,
      fields: matched.map(m => ({
        name: m.targetName,
        value: { kind: "field" as const, obj: arg, field: m.sourceName, ty: m.ty, ofVariant: variantName },
      })),
      ty: targetTy,
    };
  });
}

/** Variant guaranteed by a discriminant comparison (`path.kind === "lit"` or
 *  `!== "lit"`, either operand order, with optional `!`) when `cond` evaluates
 *  to `truth`. Exclusions narrow only when exactly one union variant remains. */
function discriminantVariantWhen(cond: TExpr, truth: boolean, ctx: Ctx): NarrowedPath | null {
  if (cond.kind === "unop" && cond.op === "!") return discriminantVariantWhen(cond.expr, !truth, ctx);
  if (cond.kind !== "binop" || (cond.op !== "===" && cond.op !== "!==")) return null;
  const field = cond.left.kind === "field" ? cond.left : cond.right.kind === "field" ? cond.right : null;
  const label = cond.left.kind === "str" ? cond.left : cond.right.kind === "str" ? cond.right : null;
  if (!field?.isDiscriminant || !label || field.obj.ty.kind !== "user") return null;
  const path = asTExprAccessPath(field.obj);
  if (!path) return null;
  const matches = truth === (cond.op === "===");
  if (matches) return { path, narrowedTy: field.obj.ty, variant: label.value };
  const decl = findDecl(ctx, tyBaseName(field.obj.ty.name));
  const rem = decl?.discriminant === field.field ? remainingVariant(decl, [label.value]) : undefined;
  return rem ? { path, narrowedTy: field.obj.ty, variant: rem.name } : null;
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

/** Walk an `&&` chain of `e !== undefined` checks on the *resolved*
 *  condition, returning a Ctx with all narrowings applied. Earlier checks
 *  are in scope for later checks (the right conjunct was already resolved
 *  under the left's narrowings by the `&&` case of resolveExpr). Consults
 *  the shared condition analyzer (§4): a positive presence fact on a bare
 *  var extends the env; on a pure field path it extends `narrowedPaths`. */
function collectAndChainNarrowings(cond: TExpr, ctx: Ctx): Ctx {
  if (cond.kind === "binop" && cond.op === "&&") {
    const leftCtx = collectAndChainNarrowings(cond.left, ctx);
    return collectAndChainNarrowings(cond.right, leftCtx);
  }
  const f = presentFact(cond);
  if (f && !f.negated) {
    if (f.scrutinee.kind === "var") {
      return withEnv(ctx, refine(ctx.env, f.scrutinee.name, f.innerTy));
    }
    const path = asTExprAccessPath(f.scrutinee);
    if (path) {
      return { ...ctx, narrowedPaths: [...ctx.narrowedPaths, { path, narrowedTy: f.innerTy }] };
    }
    return ctx;
  }
  // Positive discriminant check (`x.kind === "bool"`, `"bool" === x.kind`, or
  // `x.kind !== "other"` on a 2-variant union): record the variant so field
  // reads on the path resolve against that variant's field types.
  const dv = discriminantVariantWhen(cond, true, ctx);
  if (dv) {
    return { ...ctx, narrowedPaths: [...ctx.narrowedPaths, dv] };
  }
  const sv = synthVariantWhen(cond, true, ctx);
  if (sv) {
    return applyVariantNarrowing(ctx, sv.path, sv.unionTy, sv.variant);
  }
  const vf = variantFact(cond, { decls: ctx.typeDecls, oc: { n: 0 } });
  if (vf) {
    const path = asTExprAccessPath(vf.scrutinee);
    if (path) {
      return applyVariantNarrowing(ctx, path, vf.scrutinee.ty, vf.variant);
    }
  }
  return ctx;
}

/** Walk an `||` chain of negated presence checks (`x === undefined || a.b === undefined || ...`)
 *  on the resolved left operand, returning a Ctx where those paths are narrowed
 *  for evaluating the right operand of `||` (since the RHS only runs when the
 *  LHS was false). Mirrors `collectAndChainNarrowings`. */
function collectOrChainNarrowings(cond: TExpr, ctx: Ctx): Ctx {
  if (cond.kind === "binop" && cond.op === "||") {
    const leftCtx = collectOrChainNarrowings(cond.left, ctx);
    return collectOrChainNarrowings(cond.right, leftCtx);
  }
  const f = presentFact(cond);
  if (f && f.negated) {
    if (f.scrutinee.kind === "var") {
      return withEnv(ctx, refine(ctx.env, f.scrutinee.name, f.innerTy));
    }
    const path = asTExprAccessPath(f.scrutinee);
    if (path) {
      return { ...ctx, narrowedPaths: [...ctx.narrowedPaths, { path, narrowedTy: f.innerTy }] };
    }
  }
  const dv = discriminantVariantWhen(cond, false, ctx);
  if (dv) {
    return { ...ctx, narrowedPaths: [...ctx.narrowedPaths, dv] };
  }
  const sv = synthVariantWhen(cond, false, ctx);
  if (sv) {
    return applyVariantNarrowing(ctx, sv.path, sv.unionTy, sv.variant);
  }
  return ctx;
}

/** TS reference types that become value types in Dafny/Lean — const bindings need mutable var. */
function isRefMutableInTS(ty: Ty): boolean {
  return ty.kind === "array" || ty.kind === "map" || ty.kind === "set";
}

function findDecl(ctx: Ctx, name: string): TypeDeclInfo | undefined {
  // Dotted names (e.g. `Agent.Info`, `Permission.Ruleset`) fall back to the
  // last segment, so `//@ declare-type Info { ... }` matches a reference to
  // `Agent.Info` without forcing the user to repeat the namespace.
  return declOfDotted(ctx.typeDecls, name);
}

/** Expand alias-kind typeDecls when the alias target is structural (array,
 *  map, set, optional, or another user type). Primitive-typed aliases like
 *  `type TaskId = number` stay as `user("TaskId")` so the generated Dafny
 *  preserves the alias name. Recursive through compound types; cycle-safe. */
function expandAlias(ty: Ty, typeDecls: TypeDeclInfo[], seen: Set<string> = new Set()): Ty {
  if (ty.kind === "user") {
    if (seen.has(ty.name)) return ty;
    const dot = ty.name.lastIndexOf(".");
    const enumDecl = typeDecls.find(d => d.name === ty.name.slice(0, dot));
    if (dot > 0 && enumDecl?.constEnumMembers?.some(m => m.name === ty.name.slice(dot + 1))) return { kind: "int" };
    const decl = declOfDotted(typeDecls, ty.name);
    if (decl?.kind === "alias" && decl.aliasOfTy) {
      // Numeric enums must behave as numbers (not truthy user objects).
      if (decl.constEnumMembers) return { kind: "int" };
      const target = decl.aliasOfTy;
      if (target.kind === "array" || target.kind === "map" || target.kind === "set" || target.kind === "optional" || target.kind === "nullish" || target.kind === "user") {
        return expandAlias(target, typeDecls, new Set([...seen, ty.name]));
      }
    }
    return ty;
  }
  if (ty.kind === "optional") {
    const expanded = expandAlias(ty.inner, typeDecls, seen);
    if (expanded.kind === "nullish") return expanded;
    if (expanded.kind === "optional") {
      const mergedNull = optAbsent(ty) === "null" || optAbsent(expanded) === "null";
      const mergedUndef = optAbsent(ty) === "undefined" || optAbsent(expanded) === "undefined";
      if (mergedNull && mergedUndef) return { kind: "nullish", inner: expanded.inner };
      return { ...ty, inner: expanded.inner };
    }
    return { ...ty, inner: expanded };
  }
  if (ty.kind === "nullish") {
    const expanded = expandAlias(ty.inner, typeDecls, seen);
    if (expanded.kind === "nullish") return expanded;
    if (expanded.kind === "optional") return { kind: "nullish", inner: expanded.inner };
    return { kind: "nullish", inner: expanded };
  }
  if (ty.kind === "array") return { kind: "array", elem: expandAlias(ty.elem, typeDecls, seen) };
  if (ty.kind === "tuple") return { kind: "tuple", elems: ty.elems.map(e => expandAlias(e, typeDecls, seen)) };
  if (ty.kind === "set") return { kind: "set", elem: expandAlias(ty.elem, typeDecls, seen) };
  if (ty.kind === "map") return { kind: "map", key: expandAlias(ty.key, typeDecls, seen), value: expandAlias(ty.value, typeDecls, seen) };
  return ty;
}

/** Numeric aliases keep their names in declarations but use their underlying
 *  types in expressions. Optional/nullish payloads need the same treatment for
 *  zero's falsiness; collection elements are resolved when read. */
function numericValueType(ty: Ty, typeDecls: TypeDeclInfo[], seen: Set<string> = new Set()): Ty {
  if (ty.kind === "optional") return { ...ty, inner: numericValueType(ty.inner, typeDecls, seen) };
  if (ty.kind === "nullish") return { kind: "nullish", inner: numericValueType(ty.inner, typeDecls, seen) };
  if (ty.kind !== "user" || seen.has(ty.name)) return ty;
  const decl = declOfDotted(typeDecls, ty.name);
  if (decl?.kind === "alias" && decl.aliasOfTy) {
    const target = numericValueType(decl.aliasOfTy, typeDecls, new Set([...seen, ty.name]));
    if (target.kind === "int" || target.kind === "nat" || target.kind === "real") return target;
  }
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
    const decl = declOfDotted(typeDecls, ty.name);
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
  if (ty.kind === "optional" || ty.kind === "nullish") return isUnmodeledTy(ty.inner, typeDecls);
  if (ty.kind === "array") return isUnmodeledTy(ty.elem, typeDecls);
  if (ty.kind === "tuple") return ty.elems.some(e => isUnmodeledTy(e, typeDecls));
  if (ty.kind === "set") return isUnmodeledTy(ty.elem, typeDecls);
  if (ty.kind === "map") return isUnmodeledTy(ty.key, typeDecls) || isUnmodeledTy(ty.value, typeDecls);
  if (ty.kind === "user") return declOfTy(typeDecls, ty) === undefined;
  return false;
}

/** A `user` type that resolves to a string-union declare-type — runs as a plain
 *  string at runtime, so it's a refinement of `string`, not an opaque blob. */
function isStringUnionTy(ty: Ty, typeDecls: TypeDeclInfo[]): boolean {
  return declOfTy(typeDecls, ty)?.kind === "string-union";
}

/** Whether ts-morph widened a string-union initializer to the declared string
 *  shape. Inferred optional locals need the same rescue as bare locals:
 *  `Option<string>` from TS must not erase an `Option<Color>` initializer. */
function isWidenedStringUnionTy(declTy: Ty, initTy: Ty, typeDecls: TypeDeclInfo[]): boolean {
  if (declTy.kind === "string" && isStringUnionTy(initTy, typeDecls)) return true;
  if (declTy.kind === "optional" && initTy.kind === "optional") {
    return isWidenedStringUnionTy(declTy.inner, initTy.inner, typeDecls);
  }
  return false;
}

/** Infer quantifier variable type from usage in body.
 *  If the variable is used as a map/set key (e.g. map.has(k), map.get(k)),
 *  return the collection's key type. Otherwise return null (default to int). */
function inferQuantVarType(varName: string, body: RawExpr, ctx: Ctx): Ty | null {
  // Spec membership uses a binary node (`x in collection`), unlike the
  // executable `.has(x)` / `.includes(x)` calls handled below. Infer the
  // quantified variable from the RHS collection so documented forms such as
  // `forall(x, x in \result ==> ...)` do not silently fall back to `int`.
  if (body.kind === "binop" && body.op === "in" &&
      body.left.kind === "var" && body.left.name === varName) {
    const collectionTy = resolveExpr(body.right, ctx).ty;
    if (collectionTy.kind === "map") return collectionTy.key;
    if (collectionTy.kind === "set" || collectionTy.kind === "array") return collectionTy.elem;
  }
  // Look for membership/lookup builtins (map.has(k), map.get(k),
  // array.includes(k) — registry `argIsKey`) where k is our variable
  if (body.kind === "call" && body.fn.kind === "field" &&
      body.args.length === 1 && body.args[0].kind === "var" && body.args[0].name === varName) {
    const objTy = lookup(ctx.env, body.fn.obj.kind === "var" ? body.fn.obj.name : "");
    const id = objTy ? recognizeBuiltin(objTy, body.fn.field) : null;
    if (id && builtinSpec(id).argIsKey && objTy) {
      if (objTy.kind === "map") return objTy.key;
      if (objTy.kind === "set") return objTy.elem;
      if (objTy.kind === "array") return objTy.elem;
    }
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
  if (fn.kind === "var" && binding(ctx.env, fn.name))
    return lookup(ctx.env, fn.name)?.kind === "fn" ? "pure" : "method";
  if (fn.kind === "field" && fn.obj.kind === "var" && fn.obj.name === "Math") return "pure";
  if (fn.kind === "field" && fn.obj.kind === "var" && fn.obj.name === "Array" && fn.field === "isArray") return "pure";
  if (fn.kind === "field" && fn.obj.kind === "var" && fn.obj.name === "String" && fn.field === "fromCharCode") return "pure";
  if (fn.kind === "field" && fn.obj.kind === "var" && fn.obj.name === "Number" && fn.field === "isSafeInteger") return "pure";
  if (fn.kind === "var" && (ctx.inSpec || ctx.inLambda) && ctx.pureFns.has(fn.name)) return "spec-pure";
  // Effectively pure bare-name externs are function calls. Impure externs are
  // lifted to statement-level method binds so repeated invocations remain
  // independent. A method call cannot occur in a spec or lambda expression.
  if (fn.kind === "var") {
    const ext = ctx.externs.get(fn.name);
    if (ext) {
      if (!ext.impure) return "pure";
      if (ctx.inSpec) throw new Error(`impure extern ${fn.name} cannot be called from a specification`);
      if (ctx.inLambda) throw new Error(`impure extern ${fn.name} cannot be called from a lambda`);
      return "method";
    }
  }
  if (fn.kind === "var" && ctx.inSpec) {
    // Not a known pure function — could be external (Lean-defined spec helper).
    // Pass through as "pure" and let Lean catch any errors.
    return "pure";
  }
  if (fn.kind === "var") return "method";
  return "unknown";
}

// ── Call resolution helpers ─────────────────────────────────

/** Render a resolved type back to a TS type string, for lambda param inference. */
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
/** Infer lambda param types from function-typed parameters of named callees
 *  (e.g., a `Comparator = (a, b) => bool` parameter propagates `string, string` to the lambda's
 *  inline params). Returns updated rawArgs with inferred tsType. */
function inferLambdaParamTypes(fn: TExpr, rawArgs: RawExpr[], ctx?: Ctx): RawExpr[] {
  // Named-callee propagation: when an argument position expects a function
  // type, infer the lambda's param types from that function type. Aliases
  // (e.g., `Comparator`) are expanded via the typeDecls.
  if (fn.kind === "var" && ctx?.fnParams.has(fn.name) && !binding(ctx.env, fn.name)) {
    const paramTys = ctx.fnParams.get(fn.name)!;
    return rawArgs.map((a, i) => {
      if (a.kind !== "lambda" || i >= paramTys.length) return a;
      let pTy = paramTys[i];
      if (pTy.kind === "user") {
        const decl = declOf(ctx.typeDecls, (pTy as any).name);
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

let callbackCounter = 0;

function callbackDefaultState(ty: Ty, ctx: Ctx, seen = new Set<string>()): "missing" | "defined" | "optional" | "unknown" {
  if (ty.kind === "void") return "missing";
  if (ty.kind === "null") return "defined";
  if (ty.kind === "optional") return optAbsent(ty) === "null" ? "defined" : "optional";
  if (ty.kind === "nullish") return "optional";
  if (ty.kind === "unknown") return "unknown";
  if (ty.kind !== "user" || ty.name === "null") return "defined";
  if (seen.has(ty.name)) return "unknown";
  const decl = declOfDotted(ctx.typeDecls, ty.name);
  if (decl?.kind === "alias" && decl.aliasOfTy)
    return callbackDefaultState(decl.aliasOfTy, ctx, new Set([...seen, ty.name]));
  return decl && decl.kind !== "opaque" ? "defined" : "unknown";
}

/** Bind an inline callback against its actual JavaScript argument list.
 * Rest is a symbolic argument pack: observing its length or a fixed position
 * needs no heterogeneous array. Unobserved slots disappear without inspecting
 * identifier spellings or dropping any source computation. */
function resolveCallback(e: Extract<RawExpr, { kind: "lambda" }>, actual: Ty[], baseArity: number, ctx: Ctx): TExpr {
  const id = callbackCounter++;
  const used = actual.map(() => false);
  const defaults = actual.map(ty => callbackDefaultState(ty, ctx));
  const slots = actual.map((ty, i) => {
    const p = e.params[i];
    return {
      name: p && !p.rest && !(p.defaultValue && defaults[i] === "missing") ? p.name : freshName(`_callbackArg${id}_${i}`),
      ty: p && !p.rest && p.tsType ? parseTsType(p.tsType)
        : ty.kind === "nat" ? { ...ty, kind: "int" as const } : ty,
    };
  });
  const read = (i: number): TExpr => {
    if (i >= slots.length) return { kind: "var", name: "undefined", ty: { kind: "void" } };
    used[i] = true;
    return { kind: "var", ...slots[i] };
  };
  const executesDefault = (i: number) => !!e.params[i].defaultValue &&
    (i >= actual.length || defaults[i] === "missing");
  const ready = new Set<number>();
  const eagerReads = new Set<number>();
  let captures: Set<number> | undefined;
  const prefix: TStmt[] = [];
  const pending = new Map<number, { init: TExpr; captures: Set<number> }>();

  // All parameter names are in scope before any initializer. The frames are
  // binding identities; nested declarations shadow them through ordinary lookup.
  let env = ctx.env;
  const frames = e.params.map((p, i): Env => {
    const paramTy: Ty = executesDefault(i)
      ? expandAlias(parseTsType(p.inferredTsType ?? p.tsType ?? "unknown"), ctx.typeDecls)
      : p.rest ? { kind: "unknown" } : slots[i]?.ty ?? { kind: "void" };
    const frame: Env = {
      name: p.name, parent: env,
      ty: paramTy,
      storageTy: paramTy,
      onRead: () => {
        captures?.add(i);
        // A forward reference must never resolve to an outer variable if
        // ordinary backend lowering cannot represent its initialization order.
        if (!ready.has(i)) {
          frame.emittedName ??= freshName(`_callbackParam${id}_${i}`);
          // Keep the read itself: e.g. !array can later fold to false and erase
          // an unresolved reference. An ordinary let retains the scope check.
          if (!captures && !eagerReads.has(i)) {
            eagerReads.add(i);
            prefix.push({ kind: "let", name: freshName(`_callbackRead${id}_${i}`), ty: frame.ty,
              mutable: false, init: { kind: "var", name: frame.emittedName, ty: frame.ty } });
          }
        }
        if (!p.rest && !executesDefault(i) && i < actual.length) used[i] = true;
      },
      get argumentPack() {
        // Folding an eager read of an uninitialized rest binding to a constant
        // would erase a JavaScript error. Leave that read to ordinary lowering.
        return p.rest && (ready.has(i) || captures)
          ? { length: Math.max(0, actual.length - i), at: (k: number) => read(i + k) } : undefined;
      },
      get value() {
        return !p.rest && !executesDefault(i) && i >= actual.length && (ready.has(i) || captures)
          ? { kind: "var" as const, name: "undefined", ty: { kind: "void" as const } } : undefined;
      },
    };
    env = frame;
    return frame;
  });
  const emit = (i: number, init: TExpr) => {
    const frame = frames[i];
    prefix.push({ kind: "let", name: frame.emittedName ?? frame.name, ty: frame.ty, mutable: false, init });
    ready.add(i);
  };
  const flush = () => {
    let progress = true;
    while (progress) {
      progress = false;
      for (const [i, p] of pending) {
        if (![...p.captures].every(j => ready.has(j))) continue;
        emit(i, p.init);
        pending.delete(i);
        progress = true;
      }
    }
  };
  for (const [i, p] of e.params.entries()) {
    if (executesDefault(i)) {
      // Only literal lambda creation is deferred; all source computations keep
      // their order. Resolution is synchronous, so this local collector also
      // sees reads through nested lambdas without threading capture maps in Ctx.
      captures = p.defaultValue!.kind === "lambda" ? new Set<number>() : undefined;
      const init = resolveExpr(p.defaultValue!, { ...ctx, env, inLambda: true });
      const dependencies = captures;
      captures = undefined;
      if (!frames[i].emittedName) frames[i].ty = init.ty;
      if (dependencies) pending.set(i, { init, captures: dependencies });
      else emit(i, init);
    } else {
      // A supplied non-optional value never evaluates a default. An Option
      // cannot distinguish null from undefined, and an unknown value may be
      // either; dropping the initializer could erase a call obligation.
      if (p.defaultValue && defaults[i] === "optional") {
        throw new Error(`callback default for '${p.name}' needs a distinction between null and undefined`);
      }
      if (p.defaultValue && defaults[i] === "unknown") {
        throw new Error(`callback default for '${p.name}' needs a known argument type to decide whether the initializer executes`);
      }
      // Supplied argument slots are backend lambda parameters. A forward source
      // reference needs its own local binding, initialized at the right position.
      if (frames[i].emittedName && !p.rest && i < actual.length) emit(i, read(i));
      else ready.add(i);
    }
    flush();
  }
  // Cycles and uses before closure construction stay in ordinary lowering.
  // Hygienic names make unsupported scope references backend errors, rather
  // than silently capturing an unrelated outer binding. No source call moves.
  for (const [i, p] of pending) emit(i, p.init);
  const returnTy: Ty = e.returnTsType ? parseTsType(e.returnTsType) : { kind: "unknown" };
  const lambdaCtx = { ...ctx, env, inLambda: true, returnTy };
  const body = [...prefix, ...(Array.isArray(e.body) ? resolveBlock(e.body, lambdaCtx)
    : [{ kind: "return" as const, value: resolveExpr(e.body, lambdaCtx) }])];
  const arity = Math.max(baseArity, used.lastIndexOf(true) + 1);
  const params = slots.slice(0, arity);
  const ty: Ty = e.returnTsType ? { kind: "fn", params: params.map(p => p.ty), result: returnTy } : { kind: "unknown" };
  return { kind: "lambda", params, body, ty };
}

function callbackContext(fn: TExpr, initial?: TExpr): { actual: Ty[]; baseArity: number } | undefined {
  if (fn.kind !== "field") return undefined;
  const id = recognizeBuiltin(fn.obj.ty, fn.field);
  if (!id) return undefined;
  const spec = builtinSpec(id);
  const actual = callbackArgumentTypes(spec, fn.obj.ty, initial?.ty);
  return actual && spec.hof ? { actual, baseArity: callbackBaseArity(spec.hof.shape) } : undefined;
}

function argumentPack(e: RawExpr, ctx: Ctx): Env["argumentPack"] {
  const entry = e.kind === "var" ? binding(ctx.env, e.name) : undefined;
  const pack = entry?.argumentPack;
  if (pack) entry.onRead?.();
  return pack;
}

/** A defined-check filter predicate: `(x) => x !== undefined`, `(x) => x !== null`,
 *  or loose `(x) => x != null` / `(x) => x != undefined`. Returns which sentinel
 *  the filter removes so `filterSome` only fires when it matches the array
 *  element's absent sentinel (`#304`). */
function definedCheckRawLambdaSentinel(raw: RawExpr): "undefined" | "null" | "both" | null {
  if (raw.kind !== "lambda" || raw.params.length !== 1) return null;
  const p = raw.params[0].name;
  const body = Array.isArray(raw.body)
    ? (raw.body.length === 1 && raw.body[0].kind === "return" ? raw.body[0].value : null)
    : raw.body;
  if (!body || body.kind !== "binop" || (body.op !== "!==" && body.op !== "!=")) return null;
  const isParam = (x: RawExpr) => x.kind === "var" && x.name === p;
  const sentinelOf = (x: RawExpr): "undefined" | "null" | null =>
    x.kind === "var" && (x.name === "undefined" || x.name === "null") ? x.name : null;
  const s = isParam(body.left) ? sentinelOf(body.right) : isParam(body.right) ? sentinelOf(body.left) : null;
  if (!s) return null;
  return body.op === "!=" ? "both" : s;
}

/** Coerce call arguments to their declared parameter slots and pad missing optional args. */
function coerceCallArgs(args: TExpr[], fn: TExpr, ctx: Ctx): TExpr[] {
  if (fn.kind !== "var" || binding(ctx.env, fn.name) || !ctx.fnParams.has(fn.name)) return args;
  const paramTys = ctx.fnParams.get(fn.name)!;
  args = args.map((a, i) => {
    if (i >= paramTys.length) return a;
    return coerceToTargetTy(a, paramTys[i], ctx.typeDecls);
  });
  // Pad missing optional/nullish args with undefined (None / Nullish.Undefined)
  for (let i = args.length; i < paramTys.length; i++) {
    if (paramTys[i].kind === "optional" || paramTys[i].kind === "nullish") {
      args.push({ kind: "var" as const, name: "undefined", ty: paramTys[i] });
    }
  }
  return args;
}

/** Join Math.min/max operands without losing bigint or depending on their order. */
function minMaxNumericTy(types: Ty[], name: string): Ty {
  for (const ty of types) {
    if (isBigInt(ty)) throw new Error(`${name} does not accept bigint operands (JavaScript throws TypeError)`);
    if (ty.kind !== "int" && ty.kind !== "nat" && ty.kind !== "real")
      throw new Error(`${name} requires numeric operands, got ${tyToCanonical(ty)}`);
  }
  return types.some(ty => ty.kind === "real") ? { kind: "real" }
    : types.length > 0 && types.every(ty => ty.kind === "nat") ? { kind: "nat" } : { kind: "int" };
}

/** Resolve the concat tree built by extract for Math.min/max spreads. Numeric
 *  literal segments are sequences even when their elements mix int/nat/real;
 *  ordinary array inference would turn those into heterogeneous tuples.
 *  Empty literals contribute no operand type to the surrounding concat. */
function resolveMinMaxSequence(raw: RawExpr, ctx: Ctx, name: string): { expr: TExpr; types: Ty[] } {
  if (raw.kind === "binop" && raw.op === "arrayConcat") {
    const left = resolveMinMaxSequence(raw.left, ctx, name);
    const right = resolveMinMaxSequence(raw.right, ctx, name);
    const types = [...left.types, ...right.types];
    return { expr: { kind: "binop", op: "arrayConcat", left: left.expr, right: right.expr,
      ty: { kind: "array", elem: minMaxNumericTy(types, name) } }, types };
  }
  if (raw.kind === "arrayLiteral") {
    const elems = raw.elems.map(e => resolveExpr(e, ctx));
    const types = elems.map(e => e.ty);
    return { expr: { kind: "arrayLiteral", elems,
      ty: { kind: "array", elem: minMaxNumericTy(types, name) } }, types };
  }
  const expr = resolveExpr(raw, ctx);
  if (expr.ty.kind !== "array") throw new Error(`${name} spread requires a numeric array`);
  minMaxNumericTy([expr.ty.elem], name);
  return { expr, types: [expr.ty.elem] };
}

/** Infer return type for collection/string method calls. */
function inferMethodReturnTy(fn: TExpr, args: TExpr[], ctx: Ctx): Ty {
  if (fn.kind !== "field") return { kind: "unknown" };
  // `Array.isArray(x)` always returns boolean. narrow.ts recognizes this call as
  // a discriminator predicate when `x` has type of a synthesized array-union.
  if (fn.obj.kind === "var" && fn.obj.name === "Array" && fn.field === "isArray") {
    return { kind: "bool" };
  }
  // `String.fromCharCode(n)` is the inverse of `s.charCodeAt(i)`: an int code
  // point in, a one-character string out.
  if (fn.obj.kind === "var" && fn.obj.name === "String" && fn.field === "fromCharCode") {
    return { kind: "string" };
  }
  if (fn.obj.kind === "var" && fn.obj.name === "Number" && fn.field === "isSafeInteger") {
    return { kind: "bool" };
  }
  // Math.* numeric builtins: abs/min/max preserve the operand's numeric type
  // (real if any operand is real); floor/ceil/round/trunc return an integer.
  if (fn.obj.kind === "var" && fn.obj.name === "Math") {
    if (fn.field === "abs" && args.length === 1) return args[0].ty;
    if (fn.field === "min" || fn.field === "max") {
      if (args.length === 0)
        throw new Error(`Math.${fn.field}() with zero arguments returns ${fn.field === "max" ? "-Infinity" : "Infinity"}, which is not supported by the numeric model`);
      return minMaxNumericTy(args.map(a => a.ty), `Math.${fn.field}`);
    }
    // trunc/round are the identity on an integer, so a nat argument stays nat.
    if ((fn.field === "trunc" || fn.field === "round") && args.length === 1 &&
        args[0].ty.kind === "nat") return { kind: "nat" };
    if (["floor", "ceil", "round", "trunc"].includes(fn.field)) return { kind: "int" };
  }
  const objTy = fn.obj.ty;
  const id = recognizeBuiltin(objTy, fn.field);
  if (id) return builtinSpec(id).ret(objTy, args, { inSpec: ctx.inSpec });
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
    const baseTyName = tyBaseName(objTy.name);
    const isDiscriminant = getDiscriminant(ctx, baseTyName) === field;
    const decl = findDecl(ctx, baseTyName);
    if (decl?.kind === "record") {
      const f = decl.fields?.find(f => f.name === field);
      if (f) return { ty: f.type!, isDiscriminant };
    }
    if (decl?.kind === "discriminated-union" && decl.variants) {
      const matches = decl.variants
        .map(v => v.fields.find(f => f.name === field)?.type)
        .filter((t): t is Ty => t !== undefined);
      if (matches.length > 0 && matches.every(t => tyEqual(t, matches[0]))) {
        return { ty: matches[0], isDiscriminant };
      }
      return { ty: { kind: "unknown" }, isDiscriminant };
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
 *  base's field shows through. `f?:` fields decide presence at runtime (`Some?`);
 *  required fields (including `T | null`) are always copied from the override.
 *  An `Option`-typed override is the whole merge guarded by its tag. */
function resolveRecordMerge(base: RawExpr, override: RawExpr, ctx: Ctx): TExpr {
  const tbase = resolveExpr(base, ctx);
  const tover = resolveExpr(override, ctx);
  const overInner = (tover.ty.kind === "optional" || tover.ty.kind === "nullish") ? tover.ty.inner : tover.ty;
  // Result record type: prefer the override's (an optional/nullish override still merges
  // into its inner type), else the base's.
  const rTy = overInner.kind === "user" ? overInner
            : tbase.ty.kind === "user" ? tbase.ty : null;
  const decl = rTy ? declOfKind(ctx.typeDecls, rTy.name, "record") : undefined;
  if (!rTy || !decl?.fields) {
    throw new Error(`object spread merge { ...a, ...b } needs a known record type for both operands ` +
      `(base: ${tyToCanonical(tbase.ty)}, override: ${tyToCanonical(tover.ty)})`);
  }
  if (tbase.ty.kind === "optional" || tbase.ty.kind === "nullish") {
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
      // A required key is always copied, even when its value is null/undefined.
      if (!f.optionalKey || (ft.kind !== "optional" && ft.kind !== "nullish")) return { name: f.name, value: ovf };
      const bvf: TExpr = { kind: "field", obj: bv, field: f.name, ty: ft };
      if (ft.kind === "nullish") {
        // `f?: T | null`: override wins unless `ov.f === undefined` (null still overrides!).
        const isUndef: TExpr = {
          kind: "binop", op: "===",
          left: ovf, right: { kind: "var", name: "undefined", ty: { kind: "void" } },
          ty: { kind: "bool" },
        };
        return { name: f.name, value: { kind: "conditional", cond: isUndef, then: bvf, else: ovf, ty: ft } };
      }
      // `f?:` optional key: override field wins iff present, else base's field
      const binder = freshName(`_m${mergeBinder++}`);
      // someBody is the unwrapped present value; transform re-wraps each arm in
      // the backend's Some constructor (Dafny `Some`, Lean `Option.some`).
      return { name: f.name, value: {
        kind: "someMatch", scrutinee: ovf, binder, binderTy: ft.inner,
        someBody: { kind: "var", name: binder, ty: ft.inner }, noneBody: bvf, ty: ft,
      } };
    }),
  });
  if (tover.ty.kind === "nullish" || (tover.ty.kind === "optional" && tover.ty.fromNullish)) {
    // Nullish override: undefined/null spreads nothing → base unchanged; Value(v) merges.
    const isPresent: TExpr = {
      kind: "binop", op: "!=",
      left: tover, right: { kind: "var", name: "null", ty: { kind: "null" } },
      ty: { kind: "bool" },
    };
    const unwrappedOver: TExpr = { kind: "checkedUnwrap", expr: tover, ty: userTy };
    return { kind: "conditional", cond: isPresent, then: merged(tbase, unwrappedOver), else: tbase, ty: userTy };
  }
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
  const rec = declOfKind(ctx.typeDecls, objTy.name, "record");
  if (!rec?.fields) return null;
  const fieldByName = new Map(rec.fields.map(f => [f.name, f]));
  const fieldTy = (v: string): Ty => fieldByName.get(v)!.type ?? { kind: "unknown" };
  const field = (v: string): TExpr => ({ kind: "field", obj, field: v, ty: fieldTy(v) });

  // The key's members, and whether it's a datatype (named) or a bare string (inline).
  let values: string[] | null = null;
  let datatype: string | null = null;
  if (keyTy.kind === "user") {
    const keyEnum = declOfKind(ctx.typeDecls, keyTy.name, "string-union");
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

function resolveConstEnumMember(obj: RawExpr, name: string, ctx: Ctx): TExpr | undefined {
  if (obj.kind !== "var" || lookup(ctx.env, obj.name)) return undefined;
  const decl = ctx.typeDecls.find(d => d.name === obj.name);
  if (!decl?.constEnumMembers) return undefined;
  const member = decl.constEnumMembers.find(m => m.name === name);
  if (!member) throw new Error(`Unknown const enum member ${obj.name}.${name}`);
  return resolveExpr({ kind: "num", value: member.value }, ctx);
}

function resolveExpr(e: RawExpr, ctx: Ctx): TExpr {
  const expr = resolveExprInner(e, ctx);
  const out = { ...expr, ty: numericValueType(expr.ty, ctx.typeDecls) };
  if ("freshClone" in e && e.freshClone && (out.kind === "var" || out.kind === "field" || out.kind === "index" || out.kind === "call")) {
    return { ...out, freshClone: true };
  }
  return out;
}

function resolveExprInner(e: RawExpr, ctx: Ctx): TExpr {
  switch (e.kind) {
    case "var": {
      if (e.name === "undefined") return { kind: "var", name: "undefined", ty: { kind: "void" } };
      if (e.name === "null") return { kind: "var", name: "null", ty: { kind: "null" } };
      const entry = binding(ctx.env, e.name);
      if (entry?.argumentPack) {
        throw new Error(`cannot materialize callback rest parameter '${e.name}'; use its length or a constant indexed read`);
      }
      entry?.onRead?.();
      return entry?.value ?? { kind: "var", name: entry?.emittedName ?? e.name, ty: entry?.ty ?? { kind: "unknown" } };
    }

    case "num":
      if (!Number.isInteger(e.value)) return { kind: "num", value: e.value, ty: { kind: "real" } };
      return { kind: "num", value: e.value, ty: e.value >= 0 ? { kind: "nat" } : { kind: "int" } };

    // Always `int` (never `nat`, even when non-negative), carrying `big` so the
    // surrounding arithmetic picks bigint division semantics — see `isBigInt`.
    case "bigint":
      return { kind: "bigint", value: e.value, ty: { kind: "int", big: true } };

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
      const ty = (expr.ty.kind === "optional" || expr.ty.kind === "nullish") ? expr.ty.inner : expr.ty;
      return { ...expr, ty };
    }

    case "binop": {
      let left = resolveExpr(e.left, ctx);
      // && and ==> narrowing: left-side optional/nullish checks narrow the right side.
      // (For ==>, the premise is assumed in the conclusion — same principle.)
      let rightCtx = ctx;
      let rawRight = e.right;
      if (e.op === "&&" || e.op === "==>") {
        rightCtx = collectAndChainNarrowings(left, ctx);
      } else if (e.op === "||") {
        // Preserve direct single-optional var comparisons (`opt === null || x < opt`,
        // `excludeTag === undefined || getTagId(t) !== excludeTag`) for transform's
        // native mirrored match lowering, as long as the non-optional side doesn't
        // also depend on a variable narrowed by `left` and neither side is `Nullish<T>`;
        // narrow all other RHS shapes via checked reads.
        const orCtx = collectOrChainNarrowings(left, ctx);
        const narrowedVars = new Set<string>();
        for (let cur = orCtx.env; cur && cur !== ctx.env; cur = cur.parent) {
          narrowedVars.add(cur.name);
        }
        const leftTy = rawRight.kind === "binop" && rawRight.left.kind === "var" ? lookup(ctx.env, rawRight.left.name) : undefined;
        const rightTy = rawRight.kind === "binop" && rawRight.right.kind === "var" ? lookup(ctx.env, rawRight.right.name) : undefined;
        const leftIsOptVar = leftTy?.kind === "optional" && !leftTy.fromNullish;
        const rightIsOptVar = rightTy?.kind === "optional" && !rightTy.fromNullish;
        const isDirectSingleOptCmp =
          rawRight.kind === "binop" &&
          ["===", "!==", "<", "<=", ">", ">="].includes(rawRight.op) &&
          (leftIsOptVar !== rightIsOptVar) &&
          !rawExprMentionsAny(leftIsOptVar ? rawRight.right : rawRight.left, narrowedVars);
        if (!isDirectSingleOptCmp) {
          rightCtx = orCtx;
        }
      }
      let right = resolveExpr(rawRight, rightCtx);
      if (e.op === "===" || e.op === "!==" || e.op === "==" || e.op === "!=") {
        left = coerceStr(left, right.ty, ctx.typeDecls);
        right = coerceStr(right, left.ty, ctx.typeDecls);
        // Spec (`//@`) comparisons are proof-only, so they can't diverge at
        // runtime; only warn on executable code.
        if (!ctx.inSpec && refEqHazard(left.ty, ctx.typeDecls) && refEqHazard(right.ty, ctx.typeDecls)) {
          warnRefEq(e.op, left.ty, right.ty);
        }
      } else if (e.op === "in") {
        const keySlot = right.ty.kind === "map" ? right.ty.key
          : (right.ty.kind === "set" || right.ty.kind === "array") ? right.ty.elem : null;
        if (keySlot) left = coerceToTargetTy(left, keySlot, ctx.typeDecls);
      }
      let ty: Ty = { kind: "unknown" };
      // <==> is bool like the comparisons; unlike ==>, neither side narrows
      // the other (no premise to assume).
      if (["===", "!==", "==", "!=", ">=", "<=", ">", "<", "in", "<==>"].includes(e.op)) ty = { kind: "bool" };
      else if (e.op === "&&") ty = right.ty;
      else if (e.op === "||" && (left.ty.kind === "optional" || left.ty.kind === "nullish")) {
        // || undefined / || null / || nullable preserves the RHS nullability;
        // otherwise yields inner type.
        if (e.right.kind === "var" && e.right.name === "undefined") {
          ty = left.ty.kind === "optional" && optAbsent(left.ty) === "undefined"
            ? left.ty
            : { kind: "optional", inner: left.ty.inner };
        } else if (e.right.kind === "var" && e.right.name === "null") {
          ty = { kind: "optional", inner: left.ty.inner, absent: "null" };
        } else if (right.ty.kind === "optional" || right.ty.kind === "nullish") {
          ty = right.ty;
        } else {
          ty = left.ty.inner;
        }
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
      let expr = resolveExpr(e.expr, ctx);
      if (e.op === "typeof" && expr.kind === "var") {
        const storage = storageLookup(ctx.env, expr.name);
        if (storage?.kind === "user" && findSynthArrayUnion(storage.name, ctx.typeDecls)) {
          expr = { ...expr, ty: storage };
        }
      }
      const ty: Ty = e.op === "!" ? { kind: "bool" } : e.op === "typeof" ? { kind: "string" }
        : e.op === "-" && expr.ty.kind === "nat" ? { ...expr.ty, kind: "int" } : expr.ty;
      return { kind: "unop", op: e.op, expr, ty };
    }

    case "call": {
      // Extract rewrites spread min/max calls to a single sequence argument.
      if (e.fn.kind === "var" && (e.fn.name === "MaxOfSeq" || e.fn.name === "MinOfSeq") && e.args.length === 1) {
        const name = e.fn.name === "MaxOfSeq" ? "Math.max" : "Math.min";
        const { expr, types } = resolveMinMaxSequence(e.args[0], ctx, name);
        // Integral spreads retain the existing int helper/result, including
        // empty literals (whose nonemptiness obligation will fail verification).
        const ty: Ty = minMaxNumericTy(types, name).kind === "real" ? { kind: "real" } : { kind: "int" };
        // Integral helpers keep their historical call classification so method
        // temporaries in existing proof files remain byte-identical. Real calls
        // use the specialized lowering that promotes their sequence segments.
        return { kind: "call", fn: { kind: "var", name: e.fn.name, ty: { kind: "unknown" } },
          args: [expr], ty, callKind: ty.kind === "real" ? "pure" : classifyCall(e.fn, ctx) };
      }
      // perm(a, b): spec-only permutation predicate — true iff `a` and `b` are
      // reorderings of each other (equal as multisets). Lowers to the `Perm`
      // preamble (Dafny `multiset(a) == multiset(b)`; Lean `a.toList ~ b.toList`).
      // It has no runtime counterpart, so it is rejected outside `//@` specs.
      if (e.fn.kind === "var" && e.fn.name === "perm" && e.args.length === 2) {
        if (!ctx.inSpec) throw new Error("perm(a, b) may only be used in //@ specifications");
        const a = resolveExpr(e.args[0], ctx);
        const b = resolveExpr(e.args[1], ctx);
        // Let the backend check argument types, including calls to proof helpers.
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
      // rest of the pipeline sees an ordinary named call. Pure externs remain
      // expressions; `//@ impure` externs are lifted as method calls.
      if (e.fn.kind === "field" && e.fn.obj.kind === "var") {
        const qualified = `${e.fn.obj.name}.${e.fn.field}`;
        const ext = ctx.externs.get(qualified);
        if (ext) {
          if (ext.impure && ctx.inSpec)
            throw new Error(`impure extern ${qualified} cannot be called from a specification`);
          if (ext.impure && ctx.inLambda)
            throw new Error(`impure extern ${qualified} cannot be called from a lambda`);
          const args = projectStructuralCallArgs(e.args.map(a => resolveExpr(a, ctx)), ext.params, ctx);
          const fn: TExpr = { kind: "var", name: ext.flat, ty: { kind: "unknown" } };
          return {
            kind: "call", fn, args, ty: ext.returnTy,
            callKind: ext.impure ? "method" : "pure",
            paramTys: ext.params,
          };
        }
      }
      const fn = resolveExpr(e.fn, ctx);
      const builtinId = fn.kind === "field" ? recognizeBuiltin(fn.obj.ty, fn.field) : null;
      const bSpec = builtinId ? builtinSpec(builtinId) : null;
      const rawArgs = inferLambdaParamTypes(fn, e.args, ctx);
      // Propagate parameter / builtin-slot types to arguments for record literal
      // resolution and collection element/key/value coercion (e.g., narrowed `T`
      // or literals passed into `Set<T | null>.has`, `Map<K | null, V>.set`, etc.).
      const paramTypes = fn.kind === "var" && !binding(ctx.env, fn.name) ? ctx.fnParams.get(fn.name) ?? null : null;
      const initial = fn.kind === "field" && fn.field === "reduce" && rawArgs.length >= 2
        ? resolveExpr(rawArgs[1], ctx) : undefined;
      const callback = callbackContext(fn, initial);
      let args = coerceCallArgs(rawArgs.map((a, i) => {
        const slotTy = (paramTypes && i < paramTypes.length ? paramTypes[i] : null)
          ?? (bSpec?.argSlot && fn.kind === "field" ? bSpec.argSlot(fn.obj.ty, i) : null);
        let aCtx = ctx;
        if (slotTy &&
            (slotTy.kind === "user" || slotTy.kind === "array" || slotTy.kind === "optional" || slotTy.kind === "nullish")) {
          aCtx = { ...aCtx, returnTy: slotTy };
        }
        if (i === 0 && a.kind === "lambda" && callback)
          return resolveCallback(a, callback.actual, callback.baseArity, aCtx);
        const resolved = i === 1 && initial ? initial : resolveExpr(a, aCtx);
        if (bSpec?.argSlot && fn.kind === "field") {
          const bSlot = bSpec.argSlot(fn.obj.ty, i);
          if (bSlot) return coerceToTargetTy(resolved, bSlot, ctx.typeDecls);
        }
        return resolved;
      }), fn, ctx);
      if (paramTypes) args = projectStructuralCallArgs(args, paramTypes, ctx);
      // Keep the underlying synth array-union storage type on `Array.isArray(x)`
      // arguments even when `x` was already narrowed in flow typing.
      if (fn.kind === "field" && fn.field === "isArray" &&
          fn.obj.kind === "var" && fn.obj.name === "Array" && args.length === 1 && args[0].kind === "var") {
        const storage = storageLookup(ctx.env, args[0].name);
        if (storage?.kind === "user" && findSynthArrayUnion(storage.name, ctx.typeDecls)) {
          args = [{ ...args[0], ty: storage }];
        }
      }
      let ty = inferMethodReturnTy(fn, args, ctx);
      // For same-file function calls, use the known return type
      if (ty.kind === "unknown" && fn.kind === "var" && !binding(ctx.env, fn.name) && ctx.fnReturns.has(fn.name)) {
        ty = ctx.fnReturns.get(fn.name)!;
      }
      // BigInt(n) / Number(n) between integer types: identity on the model's int.
      if (ty.kind === "unknown" && fn.kind === "var" && (fn.name === "BigInt" || fn.name === "Number") &&
          args.length === 1 && (args[0].ty.kind === "int" || args[0].ty.kind === "nat")) {
        ty = fn.name === "BigInt" ? { kind: "int", big: true } : { kind: "int" };
      }
      // Call through a function-typed value: its fn type carries the result
      if (ty.kind === "unknown" && fn.ty.kind === "fn") ty = fn.ty.result;
      // filterMap: `seqOfOption.filter(x => x !== undefined)` (a defined-check,
      // typically with an `x is T` type guard) drops the Nones AND unwraps to
      // seq<T>. Rewrite to a synthetic `filterSome` call lowered to the proven
      // SeqFilterSome preamble (a plain `Map(.value, Filter(.Some?))` wouldn't
      // verify — `.value` is partial).
      const filterSentinel = e.fn.kind === "field" && e.fn.field === "filter" && e.args.length === 1
        ? definedCheckRawLambdaSentinel(e.args[0]) : null;
      if (filterSentinel !== null
          && fn.kind === "field" && fn.obj.ty.kind === "array" && fn.obj.ty.elem.kind === "optional"
          && (filterSentinel === "both" || filterSentinel === optAbsent(fn.obj.ty.elem))) {
        return { kind: "call", fn: { ...fn, field: "filterSome" }, args: [], ty: { kind: "array", elem: fn.obj.ty.elem.inner }, callKind: "method" };
      }
      return { kind: "call", fn, args, ty, callKind: classifyCall(e.fn, ctx),
        ...(builtinId ? { builtinId } : {}),
        ...(paramTypes ? { paramTys: paramTypes } : {}) };
    }

    case "index": {
      const pack = argumentPack(e.obj, ctx);
      if (pack && e.idx.kind === "num" && Number.isInteger(e.idx.value) && e.idx.value >= 0) {
        return pack.at(e.idx.value);
      }
      if (e.idx.kind === "str") {
        const member = resolveConstEnumMember(e.obj, e.idx.value, ctx);
        if (member) return member;
      }
      const obj = resolveExpr(e.obj, ctx);
      let idx = resolveExpr(e.idx, ctx);
      // Map bracket access: default to Option<V>. But if the enclosing scope has a
      // known `k in m` atom matching (obj, idx) — from requires, assert, an enclosing
      // `if (k in m)`, or a loop invariant — narrow to V. Parallels how `narrowedPaths`
      // narrows `obj.field.field` under optional-undefined checks.
      let idxTy: Ty;
      if (obj.ty.kind === "array") {
        idxTy = obj.ty.elem;
      } else if (obj.ty.kind === "string") {
        idxTy = { kind: "string" };
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
        idx = coerceToTargetTy(idx, obj.ty.key, ctx.typeDecls);
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
      const pack = argumentPack(e.obj, ctx);
      if (pack && e.field === "length") return { kind: "num", value: pack.length, ty: { kind: "nat" } };
      const member = resolveConstEnumMember(e.obj, e.field, ctx);
      if (member) return member;
      const obj = resolveExpr(e.obj, ctx);
      let isDiscriminant = false;
      let ty: Ty = { kind: "unknown" };

      // Check narrowed path context (from conditional optional checks).
      // Applies when the current field-access forms a pure access path AND
      // that path is in the narrowedPaths list.
      if (ctx.narrowedPaths.length > 0) {
        const myPath = asRawAccessPath(e);
        if (myPath) {
          for (let i = ctx.narrowedPaths.length - 1; i >= 0; i--) {
            if (accessPathsEqual(ctx.narrowedPaths[i]!.path, myPath)) {
              ty = ctx.narrowedPaths[i]!.narrowedTy;
              break;
            }
          }
        }
      }

      // A variant narrowing on the object pins `ofVariant` (even when `myPath`
      // itself was also narrowed in `narrowedPaths`, e.g. a nested union) and
      // supplies the field's type when not already narrowed.
      let ofVariant: string | undefined;
      if (ctx.narrowedPaths.length > 0 && obj.ty.kind === "user") {
        const objPath = asRawAccessPath(e.obj);
        let np: NarrowedPath | undefined;
        if (objPath) {
          for (let i = ctx.narrowedPaths.length - 1; i >= 0; i--) {
            const cand = ctx.narrowedPaths[i]!;
            if (cand.variant && accessPathsEqual(cand.path, objPath)) { np = cand; break; }
          }
        }
        if (np?.variant) {
          const decl = findDecl(ctx, tyBaseName(obj.ty.name));
          const f = decl?.variants?.find(v => v.name === np.variant)?.fields.find(f => f.name === e.field);
          if (f?.type) {
            ofVariant = np.variant;
            if (ty.kind === "unknown") ty = f.type;
          }
        }
      }

      if (ty.kind === "unknown") {
        const lookup = lookupFieldTy(obj.ty, e.field, ctx);
        ty = lookup.ty;
        isDiscriminant = lookup.isDiscriminant;
      }

      return { kind: "field", obj, field: e.field, ty, isDiscriminant, ofVariant };
    }

    case "nullish": {
      // left ?? right — result type is left's inner (when left is optional/nullish)
      // or just left's type, unified with right's type.
      const left = resolveExpr(e.left, ctx);
      const isLeftNullishLit = (left.kind === "var" && (left.name === "undefined" || left.name === "null")) ||
        left.ty.kind === "void" || left.ty.kind === "null";
      const isArrayIndex = left.kind === "index" && left.obj.ty.kind === "array";
      const isLeftNullable = left.ty.kind === "optional" || left.ty.kind === "nullish";
      const inner: Ty = (left.ty.kind === "optional" || left.ty.kind === "nullish") ? left.ty.inner : left.ty;
      // The default shares the result type, so coerce a string literal to a
      // string-union enum (e.g. `availableLevels[0] ?? "off"`).
      const right = coerceToTargetTy(resolveExpr(e.right, ctx), isLeftNullishLit ? { kind: "unknown" } : inner, ctx.typeDecls);
      // When `left` is non-nullable and not an unchecked array index (#352):
      // `undefined ?? right` / `null ?? right` has `right`'s type, and `nonOpt ?? right`
      // evaluates to `left` directly (narrow.ts strips the dead fallback).
      if (!isLeftNullable && !isArrayIndex) {
        return { kind: "nullish", left, right, ty: isLeftNullishLit ? right.ty : left.ty };
      }
      // `??` is only total when its default is: with a nullable/null/undefined
      // right operand (`x ?? undefined`, `ruleA(e) ?? ruleB(e) ?? null`), the
      // result keeps the right operand's nullability.
      let ty: Ty = inner;
      if (right.ty.kind === "optional" || right.ty.kind === "nullish") ty = right.ty;
      else if (right.ty.kind === "void" || (right.kind === "var" && right.name === "undefined")) ty = { kind: "optional", inner };
      else if (right.ty.kind === "null" || (right.kind === "var" && right.name === "null")) ty = { kind: "optional", inner, absent: "null" };
      return { kind: "nullish", left, right, ty };
    }

    case "optChain": {
      // obj?.<chain> — obj has type Option<T> or Nullish<T>; we walk the chain
      // stepping through types from T. Short-circuiting always yields `undefined`
      // in JS (so a `T | null` chain step becomes `Nullish<T>`).
      const obj = resolveExpr(e.obj, ctx);
      const isObjNullishLit = (obj.kind === "var" && (obj.name === "undefined" || obj.name === "null")) ||
        obj.ty.kind === "void" || obj.ty.kind === "null";
      const isObjArrayIndex = obj.kind === "index" && obj.obj.ty.kind === "array";
      const isObjNullable = obj.ty.kind === "optional" || obj.ty.kind === "nullish";
      let stepInTy = (obj.ty.kind === "optional" || obj.ty.kind === "nullish") ? obj.ty.inner : obj.ty;
      const chain: import("./typedir.js").TChainStep[] = [];
      for (const step of e.chain) {
        if (step.kind === "field") {
          const fieldTy = lookupFieldTy(stepInTy, step.name, ctx).ty;
          chain.push({ kind: "field", name: step.name, ty: fieldTy });
          stepInTy = fieldTy;
        } else if (step.kind === "index") {
          let idx = resolveExpr(step.idx, ctx);
          if (stepInTy.kind === "map") idx = coerceToTargetTy(idx, stepInTy.key, ctx.typeDecls);
          const idxTy: Ty = stepInTy.kind === "array" ? stepInTy.elem
            : stepInTy.kind === "string" ? { kind: "string" }
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
              : ((obj.ty.kind === "optional" || obj.ty.kind === "nullish") ? obj.ty.inner : obj.ty);
            const fakeObj: TExpr = { kind: "var", name: "_chain_recv", ty: priorInTy };
            const fakeFn: TExpr = { kind: "field", obj: fakeObj, field: lastField.name, ty: lastField.ty };
            const builtinId = recognizeBuiltin(priorInTy, lastField.name);
            const bSpec = builtinId ? builtinSpec(builtinId) : null;
            rawArgs = inferLambdaParamTypes(fakeFn, rawArgs);
            const initial = lastField.name === "reduce" && rawArgs.length >= 2 ? resolveExpr(rawArgs[1], ctx) : undefined;
            const callback = callbackContext(fakeFn, initial);
            const args = rawArgs.map((a, i) => {
              const slotTy = bSpec?.argSlot ? bSpec.argSlot(priorInTy, i) : null;
              const aCtx = slotTy && (slotTy.kind === "user" || slotTy.kind === "array" || slotTy.kind === "optional" || slotTy.kind === "nullish")
                ? { ...ctx, returnTy: slotTy } : ctx;
              const resolved = i === 0 && a.kind === "lambda" && callback
                ? resolveCallback(a, callback.actual, callback.baseArity, aCtx)
                : i === 1 && initial ? initial : resolveExpr(a, aCtx);
              return slotTy ? coerceToTargetTy(resolved, slotTy, ctx.typeDecls) : resolved;
            });
            callTy = inferMethodReturnTy(fakeFn, args, ctx);
            callKind = "method";
            chain.push({ kind: "call", args, ty: callTy, callKind,
              ...(builtinId ? { builtinId } : {}) });
            stepInTy = callTy;
            continue;
          }
          const args = rawArgs.map(a => resolveExpr(a, ctx));
          chain.push({ kind: "call", args, ty: callTy, callKind });
          stepInTy = callTy;
        }
      }
      const finalTy = stepInTy;
      // Non-optional receiver (excluding unchecked array index) never produces
      // None from the `?.` step itself (#352); narrow.ts lowers it directly.
      // When the receiver IS nullable, short-circuiting adds `| undefined`:
      //   - `T | null` + `| undefined` → `Nullish<T>`
      //   - `Nullish<T>` → `Nullish<T>`
      //   - `T | undefined` → `T | undefined`
      //   - `T` → `T | undefined`
      const ty: Ty = isObjNullishLit ? { kind: "void" }
        : (!isObjNullable && !isObjArrayIndex) ? finalTy
        : finalTy.kind === "nullish" ? finalTy
        : finalTy.kind === "optional"
          ? (optAbsent(finalTy) === "null" ? { kind: "nullish", inner: finalTy.inner } : finalTy)
          : { kind: "optional", inner: finalTy };
      return { kind: "optChain", obj, chain, ty };
    }

    case "record": {
      const spread = e.spread ? resolveExpr(e.spread, ctx) : null;
      const asserted = e.assertedTsType && expandAlias(parseTsType(e.assertedTsType), ctx.typeDecls);
      const assertedUnion = asserted && asserted.kind === "user" &&
        declOfKind(ctx.typeDecls, asserted.name, "discriminated-union");
      const ty = spread ? spread.ty : assertedUnion ? asserted : { kind: "unknown" as const };
      // Record literal in map-typed context (e.g. `const M: Record<string, V> = {a: ...}`):
      // attach the map type so transform/emit can produce a map literal.
      if (!spread && ctx.returnTy.kind === "map") {
        const mapTy = ctx.returnTy;
        const fieldCtx = { ...ctx, returnTy: mapTy.value };
        const fields = e.fields.map(f => ({ name: f.name, value: resolveExpr(f.value, fieldCtx) }));
        return { kind: "record", spread: null, fields, ty: mapTy };
      }
      // Infer record type: from spread, or from return type context. Unwrap
      // an outer Optional/Nullish when looking at returnTy — `return {...} : null`
      // has ctx.returnTy = Option<T>/Nullish<T>, but the record literal's natural type is T.
      const returnTyUnwrapped = (ctx.returnTy.kind === "optional" || ctx.returnTy.kind === "nullish") ? ctx.returnTy.inner : ctx.returnTy;
      const recordTy = ty.kind === "user" ? ty : returnTyUnwrapped.kind === "user" ? returnTyUnwrapped : null;
      const decl = recordTy ? declOfKind(ctx.typeDecls, recordTy.name, "record") : undefined;
      // Union-variant literal or spread in union-typed context: contextual field
      // types come from the variant selected by the literal's discriminant field,
      // or from the narrowed variant of the spread path.
      let declFields = decl?.fields;
      let ofVariant: string | undefined;
      let spreadOfVariant: string | undefined;
      if (!declFields && recordTy) {
        const udecl = declOfKind(ctx.typeDecls, tyBaseName(recordTy.name), "discriminated-union");
        if (udecl?.discriminant && udecl.variants) {
          if (spread) {
            const spPath = asTExprAccessPath(spread);
            spreadOfVariant = spPath ? lookupNarrowedVariant(spPath, ctx) : undefined;
          }
          const tagRaw = e.fields.find(f => f.name === udecl.discriminant)?.value;
          if (tagRaw?.kind === "str" || tagRaw?.kind === "bool") {
            ofVariant = String(tagRaw.value);
            declFields = udecl.variants.find(v => v.name === ofVariant)?.fields;
          } else if (spread && !tagRaw && spreadOfVariant) {
            ofVariant = spreadOfVariant;
            declFields = udecl.variants.find(v => v.name === spreadOfVariant)?.fields;
          }
        }
      }
      // Clear returnTy for field values — it applies to THIS record, not nested ones
      const fieldCtx = recordTy ? { ...ctx, returnTy: { kind: "unknown" as const } as Ty } : ctx;
      const fields = e.fields.map(f => {
        const fieldDecl = declFields?.find(df => df.name === f.name);
        // Propagate declared field type into context so nested records resolve
        // their union variant correctly (e.g., { kind: 'Idle' } → EffectMode.Idle).
        // Optional fields propagate their inner type (the Some-wrap is restored
        // by coerceToTargetTy below); array fields propagate whole, so the
        // arrayLiteral case can thread the element type.
        const fdTy = fieldDecl?.type;
        const fdCtxTy = (fdTy?.kind === "optional" || fdTy?.kind === "nullish") ? fdTy.inner : fdTy;
        const valueCtx = fdCtxTy && (fdCtxTy.kind === "user" || fdCtxTy.kind === "array")
          ? { ...fieldCtx, returnTy: fdCtxTy }
          : fieldCtx;
        let value = resolveExpr(f.value, valueCtx);
        if (fieldDecl) {
          const declTy = fieldDecl.type!;
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
      return {
        kind: "record",
        spread,
        fields,
        ty: recordTy ?? ty,
        ...(ofVariant ? { ofVariant } : {}),
        ...(spreadOfVariant ? { spreadOfVariant } : {}),
      };
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
      const bound = quantified(ctx.env, e.var, varTy);
      return { kind: "forall", var: bound.emittedName ?? e.var, varTy, body: resolveExpr(e.body, withEnv(ctx, bound)), ty: { kind: "bool" } };
    }

    case "exists": {
      const varTy: Ty = e.varType !== "int" ? parseTsType(e.varType)
        : inferQuantVarType(e.var, e.body, ctx) ?? { kind: "int" };
      const bound = quantified(ctx.env, e.var, varTy);
      return { kind: "exists", var: bound.emittedName ?? e.var, varTy, body: resolveExpr(e.body, withEnv(ctx, bound)), ty: { kind: "bool" } };
    }

    case "arrayLiteral": {
      // Expected-tuple context: type each element against its own slot type and
      // produce a tuple literal (`[1, "a"]: [number, string]`).
      if (ctx.returnTy.kind === "tuple") {
        const slots = ctx.returnTy.elems;
        const elems = e.elems.map((el, i) => {
          const slot = slots[i];
          const r = resolveExpr(el, slot ? { ...ctx, returnTy: slot } : ctx);
          return slot ? coerceToTargetTy(r, slot, ctx.typeDecls) : r;
        });
        return { kind: "arrayLiteral", elems, ty: { kind: "tuple", elems: elems.map(x => x.ty) } };
      }
      // Thread the expected element type into each element, so a record/union
      // literal in an array resolves to its named datatype rather than an
      // anonymous tuple (mirrors return-position and call-argument records, which
      // get their type via ctx.returnTy). Only narrow when the context type is an
      // array (unwrapping one optional level — `TStmt[] | null` return positions);
      // otherwise leave ctx untouched.
      const rtUnwrapped = (ctx.returnTy.kind === "optional" || ctx.returnTy.kind === "nullish") ? ctx.returnTy.inner : ctx.returnTy;
      const expectedElem = rtUnwrapped.kind === "array" ? rtUnwrapped.elem : null;
      const elemCtx = expectedElem ? { ...ctx, returnTy: expectedElem } : ctx;
      const elems = e.elems.map(el => {
        const r = resolveExpr(el, elemCtx);
        // Coerce a bare string-literal element to a string-union enum (e.g.
        // `["off", …]: ModelThinkingLevel[]`), like return/arg positions.
        return expectedElem ? coerceToTargetTy(r, expectedElem, ctx.typeDecls) : r;
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
        ...(p.rest ? { rest: true as const } : {}),
        ...(p.defaultValue ? { defaultValue: resolveExpr(p.defaultValue, ctx) } : {}),
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
      // Carry the lambda's type as a fn type when its return is known (or when
      // zero-parameter, so Lean emits `Unit → T` and applies `()` at call sites).
      const lamTy: Ty = e.returnTsType || params.length === 0
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
      let thenCtx = collectAndChainNarrowings(cond, ctx);
      let elseCtx = ctx;

      // Truthiness — cond itself is optional/nullish (`opt ? a : b`), only for simple vars.
      if ((cond.ty.kind === "optional" || cond.ty.kind === "nullish") && cond.kind === "var") {
        thenCtx = withEnv(thenCtx, refine(thenCtx.env, cond.name, cond.ty.inner));
      }

      // Negated presence check (single or `||`-chain, var or field path) narrows else-branch.
      const single = negatedVarPresence(cond);
      if (single) {
        elseCtx = withEnv(elseCtx, refine(elseCtx.env, single.varName, single.innerTy));
      } else if (cond.kind === "binop" && cond.op === "||") {
        for (const n of collectEarlyReturnNarrowings(cond)) {
          elseCtx = withEnv(elseCtx, refine(elseCtx.env, n.varName, n.innerTy));
        }
      }
      const negPaths = collectEarlyReturnPathNarrowings(cond, ctx);
      if (negPaths.length > 0) {
        elseCtx = { ...elseCtx, narrowedPaths: [...elseCtx.narrowedPaths, ...negPaths] };
      }
      const elseVariant = discriminantVariantWhen(cond, false, ctx);
      if (elseVariant) {
        elseCtx = { ...elseCtx, narrowedPaths: [...elseCtx.narrowedPaths, elseVariant] };
      }
      const elseSynth = synthVariantWhen(cond, false, ctx);
      if (elseSynth) {
        elseCtx = applyVariantNarrowing(elseCtx, elseSynth.path, elseSynth.unionTy, elseSynth.variant);
      }
      // Map-index narrowing: `k in m` in the cond narrows the then-branch; `!(k in m)`
      // narrows the else-branch. Parallel to the if-statement hook in resolveStmt.
      thenCtx = withInAtoms(thenCtx, extractInAtoms(cond));
      elseCtx = withInAtoms(elseCtx, extractInAtomsNegated(cond));

      let then_ = resolveExpr(e.then, thenCtx);
      let else_ = resolveExpr(e.else, elseCtx);
      then_ = coerceStr(then_, else_.ty, ctx.typeDecls);
      else_ = coerceStr(else_, then_.ty, ctx.typeDecls);
      const ty = conditionalResultTy(then_.ty, else_.ty);
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

function resolveSpecs(specs: string[], ctx: Ctx, threadAcrossSpecs = false): TExpr[] {
  const result: TExpr[] = [];
  let specCtx = ctx;
  for (const spec of specs) {
    let clauseCtx = specCtx;
    for (const clause of splitConj(parseExpr(spec))) {
      const resolved = resolveExpr(clause, clauseCtx);
      result.push(resolved);
      clauseCtx = collectAndChainNarrowings(resolved, clauseCtx);
    }
    if (threadAcrossSpecs) specCtx = clauseCtx;
  }
  return result;
}

function splitConj(e: RawExpr): RawExpr[] {
  if (e.kind === "binop" && e.op === "&&") return [...splitConj(e.left), ...splitConj(e.right)];
  return [e];
}

// ── Resolve statements ───────────────────────────────────────

/** True if `e` references any variable name in `names`. */
function rawExprMentionsAny(e: RawExpr, names: Set<string>): boolean {
  if (names.size === 0) return false;
  switch (e.kind) {
    case "var": return names.has(e.name);
    case "num": case "bigint": case "str": case "bool": case "havoc": return false;
    case "binop": return rawExprMentionsAny(e.left, names) || rawExprMentionsAny(e.right, names);
    case "unop": case "nonNull": return rawExprMentionsAny(e.expr, names);
    case "field": return rawExprMentionsAny(e.obj, names);
    case "index": return rawExprMentionsAny(e.obj, names) || rawExprMentionsAny(e.idx, names);
    case "call": return rawExprMentionsAny(e.fn, names) || e.args.some(a => rawExprMentionsAny(a, names));
    case "record":
      return (e.spread ? rawExprMentionsAny(e.spread, names) : false) ||
        e.fields.some(f => rawExprMentionsAny(f.value, names));
    case "arrayLiteral": return e.elems.some(el => rawExprMentionsAny(el, names));
    case "conditional":
      return rawExprMentionsAny(e.cond, names) || rawExprMentionsAny(e.then, names) || rawExprMentionsAny(e.else, names);
    case "nullish": return rawExprMentionsAny(e.left, names) || rawExprMentionsAny(e.right, names);
    case "optChain": return rawExprMentionsAny(e.obj, names);
    case "forall": case "exists": return rawExprMentionsAny(e.body, names);
    case "lambda": return false;
    default: return false;
  }
}

/** Collect root variable names assigned anywhere in `stmts` (both direct
 *  assignments `x = ...` and dotted field writes `x.f = ...`). */
function collectAssignedRootsRaw(stmts: RawStmt[], out = new Set<string>()): Set<string> {
  for (const s of stmts) {
    if (s.kind === "assign") {
      out.add(s.target.split(".")[0]!);
    } else if (s.kind === "if") {
      collectAssignedRootsRaw(s.then, out);
      collectAssignedRootsRaw(s.else, out);
    } else if (s.kind === "while" || s.kind === "forof") {
      collectAssignedRootsRaw(s.body, out);
    } else if (s.kind === "switch") {
      for (const c of s.cases) collectAssignedRootsRaw(c.body, out);
      collectAssignedRootsRaw(s.defaultBody, out);
    }
  }
  return out;
}

/** True when `npPath` is at or below dotted `target` (e.g. target `"b.count"`
 *  invalidates `b.count` and `b.count.x`, but preserves `b` itself). */
function pathAtOrBelowTarget(npPath: AccessPath, target: string): boolean {
  const parts = target.split(".");
  if (npPath.rootVar !== parts[0]) return false;
  const targetFields = parts.slice(1);
  if (npPath.fields.length < targetFields.length) return false;
  return targetFields.every((f, i) => npPath.fields[i] === f);
}

/** Collect whole-variable assignment roots and dotted field-write targets
 *  separately, so sub-field writes (`sh.y = 10`) do not drop the parent's
 *  discriminated-union variant narrowing while whole-var writes (`sh = ...`) do. */
function collectAssignedTargetsRaw(
  stmts: RawStmt[],
  wholeRoots = new Set<string>(),
  dottedTargets = new Set<string>(),
): { wholeRoots: Set<string>; dottedTargets: Set<string> } {
  for (const s of stmts) {
    if (s.kind === "assign") {
      if (s.target.includes(".")) dottedTargets.add(s.target);
      else wholeRoots.add(s.target);
    } else if (s.kind === "if") {
      collectAssignedTargetsRaw(s.then, wholeRoots, dottedTargets);
      collectAssignedTargetsRaw(s.else, wholeRoots, dottedTargets);
    } else if (s.kind === "while" || s.kind === "forof") {
      collectAssignedTargetsRaw(s.body, wholeRoots, dottedTargets);
    } else if (s.kind === "switch") {
      for (const c of s.cases) collectAssignedTargetsRaw(c.body, wholeRoots, dottedTargets);
      collectAssignedTargetsRaw(s.defaultBody, wholeRoots, dottedTargets);
    }
  }
  return { wholeRoots, dottedTargets };
}

/** Restore any narrowed optional/nullish/synth-union variable in `wholeRoots`
 *  back to its declared `storageTy`, drop `narrowedPaths` rooted at `wholeRoots`,
 *  and drop `narrowedPaths` at or below any `dottedTargets` (preserving parent
 *  discriminated-union variants on sub-field writes). */
function invalidateNarrowings(
  env: Env | null,
  narrowedPaths: NarrowedPath[],
  wholeRoots: Set<string>,
  dottedTargets: Set<string>,
  typeDecls: TypeDeclInfo[],
): { env: Env | null; narrowedPaths: NarrowedPath[] } {
  if (wholeRoots.size === 0 && dottedTargets.size === 0) return { env, narrowedPaths };
  let nextEnv = env;
  for (const root of wholeRoots) {
    const cur = lookup(nextEnv, root);
    const storage = storageLookup(nextEnv, root);
    const isNarrowableStorage = storage?.kind === "optional" || storage?.kind === "nullish" ||
      (storage?.kind === "user" && !!findSynthArrayUnion(storage.name, typeDecls));
    if (isNarrowableStorage && cur && !tyEqual(cur, storage)) {
      nextEnv = refine(nextEnv, root, storage);
    }
  }
  const nextPaths = narrowedPaths.filter(np => {
    if (wholeRoots.has(np.path.rootVar)) return false;
    for (const dt of dottedTargets) {
      if (pathAtOrBelowTarget(np.path, dt)) return false;
    }
    return true;
  });
  return { env: nextEnv, narrowedPaths: nextPaths };
}

/** True if `stmts` definitely assigns a non-optional/non-nullish value
 *  to `varName` (without subsequently clearing or shadowing it) on every
 *  non-terminating exit path. Used for `#340` assignment narrowing:
 *  `if (v === undefined) { v = 6; } return v + 3;`. */
function definitelyAssignsNonOptional(stmts: RawStmt[], varName: string, ctx: Ctx): boolean {
  let assigned = false;
  let env = ctx.env;
  const targetStorage = storageLookup(env, varName);
  for (const st of stmts) {
    if (isTerminatorKind(st.kind)) return true;
    if (st.kind === "let") {
      // Inner `let` shadowing `varName` prevents outer assignment tracking.
      if (st.name === varName) return assigned;
      const [, nextEnv] = resolveStmt(st, { ...ctx, env });
      env = nextEnv;
      continue;
    }
    if (st.kind === "assign" && st.target === varName) {
      if (st.value.kind === "var" && (st.value.name === "undefined" || st.value.name === "null")) {
        assigned = false;
      } else {
        const rhsCtx: Ctx = { ...ctx, env, returnTy: targetStorage ?? ctx.returnTy };
        const rhsTy = resolveExpr(st.value, rhsCtx).ty;
        assigned = rhsTy.kind !== "optional" && rhsTy.kind !== "nullish" &&
          rhsTy.kind !== "void" && rhsTy.kind !== "null" && rhsTy.kind !== "unknown";
      }
    } else if (st.kind === "if") {
      const subCtx: Ctx = { ...ctx, env };
      if (st.else.length > 0 &&
          definitelyAssignsNonOptional(st.then, varName, subCtx) &&
          definitelyAssignsNonOptional(st.else, varName, subCtx)) {
        assigned = true;
      } else if (collectAssignedRootsRaw(st.then).has(varName) || collectAssignedRootsRaw(st.else).has(varName)) {
        assigned = false;
      }
    } else if (st.kind === "while" || st.kind === "forof") {
      if (collectAssignedRootsRaw(st.body).has(varName)) assigned = false;
    } else if (st.kind === "switch") {
      const swAssigned = sHasRootAssignSwitch(st, varName);
      if (swAssigned) assigned = false;
    }
  }
  return assigned;
}

function sHasRootAssignSwitch(s: Extract<RawStmt, { kind: "switch" }>, varName: string): boolean {
  for (const c of s.cases) {
    if (collectAssignedRootsRaw(c.body).has(varName)) return true;
  }
  return collectAssignedRootsRaw(s.defaultBody).has(varName);
}

function resolveBlock(stmts: RawStmt[], ctx: Ctx): TStmt[] {
  const result: TStmt[] = [];
  let env = ctx.env;
  let narrowedIndices = ctx.narrowedIndices;
  let narrowedPaths = ctx.narrowedPaths;
  for (const s of stmts) {
    const currentCtx = { ...ctx, env, narrowedIndices, narrowedPaths };
    const [typed, nextEnv] = resolveStmt(s, currentCtx);
    result.push(typed);
    env = nextEnv;
    // Assignment narrowing (#340) & union reassignment tracking (#405):
    // assigning a non-optional value to an optional variable or field narrows it;
    // assigning a variant literal / same-variant spread / synth array-union
    // updates its narrowed variant; dotted field writes only drop narrowings
    // at or below the written path (keeping the parent's union variant intact).
    if (s.kind === "assign") {
      const parts = s.target.split(".");
      const root = parts[0]!;
      const isNullLit = s.value.kind === "var" && s.value.name === "null";
      const isUndefLit = s.value.kind === "var" && s.value.name === "undefined";
      const isDefinitelyPresent = (targetStorage: Ty): boolean => {
        if (isUndefLit || isNullLit) return false;
        const rhsCtx: Ctx = { ...currentCtx, returnTy: targetStorage };
        const rawTy = resolveExpr(s.value, rhsCtx).ty;
        return rawTy.kind !== "optional" && rawTy.kind !== "nullish" &&
          rawTy.kind !== "void" && rawTy.kind !== "null" && rawTy.kind !== "unknown";
      };
      if (parts.length > 1) {
        const rootStorage = storageLookup(env, root);
        const udecl = rootStorage?.kind === "user"
          ? declOfKind(ctx.typeDecls, tyBaseName(rootStorage.name), "discriminated-union")
          : undefined;
        const writesDiscriminant = parts.length === 2 && udecl?.discriminant === parts[1];
        narrowedPaths = narrowedPaths.filter(np =>
          writesDiscriminant ? np.path.rootVar !== root : !pathAtOrBelowTarget(np.path, s.target));
        // Dotted assignment to an optional/nullish field (`box.val = 5`):
        // re-narrow that path when the RHS is definitely present.
        let fieldTy: Ty | undefined = rootStorage;
        for (let i = 1; i < parts.length && fieldTy; i++) {
          const cur = (fieldTy.kind === "optional" || fieldTy.kind === "nullish") ? fieldTy.inner : fieldTy;
          fieldTy = lookupFieldTy(cur, parts[i]!, currentCtx).ty;
        }
        if ((fieldTy?.kind === "optional" || fieldTy?.kind === "nullish") && isDefinitelyPresent(fieldTy)) {
          narrowedPaths = [...narrowedPaths, { path: { rootVar: root, fields: parts.slice(1) }, narrowedTy: fieldTy.inner }];
        }
      } else {
        narrowedPaths = narrowedPaths.filter(np => np.path.rootVar !== s.target);
        const storage = storageLookup(env, s.target);
        if (storage?.kind === "optional" || storage?.kind === "nullish") {
          env = refine(env, s.target, isDefinitelyPresent(storage) ? storage.inner : storage);
        } else if (storage?.kind === "user") {
          const synth = findSynthArrayUnion(storage.name, ctx.typeDecls);
          if (synth && typed.kind === "assign") {
            if (typed.value.kind === "call" && typed.value.fn.kind === "var" &&
                (typed.value.fn.name === "ArrayBranch" || typed.value.fn.name === "NonArrayBranch")) {
              const payload = synthVariantPayloadTy(storage, typed.value.fn.name, currentCtx);
              if (payload) {
                env = refine(env, s.target, payload);
                narrowedPaths = [...narrowedPaths, { path: { rootVar: s.target, fields: [] }, narrowedTy: payload, variant: typed.value.fn.name }];
              } else {
                env = refine(env, s.target, storage);
              }
            } else {
              env = refine(env, s.target, storage);
            }
          } else {
            const udecl = declOfKind(ctx.typeDecls, tyBaseName(storage.name), "discriminated-union");
            if (udecl?.discriminant && typed.kind === "assign" && typed.value.kind === "record") {
              let nextVariant: string | undefined;
              const tagF = typed.value.fields.find(f => f.name === udecl.discriminant);
              if (tagF?.value.kind === "str" || tagF?.value.kind === "bool") {
                nextVariant = String(tagF.value.value);
              } else if (typed.value.spread && typed.value.ofVariant && !tagF) {
                nextVariant = typed.value.ofVariant;
              }
              if (nextVariant) {
                narrowedPaths = [...narrowedPaths, { path: { rootVar: s.target, fields: [] }, narrowedTy: storage, variant: nextVariant }];
              }
            }
          }
        }
      }
    }
    // Control-flow invalidation: if an `if`/`while`/`forof`/`switch` may assign
    // a narrowed variable or path, restore its declared storage type before
    // subsequent statements (definite-assignment guards re-narrow below).
    if (s.kind === "if" || s.kind === "while" || s.kind === "forof" || s.kind === "switch") {
      const { wholeRoots, dottedTargets } = collectAssignedTargetsRaw([s]);
      const inv = invalidateNarrowings(env, narrowedPaths, wholeRoots, dottedTargets, ctx.typeDecls);
      env = inv.env;
      narrowedPaths = inv.narrowedPaths;
    }
    // Definite-assignment guard (#340): `if (v === undefined) { v = nonOpt; }`
    // guarantees `v` is present after the `if` on both branches.
    if (s.kind === "if" && typed.kind === "if" && s.else.length === 0) {
      const neg = negatedVarPresence(typed.cond);
      if (neg && definitelyAssignsNonOptional(s.then, neg.varName, currentCtx)) {
        env = refine(env, neg.varName, neg.innerTy);
      }
    }
    // Flow narrowing: if (x === undefined) { return } narrows x for rest of block.
    // Also handles compound: if (x === undefined || y === undefined) { return }
    // Any terminator counts (return/throw/break/continue — same set as narrow's
    // isTerminating): each exits the current block, so the rest of the block
    // only runs when the guard was false.
    // Field chains are excluded — resolve can't substitute in statement lists;
    // transform's emitOptionalMatch handles field chains in statement contexts.
    if (s.kind === "if" && s.then.length > 0 && isTerminatorKind(s.then[s.then.length - 1].kind) && s.else.length === 0) {
      if (typed.kind === "if") {
        for (const n of collectEarlyReturnNarrowings(typed.cond)) {
          env = refine(env, n.varName, n.innerTy);
        }
        for (const np of collectEarlyReturnPathNarrowings(typed.cond, currentCtx)) {
          if (np.path.fields.length === 0) {
            env = refine(env, np.path.rootVar, np.narrowedTy);
          } else {
            narrowedPaths = [...narrowedPaths, np];
          }
        }
        const nv = discriminantVariantWhen(typed.cond, false, currentCtx);
        if (nv) narrowedPaths = [...narrowedPaths, nv];
        const nsv = synthVariantWhen(typed.cond, false, currentCtx);
        if (nsv) {
          const updated = applyVariantNarrowing({ ...currentCtx, env, narrowedPaths }, nsv.path, nsv.unionTy, nsv.variant);
          env = updated.env;
          narrowedPaths = updated.narrowedPaths;
        }
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
      // type into the array literal (see the arrayLiteral case). Optionals too
      // (`const r: TExpr | null = cond ? {…} : null`) — the record case unwraps
      // one optional level when consulting returnTy.
      const initCtx = (declTy.kind === "user" || declTy.kind === "array" || declTy.kind === "optional" || declTy.kind === "nullish")
        ? { ...ctx, returnTy: declTy } : ctx;
      let init = coerceStr(resolveExpr(s.init, initCtx), declTy, ctx.typeDecls);
      // Under noUncheckedIndexedAccess, TS gives `const e = arr[i]` type T | undefined
      // while the index expression itself resolves to T. Leave that mismatch intact:
      // narrow.ts's ruleOptionalIndexBinding adds the runtime bounds guard and the
      // corresponding Some/None branches. Wrapping here would turn it into an
      // unconditional Some(arr[i]) and prevent that JS-semantics rewrite from firing.
      const deferOptionalIndex = declTy.kind === "optional" && init.kind === "index" &&
        init.obj.ty.kind === "array" && init.ty.kind !== "optional";
      if (!deferOptionalIndex) init = coerceToTargetTy(init, declTy, ctx.typeDecls);
      let ty: Ty;
      if (isUnmodeledTy(declTy, ctx.typeDecls) && !isUnmodeledTy(init.ty, ctx.typeDecls)) {
        // ts-morph's declared type is opaque to us (an expanded union it made
        // by inlining an alias we shadow via declare-type, or any-laden), but
        // LS resolved the initializer to something concrete. Take the structure
        // from `init.ty`, keeping only the optionality ts-morph reported.
        ty = declTy.kind === "nullish" && init.ty.kind !== "nullish"
          ? { kind: "nullish", inner: init.ty.kind === "optional" ? init.ty.inner : init.ty }
          : declTy.kind === "optional" && init.ty.kind !== "optional"
            ? { ...declTy, inner: init.ty }
            : init.ty;
      } else if (isWidenedStringUnionTy(declTy, init.ty, ctx.typeDecls) && !ctx.overrides.has(s.name)) {
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
        ty = (declTy.kind !== "optional" && declTy.kind !== "nullish" && init.ty.kind === "optional") ? init.ty : declTy;
      }
      // const collections are mutable in value-semantics world (TS mutates in place, Dafny/Lean reassign)
      const mutable = s.mutable || isRefMutableInTS(ty);
      return [{ kind: "let", name: s.name, ty, mutable, init }, extend(ctx.env, s.name, ty)];
    }

    case "assign": {
      const entry = binding(ctx.env, s.target);
      if (entry?.argumentPack || entry?.value) {
        throw new Error(`assignment to callback binding '${s.target}' requires materializing its argument value`);
      }
      entry?.onRead?.();
      // For dotted writes (`sh.value = ...`, `b.sh.value = ...`), record any
      // narrowed union variant at each step along the owner chain so
      // transform/emit use the right collision-renamed destructors and Lean
      // inductive match-updates at arbitrary nesting depth.
      let ofVariant: string | undefined;
      let ownerVariants: (string | undefined)[] | undefined;
      let targetTy: Ty = storageLookup(ctx.env, s.target) ?? { kind: "unknown" as const };
      if (s.target.includes(".") && !s.target.startsWith("this.")) {
        const parts = s.target.split(".");
        const root = parts[0]!;
        const fields = parts.slice(1);
        const variants: (string | undefined)[] = [];
        let curTy: Ty | undefined = storageLookup(ctx.env, root);
        for (let i = 0; i < fields.length; i++) {
          const v = lookupNarrowedVariant({ rootVar: root, fields: fields.slice(0, i) }, ctx);
          variants.push(v);
          if (curTy) {
            const unwrapped = (curTy.kind === "optional" || curTy.kind === "nullish") ? curTy.inner : curTy;
            if (unwrapped.kind === "user") {
              const decl = findDecl(ctx, tyBaseName(unwrapped.name));
              if (decl?.kind === "discriminated-union" && decl.variants) {
                const variant = (v ? decl.variants.find(vi => vi.name === v) : undefined)
                  ?? decl.variants.find(vi => vi.fields.some(f => f.name === fields[i]));
                curTy = variant?.fields.find(f => f.name === fields[i])?.type;
              } else if (decl?.kind === "record" && decl.fields) {
                curTy = decl.fields.find(f => f.name === fields[i])?.type;
              } else {
                curTy = undefined;
              }
            } else {
              curTy = undefined;
            }
          }
        }
        ofVariant = variants[0];
        if (variants.some(v => v !== undefined)) ownerVariants = variants;
        if (curTy) targetTy = curTy;
      }
      // Coerce RHS against the variable's declared storage type (not a narrowed
      // flow type) so reassignments like `v = 7` or `v = undefined` stay typed
      // as `Option<T>`.
      // Propagate the target's type as returnTy, mirroring the annotated-let
      // case, so record/union literals and array literals in the RHS resolve
      // to their named datatypes.
      const valueCtx = (targetTy.kind === "user" || targetTy.kind === "array" || targetTy.kind === "optional" || targetTy.kind === "nullish")
        ? { ...ctx, returnTy: targetTy } : ctx;
      const value = coerceToTargetTy(resolveExpr(s.value, valueCtx), targetTy, ctx.typeDecls);
      return [{ kind: "assign", target: entry?.emittedName ?? s.target, value, ...(ofVariant ? { ofVariant } : {}), ...(ownerVariants ? { ownerVariants } : {}) }, ctx.env];
    }

    case "return": {
      const value = coerceToTargetTy(resolveExpr(s.value, ctx), ctx.returnTy, ctx.typeDecls);
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
      const resolvedCond = resolveExpr(s.cond, ctx);
      let thenCtx = collectAndChainNarrowings(resolvedCond, ctx);
      let elseCtx = ctx;
      const single = negatedVarPresence(resolvedCond);
      if (single) {
        elseCtx = withEnv(ctx, refine(ctx.env, single.varName, single.innerTy));
      } else if (resolvedCond.kind === "binop" && resolvedCond.op === "||") {
        for (const n of collectEarlyReturnNarrowings(resolvedCond)) {
          elseCtx = withEnv(elseCtx, refine(elseCtx.env, n.varName, n.innerTy));
        }
      }
      const negPaths = collectEarlyReturnPathNarrowings(resolvedCond, ctx);
      if (negPaths.length > 0) {
        elseCtx = { ...elseCtx, narrowedPaths: [...elseCtx.narrowedPaths, ...negPaths] };
      }
      const elseVariant = discriminantVariantWhen(resolvedCond, false, ctx);
      if (elseVariant) {
        elseCtx = { ...elseCtx, narrowedPaths: [...elseCtx.narrowedPaths, elseVariant] };
      }
      const elseSynth = synthVariantWhen(resolvedCond, false, ctx);
      if (elseSynth) {
        elseCtx = applyVariantNarrowing(elseCtx, elseSynth.path, elseSynth.unionTy, elseSynth.variant);
      }
      // Narrow map index access across `k in m` / `!(k in m)` in the cond:
      // positive atoms (from `k in m` or &&-chains containing it) → then-branch;
      // negated atoms (from `!(k in m)`) → else-branch.
      thenCtx = withInAtoms(thenCtx, extractInAtoms(resolvedCond));
      elseCtx = withInAtoms(elseCtx, extractInAtomsNegated(resolvedCond));
      return [{ kind: "if", cond: resolvedCond, then: resolveBlock(s.then, thenCtx), else: resolveBlock(s.else, elseCtx) }, ctx.env];
    }

    case "while": {
      // Any variable or path mutated inside the loop body cannot keep a pre-loop
      // narrowing across iterations (including inside the loop condition and
      // invariants on back-edges).
      const { wholeRoots, dottedTargets } = collectAssignedTargetsRaw(s.body);
      const loopInv = invalidateNarrowings(ctx.env, ctx.narrowedPaths, wholeRoots, dottedTargets, ctx.typeDecls);
      const loopCtx: Ctx = { ...ctx, env: loopInv.env, narrowedPaths: loopInv.narrowedPaths };
      const whileSpecCtx = { ...loopCtx, inSpec: true };
      const resolvedInvariants = resolveSpecs(s.invariants, whileSpecCtx);
      const resolvedCond = resolveExpr(s.cond, loopCtx);
      // Invariants and presence checks in the `while` condition (#339) both hold
      // at the top of the loop body.
      const bodyCtx = collectAndChainNarrowings(
        resolvedCond,
        withInAtoms(loopCtx, resolvedInvariants.flatMap(extractInAtoms)),
      );
      return [{
        kind: "while",
        cond: resolvedCond,
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
      // The loop counter is minted here, once, and recorded on the loop so
      // transform emits the same name a spec here refers to. The first loop
      // over a head name in a function gets `_x_idx`, later ones `_x_idx2`, ….
      const count = ctx.forofCounts.get(s.names[0]) ?? 0;
      ctx.forofCounts.set(s.names[0], count + 1);
      const idxName = freshName(`_${s.names[0]}_idx${count === 0 ? "" : count + 1}`);
      const { wholeRoots, dottedTargets } = collectAssignedTargetsRaw(s.body);
      const loopInv = invalidateNarrowings(ctx.env, ctx.narrowedPaths, wholeRoots, dottedTargets, ctx.typeDecls);
      env = loopInv.env;
      env = extend(env, idxName, { kind: "nat" });
      for (let j = 0; j < s.names.length; j++) {
        env = extend(env, s.names[j], nameTypes[j] ?? { kind: "unknown" });
      }
      const bodyCtx: Ctx = { ...ctx, env, narrowedPaths: loopInv.narrowedPaths };
      return [{
        kind: "forof", names: s.names, nameTypes, iterable, idx: idxName,
        invariants: resolveSpecs(s.invariants, { ...bodyCtx, inSpec: true }),
        doneWith: s.doneWith ? resolveSpec(s.doneWith, { ...bodyCtx, inSpec: true }) : null,
        body: resolveBlock(s.body, bodyCtx),
      }, ctx.env];
    }

    case "throw":
      return [{ kind: "throw" }, ctx.env];

    case "switch": {
      const expr = resolveExpr(s.expr, ctx);
      const decl = expr.ty.kind === "user" ? findDecl(ctx, tyBaseName(expr.ty.name)) : undefined;
      const path = decl?.kind === "discriminated-union" && decl.discriminant === s.discriminant
        ? asTExprAccessPath(expr) : null;
      const withVariant = (variant: string | undefined): Ctx =>
        path && variant ? { ...ctx, narrowedPaths: [
          ...ctx.narrowedPaths, { path, narrowedTy: expr.ty, variant },
        ] } : ctx;
      const cases = s.cases.map(c => ({ label: c.label, body: resolveBlock(c.body, withVariant(c.label)) }));
      const defaultVariant = path && decl ? remainingVariant(decl, s.cases.map(c => c.label))?.name : undefined;
      return [{ kind: "switch", expr, discriminant: s.discriminant, cases,
        defaultBody: resolveBlock(s.defaultBody, withVariant(defaultVariant)) }, ctx.env];
    }

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

/** Whether a raw statement or expression tree contains a havoc anywhere. */
function containsHavoc(v: unknown): boolean {
  if (Array.isArray(v)) return v.some(containsHavoc);
  if (v === null || typeof v !== "object") return false;
  if ((v as { kind?: string }).kind === "havoc") return true;
  return Object.values(v).some(containsHavoc);
}

/** Syntactic purity: no while, no for-of, no mutable let, no havoc. */
function isSyntacticallyPure(stmts: RawStmt[]): boolean {
  for (const s of stmts) {
    // Havoc lowers to Dafny's `*`, which is only valid in a method.
    if (containsHavoc(s)) return false;
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
    case "recordMerge":
      collectCallsExpr(e.base, fns, out);
      collectCallsExpr(e.override, fns, out);
      return;
    case "arrayLiteral": for (const el of e.elems) collectCallsExpr(el, fns, out); return;
    case "lambda":
      for (const p of e.params) if (p.defaultValue) collectCallsExpr(p.defaultValue, fns, out);
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

/** Dotted/bare spelling of a raw call target, when statically named. */
function rawCalleeName(e: RawExpr): string | null {
  if (e.kind === "var") return e.name;
  if (e.kind === "field") {
    const obj = rawCalleeName(e.obj);
    return obj ? `${obj}.${e.field}` : null;
  }
  return null;
}

/** Whether a raw function body invokes any extern resolved as impure. */
function containsImpureExternCall(v: unknown, names: Set<string>): boolean {
  if (Array.isArray(v)) return v.some(x => containsImpureExternCall(x, names));
  if (v === null || typeof v !== "object") return false;
  const node = v as { kind?: string; fn?: RawExpr };
  if (node.kind === "call" && node.fn) {
    const callee = rawCalleeName(node.fn);
    if (callee && names.has(callee)) return true;
  }
  return Object.values(v).some(x => containsImpureExternCall(x, names));
}

function computePureFns(functions: RawFunction[], externDecls: import("./rawir.js").RawExtern[]): Set<string> {
  const allFnNames = new Set(functions.map(fn => fn.name));
  const impureExternNames = new Set(
    externDecls.filter(ext => ext.impure).flatMap(ext => [ext.qualified, ext.flat]),
  );
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
    functions.filter(fn => !forcePure.has(fn.name) &&
      (!isSyntacticallyPure(fn.body) || containsImpureExternCall(fn.body, impureExternNames)))
      .map(fn => fn.name)
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

// ── Resolve function / module ────────────────────────────────

function resolveFunction(
  fn: RawFunction, typeDecls: TypeDeclInfo[], pureFns: Set<string>,
  fnParams: Map<string, Ty[]> = new Map(), fnReturns: Map<string, Ty> = new Map(),
  externs: Map<string, ExternSignature> = new Map(),
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

  const baseCtx: Ctx = { env, typeDecls, typeParams: new Set(fn.typeParams), overrides, allowResult: false, returnTy, pureFns, fnParams, fnReturns, externs, inSpec: false, inLambda: false, narrowedPaths: [], narrowedIndices: [], forofCounts: new Map() };
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
  const resolvedRequires = resolveSpecs(fn.requires, requiresCtx, true);
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

function resolveClass(cls: import("./rawir.js").RawClass, typeDecls: TypeDeclInfo[], pureFns: Set<string>, fnParams: Map<string, Ty[]> = new Map(), fnReturns: Map<string, Ty> = new Map(), externs: Map<string, ExternSignature> = new Map(), moduleConstants: Map<string, Ty> = new Map()): import("./typedir.js").TClass {
  const fields = cls.fields.map(f => ({ name: f.name, ty: expandAlias(parseTsType(f.tsType), typeDecls) }));
  // Create a synthetic record type for 'this' so field access resolves
  const thisType: Ty = { kind: "user", name: cls.name };
  const thisDecl: TypeDeclInfo = { name: cls.name, kind: "record", fields: cls.fields.map((f, i) => ({ name: f.name, tsType: f.tsType, type: fields[i].ty })) };
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
  callbackCounter = 0;
  mergeBinder = 0;
  _warnedRefEq.clear();
  precomputeFieldTypes(raw.typeDecls);
  const pureFns = computePureFns(raw.functions, raw.externs ?? []);
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
  const externs = new Map<string, ExternSignature>();
  // First pass: register signatures so spec resolution (below) can reference
  // them — including the extern referring to itself, or specs that mention
  // sibling externs.
  for (const ext of raw.externs ?? []) {
    const params = ext.params.map(p => parseTsType(p.tsType));
    const returnTy = parseTsType(ext.returnType);
    externs.set(ext.qualified, { flat: ext.flat, params, returnTy, impure: ext.impure });
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
    const baseCtx: Ctx = { env, typeDecls: raw.typeDecls, typeParams: new Set(ext.typeParams), overrides: new Map(), allowResult: false, returnTy: sig.returnTy, pureFns, fnParams, fnReturns, externs, inSpec: true, inLambda: false, narrowedPaths: [], narrowedIndices: [], forofCounts: new Map() };
    const ensuresCtx: Ctx = { ...baseCtx, env: extend(env, "\\result", sig.returnTy), allowResult: true };
    const resolveClauses = (kind: "requires" | "ensures", ctx: Ctx) => ext[kind].map(s => {
      try {
        return resolveSpec(s, ctx);
      } catch (e) {
        const reason = e instanceof Error ? e.message : String(e);
        throw new Error(`extern ${ext.qualified}: //@ ${kind} ${s}: ${reason}`);
      }
    });
    return {
      qualified: ext.qualified,
      flat: ext.flat,
      typeParams: ext.typeParams,
      params: ext.params.map((p, i) => ({ name: p.name, ty: sig.params[i] })),
      returnTy: sig.returnTy,
      requires: resolveClauses("requires", baseCtx),
      ensures: resolveClauses("ensures", ensuresCtx),
      impure: ext.impure,
    };
  });
  const emptyCtx: Ctx = { env: null, typeDecls: raw.typeDecls, typeParams: new Set(), overrides: new Map(), allowResult: false, returnTy: { kind: "int" }, pureFns, fnParams, fnReturns, externs, inSpec: false, inLambda: false, narrowedPaths: [], narrowedIndices: [], forofCounts: new Map() };
  const constants = (raw.constants ?? []).map(c => {
    const declaredTy = expandAlias(parseTsType(c.tsType), raw.typeDecls);
    // Propagate the declared type into the value's resolution context so that
    // record literals on map-typed constants (e.g. `Record<string, number>`)
    // get their `ty` set to `map<...>` rather than `user("...")`.
    const valueCtx: Ctx = { ...emptyCtx, returnTy: declaredTy };
    const value = resolveExpr(c.value, valueCtx);
    // TypeScript's number defaults to int, but fractional initializers need real.
    const ty = declaredTy.kind === "int" && value.ty.kind === "real" ? value.ty : declaredTy;
    return { name: c.name, ty, value: coerceToTargetTy(value, ty, raw.typeDecls) };
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
