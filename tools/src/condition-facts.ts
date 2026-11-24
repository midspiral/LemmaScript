/** Union condition facts and helpers for single-evaluation optional expressions. */

import type { TExpr, Ty } from "./typedir.js";
import { freshName } from "./names.js";
import type { TypeDecls } from "./typedecls.js";
import { unionDeclOfTy } from "./typedecls.js";

export interface CondCtx {
  decls: TypeDecls;
  oc: { n: number };
}

export function freshOcBinder(ctx: CondCtx): string {
  return freshName(`_oc${ctx.oc.n++}_val`);
}

/** Payloads with JavaScript falsy values, in addition to absence. */
export const isFalsyCapableTy = (ty: Ty): boolean =>
  ["int", "nat", "real", "string", "bool"].includes(ty.kind);

/** Pull one `parse`-matching conjunct out of an `&&` tree, returning it plus
 *  the tree with that conjunct removed:
 *  `(x !== undefined && b) && c` → { check, restCond: b && c }.
 *
 *  Search matching conjuncts in source order. A later check may read a field
 *  whose root an earlier check unwraps, so the left subtree must be searched
 *  before the right operand. Keep the remaining conjuncts in their original
 *  relative order. */
export function extractConjunct<C>(cond: TExpr, parse: (e: TExpr) => C | null): { check: C; restCond: TExpr } | null {
  if (cond.kind !== "binop" || cond.op !== "&&") return null;
  const left = parse(cond.left);
  if (left) return { check: left, restCond: cond.right };
  if (cond.left.kind === "binop" && cond.left.op === "&&") {
    const inner = extractConjunct(cond.left, parse);
    if (inner) return { check: inner.check, restCond: { ...cond, left: inner.restCond } as TExpr };
  }
  const right = parse(cond.right);
  if (right) return { check: right, restCond: cond.left };
  if (cond.right.kind === "binop" && cond.right.op === "&&") {
    const inner = extractConjunct(cond.right, parse);
    if (inner) return { check: inner.check, restCond: { ...cond, right: inner.restCond } as TExpr };
  }
  return null;
}

type OptChain = Extract<TExpr, { kind: "optChain" }>;

/** Apply an optional chain's steps (field / index / call) to a base expr. */
export function applyChain(body: TExpr, chain: OptChain["chain"]): TExpr {
  for (const step of chain) {
    if (step.kind === "field") body = { kind: "field", obj: body, field: step.name, ty: step.ty,
      ...(step.isDiscriminant ? { isDiscriminant: true } : {}) };
    else if (step.kind === "index") body = { kind: "index", obj: body, idx: step.idx, ty: step.ty };
    else body = { kind: "call", fn: body, args: step.args, ty: step.ty, callKind: step.callKind,
      ...(step.builtinId ? { builtinId: step.builtinId } : {}) };
  }
  return body;
}

export function arrayBoundsCond(arr: TExpr, idx: TExpr): TExpr {
  const len: TExpr = { kind: "field", obj: arr, field: "length", ty: { kind: "int" } };
  const lo: TExpr = { kind: "binop", op: "<=", left: { kind: "num", value: 0, ty: { kind: "int" } }, right: idx, ty: { kind: "bool" } };
  const hi: TExpr = { kind: "binop", op: "<", left: idx, right: len, ty: { kind: "bool" } };
  return { kind: "binop", op: "&&", left: lo, right: hi, ty: { kind: "bool" } };
}

export interface VariantFact {
  scrutinee: TExpr & { kind: "var" };
  typeName: string;
  variant: string;
}

export interface IsArrayFact {
  scrutinee: TExpr;
  typeName: string;
  variant: "ArrayBranch" | "NonArrayBranch";
}

/** A "narrowable path" is a var or a chain of field accesses rooted at a var
 *  — i.e., pure and structurally addressable, so transforms can substitute
 *  occurrences inside a matched arm without worrying about re-evaluation. */
export function isNarrowablePath(e: TExpr): boolean {
  if (e.kind === "var") return true;
  if (e.kind === "coerce") return isNarrowablePath(e.expr);
  if (e.kind === "field") return isNarrowablePath(e.obj);
  return false;
}

/** Detect `Array.isArray(<path>)` where `<path>` is a narrowable path whose
 *  type is a synthesized array-union (discriminant `"__isArray__"`). */
export function isArrayFact(call: TExpr, ctx: CondCtx): (IsArrayFact & { variant: "ArrayBranch" }) | null {
  if (call.kind !== "call") return null;
  if (call.fn.kind !== "field" || call.fn.field !== "isArray") return null;
  if (call.fn.obj.kind !== "var" || call.fn.obj.name !== "Array") return null;
  if (call.args.length !== 1) return null;
  const arg = call.args[0];
  if (!isNarrowablePath(arg) || arg.ty.kind !== "user") return null;
  const decl = unionDeclOfTy(ctx.decls, arg.ty);
  if (decl?.discriminant !== "__isArray__") return null;
  return { scrutinee: arg, typeName: arg.ty.name, variant: "ArrayBranch" };
}

/** Detect `typeof <path> === "string"` where `<path>`'s type is a synth array-
 *  union (`U | T[]`) AND its `NonArrayBranch` payload `U` is itself `string`.
 *  The runtime `=== "string"` test matches that branch only when `U` is string —
 *  for any other non-array payload (`number | T[]`, …) it never holds, so we must
 *  NOT narrow. Returns the `NonArrayBranch` variant; the dual of `Array.isArray`. */
export function typeofStringFact(e: TExpr, ctx: CondCtx): (IsArrayFact & { variant: "NonArrayBranch" }) | null {
  if (e.kind !== "binop" || e.op !== "===") return null;
  const tof = e.left.kind === "unop" && e.left.op === "typeof" ? e.left.expr
    : e.right.kind === "unop" && e.right.op === "typeof" ? e.right.expr : null;
  const lit = e.left.kind === "str" ? e.left.value : e.right.kind === "str" ? e.right.value : null;
  if (!tof || lit !== "string") return null;
  if (!isNarrowablePath(tof) || tof.ty.kind !== "user") return null;
  const decl = unionDeclOfTy(ctx.decls, tof.ty);
  if (decl?.discriminant !== "__isArray__") return null;
  const valTy = decl.variants?.find(v => v.name === "NonArrayBranch")?.fields.find(f => f.name === "val")?.type;
  if (valTy?.kind !== "string") return null;   // guard: the non-array branch must actually be `string`
  return { scrutinee: tof, typeName: tof.ty.name, variant: "NonArrayBranch" };
}

/** Leading `Array.isArray(path)` fact of an `&&` chain (positive form only — a
 *  negated `!Array.isArray(...)` would narrow to the wrong variant for then-body
 *  consumers, so those are left to the untouched-conditional path). */
export function leadingIsArray(cond: TExpr, ctx: CondCtx) {
  return extractConjunct(cond, e => isArrayFact(e, ctx));
}

/** Detect `x.kind === "variant"`, `'key' in x`, or `Array.isArray(x)` (synth
 *  array-union) as a positive discriminant check on a bare-var scrutinee. */
export function variantFact(cond: TExpr, ctx: CondCtx): VariantFact | null {
  // Pattern: x.discriminant === "variant"
  if (cond.kind === "binop" && cond.op === "===" && cond.right.kind === "str" &&
      cond.left.kind === "field" && cond.left.isDiscriminant &&
      cond.left.obj.kind === "var" && cond.left.obj.ty.kind === "user") {
    return { scrutinee: cond.left.obj, typeName: cond.left.obj.ty.name, variant: cond.right.value };
  }
  // Pattern: 'key' in x — narrows x to the unique variant containing `key`.
  if (cond.kind === "binop" && cond.op === "in" &&
      cond.left.kind === "str" && cond.right.kind === "var" &&
      cond.right.ty.kind === "user") {
    const key = cond.left.value;
    const typeName = cond.right.ty.name;
    const decl = unionDeclOfTy(ctx.decls, cond.right.ty);
    if (decl?.variants) {
      const matches = decl.variants.filter(v => v.fields.some(f => f.name === key));
      if (matches.length === 1) {
        return { scrutinee: cond.right, typeName, variant: matches[0].name };
      }
    }
  }
  // Pattern: Array.isArray(x) — narrows x to the ArrayBranch variant of a
  // synthesized array-union (discriminant "__isArray__"). Statement-level
  // discriminant chains (`if (Array.isArray(x)) {...} else if (...)`) still
  // require a bare-var scrutinee since the existing var-name-keyed
  // replacement machinery in transform.ts only handles that shape; path
  // scrutinees (e.g. `m.content`) are handled exclusively by the
  // conditional/expression tagMatch drivers.
  const arrCheck = isArrayFact(cond, ctx);
  if (arrCheck && arrCheck.scrutinee.kind === "var") {
    return { scrutinee: arrCheck.scrutinee, typeName: arrCheck.typeName, variant: arrCheck.variant };
  }
  return null;
}

/** Detect `x.kind !== "variant"` (negative discriminant check) or
 *  `!Array.isArray(x)` (synth array-union, narrows to NonArrayBranch). */
export function negVariantFact(cond: TExpr, ctx: CondCtx): VariantFact | null {
  if (cond.kind === "binop" && cond.op === "!==" && cond.right.kind === "str" &&
      cond.left.kind === "field" && cond.left.isDiscriminant &&
      cond.left.obj.kind === "var" && cond.left.obj.ty.kind === "user") {
    return { scrutinee: cond.left.obj, typeName: cond.left.obj.ty.name, variant: cond.right.value };
  }
  // Pattern: !Array.isArray(x) — narrows x to the NonArrayBranch variant.
  // Same var-scrutinee restriction as variantFact.
  if (cond.kind === "unop" && cond.op === "!") {
    const arrCheck = isArrayFact(cond.expr, ctx);
    if (arrCheck && arrCheck.scrutinee.kind === "var") {
      return { scrutinee: arrCheck.scrutinee, typeName: arrCheck.typeName, variant: "NonArrayBranch" };
    }
  }
  return null;
}
