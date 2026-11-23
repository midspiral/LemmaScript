/**
 * condition-facts — shared condition detection for spec narrowing,
 * `.filter()` recognition, array bounds, and variant narrowing.
 *
 * Optional/nullish and variant narrowing no longer rewrite control flow into
 * `someMatch`/`tagMatch`; they use checked local coercions and projections
 * instead. This module keeps the small pure fact detectors used by `resolve.ts`
 * (specs / non-TS frontends), `narrow.ts` (array bounds), and `transform.ts`
 * (`.filter` narrowing).
 */

import type { TExpr, Ty, Nullish } from "./typedir.js";
import { excludeNullish, includesNullish } from "./nullish.js";
import type { TypeDecls } from "./typedecls.js";
import { unionDeclOfTy } from "./typedecls.js";

export interface CondCtx {
  decls: TypeDecls;
}

// ── Presence facts (for specs & .filter() detection) ────────

export interface PresentFact {
  scrutinee: TExpr;
  innerTy: Ty;
  negated: boolean;
  truthiness: boolean;
  excluded: Nullish;
}

/** Detect optional/nullish presence checks: `e !== undefined`, `e === undefined`,
 *  `e != null`, `e == null`, `!c`, or bare optional `e` on a pure access path. */
export function presentFact(cond: TExpr): PresentFact | null {
  if (cond.kind === "unop" && cond.op === "!") {
    const inner = presentFact(cond.expr);
    if (inner) return { ...inner, negated: !inner.negated };
    return null;
  }
  if (cond.kind !== "binop" || !["!==", "===", "!=", "=="].includes(cond.op)) {
    if (cond.ty.kind === "optional" && isNarrowablePath(cond)) {
      return {
        scrutinee: cond,
        innerTy: cond.ty.inner,
        negated: false,
        truthiness: true,
        excluded: "both",
      };
    }
    return null;
  }
  let e: TExpr | null = null;
  let excluded: Nullish = "undefined";
  if (cond.right.kind === "var" && (cond.right.name === "undefined" || cond.right.name === "null")) {
    e = cond.left;
    excluded = cond.right.name;
  } else if (cond.left.kind === "var" && (cond.left.name === "undefined" || cond.left.name === "null")) {
    e = cond.right;
    excluded = cond.left.name;
  }
  if (!e || e.ty.kind !== "optional" || !isNarrowablePath(e)) return null;
  if (cond.op === "==" || cond.op === "!=") excluded = "both";
  if (excluded !== "both" && !includesNullish(e.ty.nullish, excluded)) return null;
  return {
    scrutinee: e,
    innerTy: excludeNullish(e.ty, excluded),
    negated: cond.op === "===" || cond.op === "==",
    truthiness: false,
    excluded,
  };
}

/** Which primitive types have falsy values in JS (`0`, `""`, `false`). */
export const isFalsyCapableTy = (ty: Ty): boolean =>
  ["int", "nat", "real", "string", "bool"].includes(ty.kind);

// ── Conjunct extraction ─────────────────────────────────────

export function extractConjunct<C>(
  cond: TExpr,
  parse: (e: TExpr) => C | null,
): { check: C; restCond: TExpr } | null {
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

// ── Optional chains ─────────────────────────────────────────

type OptChain = Extract<TExpr, { kind: "optChain" }>;

/** Apply an optional chain's steps (field / index / call) to a base expr. */
export function applyChain(body: TExpr, chain: OptChain["chain"]): TExpr {
  for (const step of chain) {
    if (step.kind === "field") body = { kind: "field", obj: body, field: step.name, ty: step.ty };
    else if (step.kind === "index") body = { kind: "index", obj: body, idx: step.idx, ty: step.ty };
    else body = { kind: "call", fn: body, args: step.args, ty: step.ty, callKind: step.callKind,
      ...(step.builtinId ? { builtinId: step.builtinId } : {}) };
  }
  return body;
}

// ── In-bounds facts ─────────────────────────────────────────

/** `0 <= idx && idx < arr.length` — the in-bounds guard for an array index. */
export function arrayBoundsCond(arr: TExpr, idx: TExpr): TExpr {
  const len: TExpr = { kind: "field", obj: arr, field: "length", ty: { kind: "int" } };
  const lo: TExpr = { kind: "binop", op: "<=", left: { kind: "num", value: 0, ty: { kind: "int" } }, right: idx, ty: { kind: "bool" } };
  const hi: TExpr = { kind: "binop", op: "<", left: idx, right: len, ty: { kind: "bool" } };
  return { kind: "binop", op: "&&", left: lo, right: hi, ty: { kind: "bool" } };
}

// ── Access paths & Variant facts ────────────────────────────

export function isNarrowablePath(e: TExpr): boolean {
  if (e.kind === "coerce") return isNarrowablePath(e.expr);
  if (e.kind === "var") return true;
  if (e.kind === "field") return isNarrowablePath(e.obj);
  return false;
}

export interface VariantFact {
  scrutinee: TExpr;
  typeName: string;
  variant: string;
}

export interface IsArrayFact {
  scrutinee: TExpr;
  typeName: string;
  variant: "ArrayBranch" | "NonArrayBranch";
}

export function isArrayFact(call: TExpr, ctx: CondCtx): (IsArrayFact & { variant: "ArrayBranch" }) | null {
  if (call.kind !== "call") return null;
  if (call.fn.kind !== "field" || call.fn.field !== "isArray") return null;
  if (call.fn.obj.kind !== "var" || call.fn.obj.name !== "Array") return null;
  if (call.args.length !== 1) return null;
  const rawArg = call.args[0];
  const arg = rawArg.kind === "coerce" && rawArg.variant ? rawArg.expr : rawArg;
  if (!isNarrowablePath(arg) || arg.ty.kind !== "user") return null;
  const decl = unionDeclOfTy(ctx.decls, arg.ty);
  if (decl?.discriminant !== "__isArray__") return null;
  return { scrutinee: arg, typeName: arg.ty.name, variant: "ArrayBranch" };
}

export function typeofStringFact(e: TExpr, ctx: CondCtx): (IsArrayFact & { variant: "NonArrayBranch" }) | null {
  if (e.kind !== "binop" || (e.op !== "===" && e.op !== "==")) return null;
  const rawTof = e.left.kind === "unop" && e.left.op === "typeof" ? e.left.expr
    : e.right.kind === "unop" && e.right.op === "typeof" ? e.right.expr : null;
  const lit = e.left.kind === "str" ? e.left.value : e.right.kind === "str" ? e.right.value : null;
  if (!rawTof || lit !== "string") return null;
  const tof = rawTof.kind === "coerce" && rawTof.variant ? rawTof.expr : rawTof;
  if (!isNarrowablePath(tof) || tof.ty.kind !== "user") return null;
  const decl = unionDeclOfTy(ctx.decls, tof.ty);
  if (decl?.discriminant !== "__isArray__") return null;
  const valTy = decl.variants?.find(v => v.name === "NonArrayBranch")?.fields.find(f => f.name === "val")?.type;
  if (valTy?.kind !== "string") return null;
  return { scrutinee: tof, typeName: tof.ty.name, variant: "NonArrayBranch" };
}

export function variantFact(cond: TExpr, ctx: CondCtx): VariantFact | null {
  if (cond.kind === "binop" && (cond.op === "===" || cond.op === "==") && cond.right.kind === "str" &&
      cond.left.kind === "field" && cond.left.isDiscriminant &&
      isNarrowablePath(cond.left.obj) && cond.left.obj.ty.kind === "user") {
    return { scrutinee: cond.left.obj, typeName: cond.left.obj.ty.name, variant: cond.right.value };
  }
  if (cond.kind === "field" && cond.isDiscriminant && isNarrowablePath(cond.obj) && cond.obj.ty.kind === "user") {
    const decl = unionDeclOfTy(ctx.decls, cond.obj.ty);
    if (decl?.variants?.some(v => v.name === "true")) {
      return { scrutinee: cond.obj, typeName: cond.obj.ty.name, variant: "true" };
    }
  }
  if (cond.kind === "binop" && cond.op === "in" &&
      cond.left.kind === "str" && isNarrowablePath(cond.right) &&
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
  const arrCheck = isArrayFact(cond, ctx);
  if (arrCheck) return arrCheck;
  const tofCheck = typeofStringFact(cond, ctx);
  if (tofCheck) return tofCheck;
  return null;
}

export function negVariantFact(cond: TExpr, ctx: CondCtx): VariantFact | null {
  if (cond.kind === "binop" && (cond.op === "!==" || cond.op === "!=") && cond.right.kind === "str" &&
      cond.left.kind === "field" && cond.left.isDiscriminant &&
      isNarrowablePath(cond.left.obj) && cond.left.obj.ty.kind === "user") {
    return { scrutinee: cond.left.obj, typeName: cond.left.obj.ty.name, variant: cond.right.value };
  }
  if (cond.kind === "unop" && cond.op === "!") {
    const vf = variantFact(cond.expr, ctx);
    if (vf) return vf;
  }
  if (cond.kind === "binop" && (cond.op === "!==" || cond.op === "!=")) {
    const eq = { ...cond, op: "===" };
    const tof = typeofStringFact(eq, ctx);
    if (tof) return tof;
  }
  return null;
}
