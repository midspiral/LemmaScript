/** Nullish type algebra shared by resolution, condition analysis and lowering. */
import type { Ty, Nullish } from "./typedir.js";
import { tyEqual } from "./typedir.js";

export const UNDEFINED: Ty = { kind: "nullish", nullish: "undefined" };
export const NULL: Ty = { kind: "nullish", nullish: "null" };
export const nullishMask = (n: Nullish): number => n === "null" ? 1 : n === "undefined" ? 2 : 3;
export const maskNullish = (n: number): Nullish => n === 1 ? "null" : n === 2 ? "undefined" : "both";
export const includesNullish = (set: Nullish, tag: Nullish): boolean =>
  (nullishMask(set) & nullishMask(tag)) === nullishMask(tag);
export const unionNullish = (a: Nullish, b: Nullish): Nullish => maskNullish(nullishMask(a) | nullishMask(b));
export const nullishOf = (ty: Ty): Nullish | undefined =>
  ty.kind === "optional" || ty.kind === "nullish" ? ty.nullish : ty.kind === "void" ? "undefined" : undefined;

/** Source unions are flat: (T | null) | undefined has three cases, not four. */
export function optional(inner: Ty, nullish: Nullish = "undefined"): Ty {
  if (inner.kind === "optional") return optional(inner.inner, unionNullish(inner.nullish, nullish));
  if (inner.kind === "nullish" || inner.kind === "void")
    return { kind: "nullish", nullish: unionNullish(nullishOf(inner)!, nullish) };
  return { kind: "optional", inner, nullish };
}

/** Remove precisely the tested alternatives. Impossible singleton branches
 * retain their type; lowering eliminates them instead of inventing a payload. */
export function excludeNullish(ty: Ty, excluded: Nullish): Ty {
  const modes = nullishOf(ty);
  if (!modes) return ty;
  const remaining = nullishMask(modes) & ~nullishMask(excluded);
  if (ty.kind === "optional") return remaining ? optional(ty.inner, maskNullish(remaining)) : ty.inner;
  return remaining ? { kind: "nullish", nullish: maskNullish(remaining) } : ty;
}

export function joinTypes(a: Ty, b: Ty): Ty {
  if (tyEqual(a, b)) return a;
  if (a.kind === "unknown") return b;
  if (b.kind === "unknown") return a;
  const an = nullishOf(a), bn = nullishOf(b);
  const ap = a.kind === "optional" ? a.inner : an ? undefined : a;
  const bp = b.kind === "optional" ? b.inner : bn ? undefined : b;
  const payload = ap && bp ? joinPayloads(ap, bp) : ap ?? bp;
  const modes = an && bn ? unionNullish(an, bn) : an ?? bn;
  return modes ? payload ? optional(payload, modes) : { kind: "nullish", nullish: modes }
    : payload!;
}

function joinPayloads(a: Ty, b: Ty): Ty {
  if ((a.kind === "int" || a.kind === "nat") && (b.kind === "int" || b.kind === "nat"))
    return { ...a, kind: a.kind === "int" || b.kind === "int" ? "int" : "nat" };
  if (a.kind === "array" && b.kind === "array") return { kind: "array", elem: joinTypes(a.elem, b.elem) };
  return a;
}
