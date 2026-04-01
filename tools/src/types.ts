/**
 * Type mapping — TS types → Lean types.
 *
 * Single source of truth for type-related decisions.
 * The transform phase imports this.
 */

// ── Type info extracted from TS ──────────────────────────────

export interface VariantInfo {
  name: string;
  fields: { name: string; tsType: string }[];
}

export interface UnionTypeInfo {
  name: string;
  discriminant: string;
  variants: VariantInfo[];
}

export interface TypeDeclInfo {
  name: string;
  kind: "string-union" | "discriminated-union" | "record";
  /** For string unions: the literal values */
  values?: string[];
  /** For discriminated unions: the discriminant field and variants */
  discriminant?: string;
  variants?: VariantInfo[];
  /** For records: the fields */
  fields?: { name: string; tsType: string }[];
}

// ── TS type string → Ty (single source of truth) ───────────

import type { Ty } from "./typedir.js";

export function parseTsType(tsType: string): Ty {
  const t = tsType.trim();
  if (t === "number") return { kind: "int" };
  if (t === "nat") return { kind: "nat" };
  if (t === "boolean") return { kind: "bool" };
  if (t === "string") return { kind: "string" };
  if (t === "void" || t === "undefined") return { kind: "void" };
  const m = t.match(/^(?:Array<(.+)>|(.+)\[\])$/);
  if (m) return { kind: "array", elem: parseTsType(m[1] || m[2]) };
  return { kind: "user", name: t };
}

