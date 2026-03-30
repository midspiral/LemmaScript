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

// ── Primitive mapping ────────────────────────────────────────

export function tsTypeToLean(tsType: string): string {
  const t = tsType.trim();
  if (t === "number") return "Int";
  if (t === "boolean") return "Bool";
  if (t === "string") return "String";
  if (t === "void" || t === "undefined") return "Unit";
  // Array types
  if (t === "number[]") return "Array Int";
  if (t === "boolean[]") return "Array Bool";
  if (t === "string[]") return "Array String";
  const arrMatch = t.match(/^(?:Array<(.+)>|(.+)\[\])$/);
  if (arrMatch) return `Array ${tsTypeToLean(arrMatch[1] || arrMatch[2])}`;
  // User-defined: pass through (same name in Lean)
  return t;
}

// ── Derived queries ──────────────────────────────────────────

export function isNatType(leanType: string): boolean {
  return leanType === "Nat";
}

export function isArrayType(leanType: string): boolean {
  return leanType.startsWith("Array ");
}
