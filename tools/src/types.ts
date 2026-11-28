/**
 * Shared type metadata and canonical rendering for backend-neutral `Ty`.
 *
 * Extraction (`extract-types.ts`) produces structured `Ty` directly from
 * ts-morph `Type`/`TypeNode`, and `spec-type.ts` parses `//@` annotation type
 * text into `Ty`. Downstream passes consume `Ty` without `ts-morph`.
 */

import type { Ty } from "./typedir.js";

// ── Type info extracted from TS ──────────────────────────────

export interface FieldInfo {
  name: string;
  tsType: string;
  type?: Ty;     // structured Ty populated by extract (or spec-type for //@ declare-type)
  /** Declared with `?` (`f?: T`): the key itself may be absent, not just the value. */
  optionalKey?: boolean;
}

export interface VariantInfo {
  name: string;
  fields: FieldInfo[];
}

export interface UnionTypeInfo {
  name: string;
  discriminant: string;
  variants: VariantInfo[];
}

export interface TypeDeclInfo {
  name: string;
  typeParams?: string[];
  kind: "string-union" | "discriminated-union" | "record" | "alias" | "opaque";
  /** For string unions: the literal values */
  values?: string[];
  /** For discriminated unions: the discriminant field and variants */
  discriminant?: string;
  variants?: VariantInfo[];
  /** For records: the fields */
  fields?: FieldInfo[];
  /** For alias: the underlying type string */
  aliasOf?: string;
  aliasOfTy?: Ty;  // pre-computed Ty for aliasOf
  /** Numeric const enum: integer semantics; members exist only on value bindings.
   * A type-only alias has an empty member list. */
  constEnumMembers?: { name: string; value: number }[];
}

/** Render a Ty in LemmaScript canonical syntax — backend-neutral, side-effect-free.
 *  Used by `lsc info` for the signature field of `foo.ts.json`. */
export function tyToCanonical(ty: Ty): string {
  switch (ty.kind) {
    case "bool":   return "bool";
    case "nat":    return "nat";
    case "int":    return "int";
    case "real":   return "real";
    case "string": return "string";
    case "void":   return "void";
    case "null":   return "null";
    case "unknown":return "unknown";
    case "array":  return `seq<${tyToCanonical(ty.elem)}>`;
    case "tuple":  return `(${ty.elems.map(tyToCanonical).join(", ")})`;
    case "map":    return `map<${tyToCanonical(ty.key)}, ${tyToCanonical(ty.value)}>`;
    case "set":    return `set<${tyToCanonical(ty.elem)}>`;
    case "optional": return `Option<${tyToCanonical(ty.inner)}>`;
    case "nullish":  return `Nullish<${tyToCanonical(ty.inner)}>`;
    case "user":   return ty.name;
    case "fn":     return `(${ty.params.map(tyToCanonical).join(", ")}) -> ${tyToCanonical(ty.result)}`;
  }
}

