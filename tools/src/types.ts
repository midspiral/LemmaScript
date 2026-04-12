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
  typeParams?: string[];
  kind: "string-union" | "discriminated-union" | "record" | "alias";
  /** For string unions: the literal values */
  values?: string[];
  /** For discriminated unions: the discriminant field and variants */
  discriminant?: string;
  variants?: VariantInfo[];
  /** For records: the fields */
  fields?: { name: string; tsType: string }[];
  /** For alias: the underlying type string */
  aliasOf?: string;
}

// ── TS type string → Ty (single source of truth) ───────────

import type { Ty } from "./typedir.js";


/** Split generic type arguments respecting nested angle brackets. */
function splitTypeArgs(s: string): string[] {
  const args: string[] = [];
  let depth = 0, start = 0;
  for (let i = 0; i < s.length; i++) {
    if (s[i] === '<') depth++;
    else if (s[i] === '>') depth--;
    else if (s[i] === ',' && depth === 0) {
      args.push(s.slice(start, i));
      start = i + 1;
    }
  }
  args.push(s.slice(start));
  return args.map(a => a.trim());
}

export function parseTsType(tsType: string): Ty {
  const t = tsType.trim();
  // Union: T | undefined → optional<T>
  if (t.includes(" | ")) {
    let arms = t.split(" | ").map(a => a.trim());
    // Normalize expanded boolean literals: true | false → boolean
    const boolLits = new Set(["true", "false"]);
    const hasBoth = arms.includes("true") && arms.includes("false");
    if (hasBoth) {
      arms = arms.filter(a => !boolLits.has(a));
      arms.unshift("boolean");
    }
    const nonUndef = arms.filter(a => a !== "undefined");
    if (nonUndef.length === 1 && arms.length === 2) {
      return { kind: "optional", inner: parseTsType(nonUndef[0]) };
    }
  }
  if (t === "number") return { kind: "int" };
  if (t === "bigint") return { kind: "int" };
  if (t === "nat") return { kind: "nat" };
  if (t === "boolean" || t === "true" || t === "false") return { kind: "bool" };
  if (t === "string") return { kind: "string" };
  if (t === "void" || t === "undefined") return { kind: "void" };
  if (t === "unknown") return { kind: "unknown" };
  // Record<K, V> → map
  const recordMatch = t.match(/^Record<(.+)>$/);
  if (recordMatch) {
    const args = splitTypeArgs(recordMatch[1]);
    if (args.length === 2) return { kind: "map", key: parseTsType(args[0]), value: parseTsType(args[1]) };
  }
  // Array<T> or T[]
  const m = t.match(/^(?:Array<(.+)>|(.+)\[\])$/);
  if (m) return { kind: "array", elem: parseTsType(m[1] || m[2]) };
  // Map<K, V>
  const mapMatch = t.match(/^Map<(.+)>$/);
  if (mapMatch) {
    const args = splitTypeArgs(mapMatch[1]);
    if (args.length === 2) return { kind: "map", key: parseTsType(args[0]), value: parseTsType(args[1]) };
  }
  // Set<T>
  const setMatch = t.match(/^Set<(.+)>$/);
  if (setMatch) return { kind: "set", elem: parseTsType(setMatch[1]) };
  // Tuple [T1, T2, ...] → array of the common element type
  const tupleMatch = t.match(/^\[(.+)\]$/);
  if (tupleMatch) {
    const elems = splitTypeArgs(tupleMatch[1]);
    return { kind: "array", elem: parseTsType(elems[0]) };
  }
  return { kind: "user", name: t };
}

