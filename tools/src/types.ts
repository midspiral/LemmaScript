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
    const arms = t.split(" | ").map(a => a.trim());
    const nonUndef = arms.filter(a => a !== "undefined");
    if (nonUndef.length === 1 && arms.length === 2) {
      return { kind: "optional", inner: parseTsType(nonUndef[0]) };
    }
  }
  if (t === "number") return { kind: "int" };
  if (t === "nat") return { kind: "nat" };
  if (t === "boolean") return { kind: "bool" };
  if (t === "string") return { kind: "string" };
  if (t === "void" || t === "undefined") return { kind: "void" };
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
  return { kind: "user", name: t };
}

