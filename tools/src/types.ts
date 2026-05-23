/**
 * Type mapping — TS types → Lean types.
 *
 * Single source of truth for type-related decisions.
 * The transform phase imports this.
 */

// ── Type info extracted from TS ──────────────────────────────

export interface FieldInfo {
  name: string;
  tsType: string;
  type?: Ty;     // pre-computed Ty — populated by resolveModule, avoids re-parsing tsType
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
  kind: "string-union" | "discriminated-union" | "record" | "alias";
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
  // Function type: `(a: T1, b: T2) => R` or `(T1, T2) => R`. Match the
  // outermost `(...) => R` shape; param names (with `:`) are stripped.
  // Handled before union so that arrow-types whose return is a union don't
  // get consumed by the union branch.
  if (t.startsWith("(") && t.includes(") => ")) {
    const arrowIdx = t.lastIndexOf(") => ");
    let depth = 0;
    let openIdx = -1;
    for (let i = 0; i <= arrowIdx; i++) {
      if (t[i] === "(") { if (depth === 0) openIdx = i; depth++; }
      else if (t[i] === ")") depth--;
    }
    if (openIdx === 0) {
      const paramsStr = t.slice(openIdx + 1, arrowIdx);
      const ret = t.slice(arrowIdx + 5).trim();
      const paramArgs = paramsStr.length === 0 ? [] : splitTypeArgs(paramsStr);
      const params = paramArgs.map(a => {
        const colon = a.indexOf(":");
        return parseTsType(colon >= 0 ? a.slice(colon + 1) : a);
      });
      return { kind: "fn", params, result: parseTsType(ret) };
    }
  }
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
    const nonUndef = arms.filter(a => a !== "undefined" && a !== "null");
    if (nonUndef.length === 1 && arms.length >= 2) {
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
    case "unknown":return "unknown";
    case "array":  return `seq<${tyToCanonical(ty.elem)}>`;
    case "map":    return `map<${tyToCanonical(ty.key)}, ${tyToCanonical(ty.value)}>`;
    case "set":    return `set<${tyToCanonical(ty.elem)}>`;
    case "optional": return `Option<${tyToCanonical(ty.inner)}>`;
    case "user":   return ty.name;
    case "fn":     return `(${ty.params.map(tyToCanonical).join(", ")}) -> ${tyToCanonical(ty.result)}`;
  }
}

