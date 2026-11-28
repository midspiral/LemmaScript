/**
 * Thin shell adapter over the Dafny-verified `spec-type-parser.ts` kernel.
 *
 * Contains no parsing or normalization logic of its own: it only converts the
 * verified `SpecTy` datatype into `Ty` and turns `{ kind: "err" }` into a
 * descriptive `Error`. Zero `ts-morph` dependencies.
 */

import { parseSpecTypeKernel } from "./spec-type-parser.js";
import type { SpecTy } from "./spec-type-parser.js";
import type { Ty } from "./typedir.js";

function specTyToTy(st: SpecTy): Ty {
  switch (st.kind) {
    case "bool": return { kind: "bool" };
    case "nat": return { kind: "nat" };
    case "int": return { kind: "int" };
    case "bigint": return { kind: "int", big: true };
    case "real": return { kind: "real" };
    case "string": return { kind: "string" };
    case "stringUnion": return { kind: "string", values: st.values };
    case "void": return { kind: "void" };
    case "null": return { kind: "null" };
    case "unknown": return { kind: "unknown" };
    case "user": return { kind: "user", name: st.name };
    case "array": return { kind: "array", elem: specTyToTy(st.elem) };
    case "set": return { kind: "set", elem: specTyToTy(st.elem) };
    case "optionalUndef": return { kind: "optional", inner: specTyToTy(st.inner) };
    case "optionalNull": return { kind: "optional", inner: specTyToTy(st.inner), absent: "null" };
    case "nullish": return { kind: "nullish", inner: specTyToTy(st.inner) };
    case "map": return { kind: "map", key: specTyToTy(st.key), value: specTyToTy(st.value) };
    case "tuple": return { kind: "tuple", elems: st.elems.map(specTyToTy) };
    case "fn": return { kind: "fn", params: st.params.map(specTyToTy), result: specTyToTy(st.result) };
  }
}

/**
 * Parse a `//@` spec-annotation type string into a backend-neutral `Ty`.
 * Throws a descriptive `Error` on malformed or unsupported syntax.
 */
export function parseSpecType(text: string): Ty {
  const res = parseSpecTypeKernel(text);
  if (res.kind === "err") {
    throw new Error(`Invalid spec type annotation "${text}": ${res.error}`);
  }
  return specTyToTy(res.ty);
}
