import { methods, extraMethods as additionalMethods, emptyMethods } from "./httpMethods.js";

// Build a membership table from a shared list without duplicating its entries.
const known = new Set<string>([...methods, "put"]);

// Literals, local arrays, and imported readonly arrays can be interleaved.
// The repeated get/post entries count once; the empty spread adds nothing.
const firstMethods = ["head"];
const extended = new Set<string>(["options", ...firstMethods, ...methods, "put", ...additionalMethods, ...emptyMethods, "get"]);

export function isKnown(method: string): boolean {
  //@ verify
  //@ ensures \result <==> (method === "get" || method === "post" || method === "put")
  return known.has(method);
}

export function isExtendedKnown(method: string): boolean {
  //@ verify
  //@ ensures \result <==> (method === "options" || method === "head" || method === "get" || method === "post" || method === "put" || method === "delete")
  return extended.has(method);
}

export function distinctMethodCount(): number {
  //@ verify
  //@ ensures \result === 6
  return extended.size;
}

export function emptyMethodCount(): number {
  //@ verify
  //@ ensures \result === 0
  return new Set<string>([...emptyMethods]).size;
}

// The same lowering works for arrays supplied at runtime, including duplicates.
export function hasFromEither(left: string[], right: string[], method: string): boolean {
  //@ verify
  //@ ensures \result <==> (exists(i: nat, i < left.length && left[i] === method) || method === "put" || exists(j: nat, j < right.length && right[j] === method))
  return new Set<string>([...left, "put", ...right]).has(method);
}
