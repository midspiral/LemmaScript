/**
 * Pure Place representation for unified mutation write-back
 * (`midspiral/LemmaScript#387`, Milestone 3a / `robertpenner/LemmaScript#49`).
 *
 * Kept strictly inside the LemmaScript subset so its structural contracts
 * (root identity, depth/step-length correspondence, non-overlap soundness) are
 * self-verified via `npx lsc check --backend=dafny tools/src/places.ts`.
 */

export type PlaceStep =
  | { kind: "field"; field: string }
  | { kind: "index"; idxTag: string }
  | { kind: "mapKey"; keyTag: string }
  | { kind: "unwrap" }
  | { kind: "variant"; tag: string };

export interface PlacePath {
  root: string;
  steps: PlaceStep[];
}

//@ pure
export function makeVarPlace(name: string): PlacePath {
  return { root: name, steps: [] };
}

//@ pure
//@ ensures \result.root == p.root
//@ ensures \result.steps.length == p.steps.length + 1
export function extendFieldPlace(p: PlacePath, field: string): PlacePath {
  return { root: p.root, steps: [...p.steps, { kind: "field", field }] };
}

//@ pure
//@ ensures \result.root == p.root
//@ ensures \result.steps.length == p.steps.length + 1
export function extendIndexPlace(p: PlacePath, idxTag: string): PlacePath {
  return { root: p.root, steps: [...p.steps, { kind: "index", idxTag }] };
}

//@ pure
//@ ensures \result.root == p.root
//@ ensures \result.steps.length == p.steps.length + 1
export function extendMapKeyPlace(p: PlacePath, keyTag: string): PlacePath {
  return { root: p.root, steps: [...p.steps, { kind: "mapKey", keyTag }] };
}

//@ pure
//@ ensures \result.root == p.root
//@ ensures \result.steps.length == p.steps.length + 1
export function extendUnwrapPlace(p: PlacePath): PlacePath {
  return { root: p.root, steps: [...p.steps, { kind: "unwrap" }] };
}

//@ pure
//@ ensures \result.root == p.root
//@ ensures \result.steps.length == p.steps.length + 1
export function extendVariantPlace(p: PlacePath, tag: string): PlacePath {
  return { root: p.root, steps: [...p.steps, { kind: "variant", tag }] };
}

//@ pure
//@ ensures \result == p.root
export function placeRoot(p: PlacePath): string {
  return p.root;
}

//@ pure
//@ ensures \result >= 0
//@ ensures \result == p.steps.length
export function placeDepth(p: PlacePath): number {
  return p.steps.length;
}

//@ pure
//@ ensures \result == (p.steps.length == 0)
export function placeIsVar(p: PlacePath): boolean {
  return p.steps.length === 0;
}

/** Sound step-compatibility check: returns false only when two steps are
 *  provably distinct (different field names or different union variant tags,
 *  or incompatible step kinds at the same position). */
//@ pure
export function stepsMayMatch(a: PlaceStep, b: PlaceStep): boolean {
  if (a.kind === "field") {
    if (b.kind === "field") return a.field === b.field;
    return false;
  }
  if (a.kind === "variant") {
    if (b.kind === "variant") return a.tag === b.tag;
    return false;
  }
  if (a.kind === "unwrap") {
    return b.kind === "unwrap";
  }
  if (a.kind === "index") {
    return b.kind === "index";
  }
  return b.kind === "mapKey";
}

/** Sound overlap predicate on PlacePaths:
 *  - Different roots can never overlap (returns false).
 *  - Same root: if any shared prefix position has incompatible steps
 *    (for example `.a` vs `.b`, or variant `"circle"` vs `"square"`),
 *    returns false. Otherwise conservatively returns true. */
//@ ensures a.root != b.root ==> !\result
export function placesMayOverlap(a: PlacePath, b: PlacePath): boolean {
  if (a.root !== b.root) return false;
  const limit = a.steps.length < b.steps.length ? a.steps.length : b.steps.length;
  let i = 0;
  while (i < limit) {
    //@ invariant 0 <= i && i <= limit
    if (!stepsMayMatch(a.steps[i], b.steps[i])) {
      return false;
    }
    i = i + 1;
  }
  return true;
}

/** True iff `p` contains at least one `unwrap` step (Option/Nullish payload). */
export function placeHasUnwrap(p: PlacePath): boolean {
  let i = 0;
  while (i < p.steps.length) {
    //@ invariant 0 <= i && i <= p.steps.length
    if (p.steps[i].kind === "unwrap") return true;
    i = i + 1;
  }
  return false;
}

/** True iff `p` contains at least one `variant` step (discriminated union payload). */
export function placeHasVariant(p: PlacePath): boolean {
  let i = 0;
  while (i < p.steps.length) {
    //@ invariant 0 <= i && i <= p.steps.length
    if (p.steps[i].kind === "variant") return true;
    i = i + 1;
  }
  return false;
}
