/**
 * `new Set(arr)` must build a deduplicated set, not alias the array as a seq.
 * Lowers to a real set on both backends (Dafny `set x | x in arr` via the
 * SetFromSeq preamble; Lean `Std.HashSet.ofArray`), so `.size` is the distinct
 * count and `.has` is set membership ⟺ array membership.
 */

export function dedupSize(arr: number[]): number {
  const s = new Set(arr);
  return s.size;
}

export function member(arr: number[], x: number): boolean {
  //@ ensures \result <==> exists(i: nat, i < arr.length && arr[i] === x)
  const s = new Set(arr);
  return s.has(x);
}
