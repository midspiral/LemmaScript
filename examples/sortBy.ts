/**
 * In-place `Array.prototype.sort(cmp)` is modeled as reassignment to a
 * permutation of the input sorted by the comparator (Dafny only). The model
 * `requires` the comparator to be a total preorder — the soundness condition for
 * a sorted permutation to exist — which the standard key-difference idiom
 * `(a, b) => a.k - b.k` discharges automatically by linear arithmetic. The
 * result is a same-length, same-multiset permutation, sorted ascending by key.
 */

//@ backend dafny

interface Rec {
  k: number;
}

export function sortByKey(input: Rec[]): Rec[] {
  //@ ensures \result.length === input.length
  //@ ensures forall(i: nat, i + 1 < \result.length ==> \result[i].k <= \result[i + 1].k)
  const xs = input.slice();
  xs.sort((a, b) => a.k - b.k);
  return xs;
}
