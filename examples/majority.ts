/**
 * Boyer-Moore majority vote — linear time, constant extra space.
 *
 * Returns the strict majority element of arr (an element appearing strictly
 * more than n/2 times) if one exists, else -1. Elements are required to be
 * non-negative so that -1 is a distinguishable sentinel.
 *
 * The non-obvious bit lives in pass 1's two-sided invariant:
 *
 *   2 * occOf(arr, cand, i) <= i + cnt                          // cand
 *   forall y, y !== cand ==> 2 * occOf(arr, y, i) <= i - cnt    // others
 *
 * Together they say: no value other than cand can be a strict majority of
 * arr[0..i]. At i === arr.length this collapses to: any strict majority
 * of arr must equal cand. Pass 2 then verifies cand by direct count.
 */
//@ pure
function occOf(arr: number[], x: number, n: number): number {
  //@ requires 0 <= n && n <= arr.length
  //@ decreases n
  //@ type n nat
  return n === 0 ? 0 : occOf(arr, x, n - 1) + (arr[n - 1] === x ? 1 : 0);
}

export function majority(arr: number[]): number {
  //@ requires forall(k: nat, k < arr.length ==> arr[k] >= 0)
  //@ ensures \result === -1 || (\result >= 0 && 2 * occOf(arr, \result, arr.length) > arr.length)
  //@ ensures (exists(x: nat, 2 * occOf(arr, x, arr.length) > arr.length)) ==> \result !== -1
  //@ type i nat
  //@ type j nat

  // Pass 1: pick a candidate. If a strict majority exists, it equals cand here.
  let cand = 0;
  let cnt = 0;
  let i = 0;
  while (i < arr.length) {
    //@ invariant 0 <= i && i <= arr.length
    //@ invariant cnt >= 0
    //@ invariant cand >= 0
    //@ invariant 2 * occOf(arr, cand, i) <= i + cnt
    //@ invariant forall(y: int, y !== cand ==> 2 * occOf(arr, y, i) <= i - cnt)
    //@ decreases arr.length - i
    if (cnt === 0) {
      cand = arr[i];
      cnt = 1;
    } else if (arr[i] === cand) {
      cnt = cnt + 1;
    } else {
      cnt = cnt - 1;
    }
    i = i + 1;
  }

  // Pass 2: confirm cand by counting its occurrences directly.
  let occ = 0;
  let j = 0;
  while (j < arr.length) {
    //@ invariant 0 <= j && j <= arr.length
    //@ invariant occ === occOf(arr, cand, j)
    //@ decreases arr.length - j
    if (arr[j] === cand) {
      occ = occ + 1;
    }
    j = j + 1;
  }

  if (2 * occ > arr.length) {
    return cand;
  } else {
    return -1;
  }
}
