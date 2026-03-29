/**
 * Linear search — return-in-loop with simpler invariants than binary search.
 * No sorted property needed.
 */

export function linearSearch(arr: number[], target: number): number {
  //@ ensures result >= -1 && result < arr.length
  //@ ensures result >= 0 ==> arr[result] === target
  //@ ensures result === -1 ==> forall(k, 0 <= k && k < arr.length ==> arr[k] !== target)

  let i = 0;
  while (i < arr.length) {
    //@ invariant 0 <= i && i <= arr.length
    //@ invariant forall(k, 0 <= k && k < i ==> arr[k] !== target)
    //@ invariant result === -1 || (result >= 0 && result < arr.length && arr[result] === target)
    //@ decreases arr.length - i
    if (arr[i] === target) {
      return i;
    }
    i = i + 1;
  }
  return -1;
}
