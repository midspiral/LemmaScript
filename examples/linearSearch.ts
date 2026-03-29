/**
 * Linear search — verified with LemmaScript.
 */

export function linearSearch(arr: number[], target: number): number {
  //@ ensures \result >= -1 && \result < arr.length
  //@ ensures \result >= 0 ==> arr[\result] === target
  //@ ensures \result === -1 ==> forall(k: nat, k < arr.length ==> arr[k] !== target)
  //@ type i nat

  let i = 0;
  let result = -1;

  while (i < arr.length) {
    //@ invariant 0 <= i && i <= arr.length
    //@ invariant forall(k: nat, k < i ==> arr[k] !== target)
    //@ invariant result === -1 || (result >= 0 && result < arr.length && arr[result] === target)
    //@ done_with result !== -1 || !(i < arr.length)
    //@ decreases arr.length - i
    if (arr[i] === target) {
      result = i;
      break;
    }
    i = i + 1;
  }

  return result;
}
