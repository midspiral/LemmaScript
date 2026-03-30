/**
 * Max element — exercises exists quantifier and array comparisons.
 */

export function maxElement(arr: number[]): number {
  //@ requires arr.length > 0
  //@ ensures forall(k: nat, k < arr.length ==> arr[k] <= \result)
  //@ ensures exists(k: nat, k < arr.length && arr[k] === \result)
  //@ type i nat

  let max = arr[0];
  let i = 1;
  while (i < arr.length) {
    //@ invariant 1 <= i && i <= arr.length
    //@ invariant forall(k: nat, k < i ==> arr[k] <= max)
    //@ invariant exists(k: nat, k < i && arr[k] === max)
    //@ decreases arr.length - i
    if (arr[i] > max) {
      max = arr[i];
    }
    i = i + 1;
  }
  return max;
}
