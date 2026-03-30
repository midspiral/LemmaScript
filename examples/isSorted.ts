/**
 * Is-sorted check — verifies a boolean-returning function matches a spec.
 */

export function isSorted(arr: number[]): boolean {
  //@ requires arr.length > 0
  //@ ensures \result === true ==> forall(k: nat, k + 1 < arr.length ==> arr[k] <= arr[k + 1])
  //@ ensures \result === false ==> exists(k: nat, k + 1 < arr.length && arr[k] > arr[k + 1])
  //@ type i nat

  let result = true;
  let i = 0;
  while (i + 1 < arr.length) {
    //@ invariant i < arr.length
    //@ invariant result === true ==> forall(k: nat, k < i ==> arr[k] <= arr[k + 1])
    //@ invariant result === false ==> exists(k: nat, k + 1 < arr.length && arr[k] > arr[k + 1])
    //@ done_with result === false || !(i + 1 < arr.length)
    //@ decreases arr.length - i
    if (arr[i] > arr[i + 1]) {
      result = false;
      break;
    }
    i = i + 1;
  }
  return result;
}
