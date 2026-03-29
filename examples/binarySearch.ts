/**
 * Binary search — verified with LemmaScript.
 */

export function binarySearch(arr: number[], target: number): number {
  //@ requires sorted(arr)
  //@ requires arr.length > 0
  //@ ensures \result >= -1 && \result < arr.length
  //@ ensures \result >= 0 ==> arr[\result] === target
  //@ ensures \result === -1 ==> forall(k, 0 <= k && k < arr.length ==> arr[k] !== target)

  let lo = 0;
  let hi = arr.length - 1;
  let result = -1;

  while (lo <= hi) {
    //@ invariant 0 <= lo && lo <= arr.length
    //@ invariant -1 <= hi && hi < arr.length
    //@ invariant forall(k, 0 <= k && k < lo ==> arr[k] !== target)
    //@ invariant forall(k, hi < k && k < arr.length ==> arr[k] !== target)
    //@ invariant result === -1 || (result >= 0 && result < arr.length && arr[result] === target)
    //@ done_with result !== -1 || !(lo <= hi)
    //@ decreases (hi - lo + 1).toNat

    const mid = Math.floor((lo + hi) / 2);

    if (arr[mid] === target) {
      result = mid;
      break;
    } else if (arr[mid] < target) {
      lo = mid + 1;
    } else {
      hi = mid - 1;
    }
  }

  return result;
}
