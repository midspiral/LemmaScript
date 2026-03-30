/**
 * Array contains — for-of loop example.
 */

export function arrayContains(arr: number[], target: number): boolean {
  //@ ensures \result === true ==> exists(k: nat, k < arr.length && arr[k] === target)
  //@ ensures \result === false ==> forall(k: nat, k < arr.length ==> arr[k] !== target)

  let found = false;
  for (const x of arr) {
    //@ invariant found === false ==> forall(k: nat, k < _x_idx ==> arr[k] !== target)
    //@ invariant found === true ==> exists(k: nat, k < arr.length && arr[k] === target)
    //@ done_with found === true || !(_x_idx < arr.length)
    if (x === target) {
      found = true;
      break;
    }
  }
  return found;
}
