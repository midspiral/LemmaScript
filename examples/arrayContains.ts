/**
 * Array contains — for-of loop example.
 */

export function arrayContains(arr: number[], target: number): boolean {
  //@ ensures implies($result === true, exists((k: nat) => k < arr.length && arr[k] === target))
  //@ ensures implies($result === false, forall((k: nat) => implies(k < arr.length, arr[k] !== target)))

  let found = false;
  for (const x of arr) {
    //@ invariant implies(found === false, forall((k: nat) => implies(k < _x_idx, arr[k] !== target)))
    //@ invariant implies(found === true, exists((k: nat) => k < arr.length && arr[k] === target))
    //@ done_with found === true || !(_x_idx < arr.length)
    if (x === target) {
      found = true;
      break;
    }
  }
  return found;
}
