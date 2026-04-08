/**
 * Swap two elements in an array.
 */
function swap(arr: number[], i: number, j: number): number[] {
  //@ type i nat
  //@ type j nat
  //@ requires i < arr.length
  //@ requires j < arr.length
  //@ ensures \result.length === arr.length
  //@ ensures \result[i] === arr[j]
  //@ ensures \result[j] === arr[i]
  let result = arr;
  const tmp = result[i];
  result[i] = result[j];
  result[j] = tmp;
  return result;
}
