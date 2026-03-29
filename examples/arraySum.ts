/**
 * Array sum — simplest verification example.
 * No early return, no break. Pure accumulator pattern.
 */

//@ import { sumTo } from "./arraySum.spec.lean"

export function arraySum(arr: number[]): number {
  //@ ensures result === sumTo(arr, arr.length)
  //@ nat i

  let sum = 0;
  let i = 0;
  while (i < arr.length) {
    //@ invariant 0 <= i && i <= arr.length
    //@ invariant sum === sumTo(arr, i)
    //@ decreases arr.length - i
    sum = sum + arr[i];
    i = i + 1;
  }
  return sum;
}
