/**
 * Higher-order function examples.
 */

export function doubleAll(arr: number[]): number[] {
  //@ ensures \result.length === arr.length
  return arr.map((x) => x * 2);
}

export function positives(arr: number[]): number[] {
  return arr.filter((x) => x > 0);
}

export function allPositive(arr: number[]): boolean {
  return arr.every((x) => x > 0);
}

export function hasNegative(arr: number[]): boolean {
  return arr.some((x) => x < 0);
}
