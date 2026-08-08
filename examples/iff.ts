/**
 * iff(...) in specs — characterize a boolean result exactly in one
 * clause, instead of a pair of one-directional implications.
 * Unlike an infix extension, the call is valid TypeScript syntax.
 */

//@ verify
//@ requires x >= 0
//@ ensures iff($result, x % 2 === 0)
export function isEven(x: number): boolean {
  return x % 2 === 0;
}

//@ verify
//@ requires x >= 0 && y >= 0
//@ ensures iff($result, iff(x % 2 === 0, y % 2 === 0))
export function sameParity(x: number, y: number): boolean {
  return x % 2 === y % 2;
}
