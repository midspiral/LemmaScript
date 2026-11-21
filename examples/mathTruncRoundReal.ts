/**
 * Math.trunc and Math.round on real operands (Dafny only: the Lean backend
 * does not support `real`).
 *
 * In idealized mode a `number` is an exact mathematical real: there is no -0,
 * NaN, or Infinity. Math.round lowers to FloorReal(x + 0.5) with an exact sum,
 * which matches JS Math.round on every finite double.
 */

//@ backend dafny

// Math.trunc drops the fractional part, rounding toward zero.
export function truncReal(): boolean {
  //@ ensures \result === true
  return Math.trunc(2.9) === 2 && Math.trunc(-2.9) === -2 && Math.trunc(-0.5) === 0;
}

// A whole-number literal such as -3.0 resolves as an integer, so a real
// parameter is needed to send a negative whole number through TruncReal.
export function negativeWholeReal(x: number): boolean {
  //@ type x real
  //@ requires x === -3
  //@ ensures \result === true
  return Math.trunc(x) === -3 && Math.round(x) === -3;
}

// Math.round rounds halfway ties toward +Infinity.
export function roundReal(): boolean {
  //@ ensures \result === true
  return Math.round(2.5) === 3 && Math.round(-2.5) === -2 && Math.round(-2.51) === -3 &&
    Math.round(-0.5) === 0 && Math.round(2.4) === 2;
}

// A real variable truncates toward zero: within 1 of x, on the zero side.
export function truncRealVar(x: number): number {
  //@ type x real
  //@ ensures x >= 0 ==> \result <= x && x < \result + 1
  //@ ensures x < 0 ==> \result - 1 < x && x <= \result
  //@ ensures x === 0 ==> \result === 0
  return Math.trunc(x);
}

// Rounding a real variable lands within one half of it.
export function roundRealVar(x: number): number {
  //@ type x real
  //@ ensures x - 0.5 < \result && \result <= x + 0.5
  return Math.round(x);
}
