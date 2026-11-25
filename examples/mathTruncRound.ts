/**
 * Math.trunc and Math.round on integral operands, supported by both backends.
 *
 * `Math.trunc(a / b)` on integers truncates toward zero, so it lowers straight
 * to truncated integer division (`JSTruncDiv`, Lean `Int.tdiv`) without passing
 * through `real`: 7/2 -> 3, -7/2 -> -3, 7/-2 -> -3 (floor would give -4).
 * An integer argument is already whole, so both functions are the identity on it.
 * Real-valued operands are covered by mathTruncRoundReal.ts (Dafny only).
 */

export function truncDivision(): boolean {
  //@ ensures \result === true
  return Math.trunc(-7 / 2) === -3 && Math.trunc(7 / 2) === 3 && Math.trunc(7 / -2) === -3 &&
    Math.trunc(-7 / -2) === 3 && Math.trunc(-6 / 3) === -2;
}

// The divisor is a parameter, so Dafny must check `b != 0` at the call to JSTruncDiv.
export function truncDiv(a: number, b: number): number {
  //@ requires b !== 0
  //@ ensures b > 0 && a >= 0 ==> \result >= 0
  //@ ensures b > 0 && a <= 0 ==> \result <= 0
  return Math.trunc(a / b);
}

// On nat operands truncation and floor agree.
export function truncNatQuotient(a: number, b: number): number {
  //@ type a nat
  //@ type b nat
  //@ requires b > 0
  //@ ensures \result === Math.floor(a / b)
  return Math.trunc(a / b);
}

// An int dividend over a nat divisor still truncates toward zero, so negating
// the dividend negates the quotient (floor division would not).
export function truncMixed(a: number, b: number): number {
  //@ type b nat
  //@ requires b > 0
  //@ ensures \result === -Math.trunc(-a / b)
  return Math.trunc(a / b);
}

// A nat argument keeps type nat, so the result indexes an array directly.
export function elementAt(xs: number[], i: number): number {
  //@ type i nat
  //@ requires i < xs.length
  //@ ensures \result === xs[i]
  return xs[Math.round(i)];
}

export function truncInt(x: number): number {
  //@ ensures \result === x
  return Math.trunc(x);
}

export function roundInt(x: number): number {
  //@ ensures \result === x
  return Math.round(x);
}
