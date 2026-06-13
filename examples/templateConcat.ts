/**
 * Template literals are string concatenation, not numeric `+`. `${a}${b}` must
 * stringify each interpolation (Dafny NatToString, Lean toString), so it is NOT
 * `a + b` and `${a}${b}` !== `${b}${a}` in general.
 */

export function noSep(a: number, b: number): string {
  return `${a}${b}`;
}

export function bracketed(a: number, b: number): number {
  //@ ensures \result >= 4
  return `[${a}][${b}]`.length;
}
