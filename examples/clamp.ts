/**
 * Imperative clamp supported by both backends.
 * Tests: mutable locals, conditional assignment, requires/ensures.
 */

function clamp(x: number, lo: number, hi: number): number {
  //@ requires lo <= hi
  //@ ensures \result >= lo && \result <= hi
  let result = x;
  if (result < lo) {
    result = lo;
  }
  if (result > hi) {
    result = hi;
  }
  return result;
}
