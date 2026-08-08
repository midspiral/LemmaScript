//@ backend lean
/**
 * Monadic HOF — callback calls a Velvet method (non-pure function).
 * Tests: mapM variant selection, call-graph purity propagation.
 */

function clampElement(x: number, lo: number, hi: number): number {
  //@ requires lo <= hi
  //@ ensures $result >= lo && $result <= hi
  let result = x;
  if (result < lo) {
    result = lo;
  }
  if (result > hi) {
    result = hi;
  }
  return result;
}

function clampAll(arr: number[], lo: number, hi: number): number[] {
  //@ requires lo <= hi
  return arr.map((x) => clampElement(x, lo, hi));
}
