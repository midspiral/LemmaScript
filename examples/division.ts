/**
 * Division semantics — guards against integer-division unsoundness.
 *
 * JavaScript has one numeric type (IEEE-754 double) and `/` is *always* real
 * (floating) division: `3 / 2 === 1.5`, never `1`. LemmaScript models this, so
 * bare `a / b` resolves to a `real` even when both operands are integers. To
 * get an integer quotient you round explicitly with `Math.floor`, which lowers
 * to the JS-faithful `JSFloorDiv` (floor toward -infinity) — and that is the
 * only division helper we emit; bare `/` needs none.
 *
 * The trap this guards against: before the fix, `int / int` emitted Dafny/Lean
 * *integer* division (`3 / 2 == 1`), so a program could prove postconditions
 * that are false at runtime. The functions below must verify only under
 * real-division semantics.
 *
 * NOTE: postconditions are stated multiplicatively (`\result * b === a`) rather
 * than with a real literal like `1.5`, because the spec lexer does not yet
 * tokenize decimal literals — a separate, related gap.
 */

//@ backend dafny

// Bare `/` on two integer literals is real division: 3 / 2 is 1.5, not 1.
// If the result were integer division (1), `1 * 2 === 3` would be false.
export function threeHalves(): number {
  //@ type \result real
  //@ ensures \result * 2 === 3
  return 3 / 2;
}

// The core case: dividing two integer *variables* yields a real, not an
// integer. `(a / b) * b === a` holds for real division and fails for integer
// division (e.g. a=3, b=2: real gives 3, integer division gives 2).
export function divide(a: number, b: number): number {
  //@ type \result real
  //@ requires b !== 0
  //@ ensures \result * b === a
  return a / b;
}

// Integer (floor) division is opt-in via Math.floor → JSFloorDiv, which floors
// toward -infinity to match JS: 7/2 -> 3, but -7/2 -> -4 (truncation gives -3).
export function floorDivision(): boolean {
  //@ ensures \result === true
  return Math.floor(7 / 2) === 3 && Math.floor(-7 / 2) === -4;
}
