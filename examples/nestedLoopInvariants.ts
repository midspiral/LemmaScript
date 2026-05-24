/**
 * Nested loops with their own `//@ invariant`/`decreases`.
 *
 * A loop's invariants are written as leading comments of its first body
 * statement. When that first statement is itself a loop, those comments sit
 * directly before the inner loop — so annotation collection must take the
 * INNER loop's invariants from the inner loop's body, not from the inner loop
 * node's leading comments (which are the OUTER loop's invariants). Otherwise the
 * outer's `invariant`/`decreases` leak into the inner loop and termination
 * fails (the inner loop inherits the outer's `decreases`). See
 * `collectLoopAnnotations` in extract.ts.
 */

//@ backend dafny

export function nestedSum(n: number): number {
  //@ verify
  //@ type i nat
  //@ type j nat
  //@ requires n >= 0
  //@ ensures \result >= 0
  let acc = 0;
  for (let i = 0; i < n; i = i + 1) {
    //@ invariant 0 <= i && i <= n
    //@ invariant acc >= 0
    //@ decreases n - i
    for (let j = 0; j < n; j = j + 1) {
      //@ invariant 0 <= j && j <= n
      //@ invariant acc >= 0
      //@ decreases n - j
      acc = acc + 1;
    }
  }
  return acc;
}
