/**
 * C-style `for (init; cond; update)` desugars to `init; while (cond) { body; update; }`.
 * A `continue` inside the body would skip the trailing `update`, so the desugar
 * inserts a copy of the update statement immediately before each same-scope
 * `continue` to preserve loop progress. Nested loops (`while`, `for-of`) have
 * their own continue scope and must not receive the outer update.
 */

//@ backend dafny

// Skip-evens count: walks `xs`, skipping even values via `continue`. The
// `continue` is in the same scope as the outer `for`; the desugar must
// insert `i = i + 1` immediately before the `continue`.
export function countOdds(xs: number[]): number {
  //@ verify
  //@ type i nat
  //@ ensures \result <= xs.length
  let n = 0;
  for (let i = 0; i < xs.length; i = i + 1) {
    //@ invariant i <= xs.length
    //@ invariant n <= i
    //@ decreases xs.length - i
    if (xs[i]! % 2 === 0) continue;
    n = n + 1;
  }
  return n;
}

// Chain of mid-body early-continues (the shape in mastra's
// `sanitizeOrphanedToolPairs` output loop). Some `continue`s have a body
// before them, some are bare. The single-trailing-guard inversion does not
// cover this chain — each `continue` must get the `i = i + 1` update before it.
export function copyNonzero(xs: number[]): number[] {
  //@ verify
  //@ type i nat
  //@ ensures \result.length <= xs.length
  const out: number[] = [];
  for (let i = 0; i < xs.length; i = i + 1) {
    //@ invariant i <= xs.length
    //@ invariant out.length <= i
    //@ decreases xs.length - i
    const v = xs[i]!;
    if (v === 0) {
      continue;
    }
    if (v < 0) continue;
    out.push(v);
  }
  return out;
}

// Inner `continue` belongs to the inner `for-of` loop and must NOT receive
// the outer `for`'s update. If the desugar incorrectly inserts the outer
// update inside the inner body, this verification fails (or, worse,
// produces broken Dafny that diverges).
export function countPositivesNonNested(grid: number[][]): number {
  //@ verify
  //@ type i nat
  //@ ensures \result >= 0
  let total = 0;
  for (let i = 0; i < grid.length; i = i + 1) {
    //@ invariant i <= grid.length
    //@ invariant total >= 0
    //@ decreases grid.length - i
    const row = grid[i]!;
    for (const x of row) {
      //@ invariant total >= 0
      if (x <= 0) continue;
      total = total + 1;
    }
  }
  return total;
}
