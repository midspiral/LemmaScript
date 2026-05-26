/**
 * perm(a, b) — the spec-only permutation predicate.
 *
 * `perm(a, b)` holds iff `a` and `b` are reorderings of each other (equal as
 * multisets). It exists only inside `//@` annotations; it lowers to
 * `multiset(a) == multiset(b)` in Dafny, and to `a.toList ~ b.toList`
 * (mathlib's `List.Perm`) in Lean. It has no runtime counterpart.
 *
 * This example shows the two ways it earns its keep:
 *   1. The multiset laws come for free — reflexivity, symmetry, and that
 *      swapping two concatenated batches is a permutation all verify with no
 *      hand proof.
 *   2. The payoff: a count over a list is permutation-invariant. `countOn` is
 *      a fold into (ℤ, +); the companion .dfy proves it equals the multiplicity
 *      of `true`, from which invariance under `perm` is immediate. This is the
 *      bridging lemma the Quorum / Quota case studies wanted but could not state.
 */

// Number of `true` flags in the list — a head-recursive fold into (ℤ, +).
function countOn(xs: boolean[]): number {
  //@ ensures 0 <= \result && \result <= xs.length
  //@ decreases xs.length
  if (xs.length === 0) return 0;
  return (xs[0] ? 1 : 0) + countOn(xs.slice(1));
}

// ── Multiset laws (free) ──────────────────────────────────────

// Reflexivity.
function permRefl(xs: boolean[]): boolean {
  //@ ensures perm(xs, xs)
  return true;
}

// Symmetry.
function permSymm(xs: boolean[], ys: boolean[]): boolean {
  //@ requires perm(xs, ys)
  //@ ensures perm(ys, xs)
  return true;
}

// Swapping two concatenated batches is a permutation — the algebraic heart of
// the "order edits arrive in does not matter" convergence argument.
function permConcatComm(xs: boolean[], ys: boolean[]): boolean {
  //@ ensures perm(xs.concat(ys), ys.concat(xs))
  return true;
}

// ── The payoff: countOn is permutation-invariant ─────────────
// Pure-carrier lemma; the induction lives in the companion .dfy.
function countOnPerm(xs: boolean[], ys: boolean[]): boolean {
  //@ requires perm(xs, ys)
  //@ ensures countOn(xs) === countOn(ys)
  return true;
}
