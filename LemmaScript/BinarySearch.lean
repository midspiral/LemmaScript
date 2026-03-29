/-
  LemmaScript Phase 0 — Binary Search feasibility proof

  This file is what the `lsc` code generator would eventually produce
  (plus the spec content from a .spec.lean file). For Phase 0 we
  hand-write it using Velvet's `method` syntax on top of Loom.

  Source: examples/binarySearch.ts
-/
import Velvet.Syntax
import Velvet.Std

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

-- ============================================================
-- Ghost definitions (would live in binarySearch.spec.lean)
-- ============================================================

/-- An array is sorted iff elements are non-decreasing. -/
@[grind, loomAbstractionSimp]
def sorted (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

-- ============================================================
-- Binary search method (generated from binarySearch.ts)
-- ============================================================

-- Use Int-typed quantifiers throughout to match invariants with postconditions.
-- The code generator should emit consistent types to avoid Nat/Int bridging issues.

method binarySearch (arr : Array Int) (target : Int) return (res : Int)
  require sorted arr
  require 0 < arr.size
  ensures -1 ≤ res
  ensures res < arr.size
  ensures 0 ≤ res → arr[res.toNat]! = target
  ensures res = -1 → ∀ k : Int, 0 ≤ k → k < ↑arr.size → arr[k.toNat]! ≠ target
  do
    let mut lo : Int := 0
    let mut hi : Int := arr.size - 1
    let mut result : Int := -1

    while lo ≤ hi
      invariant 0 ≤ lo
      invariant lo ≤ ↑arr.size
      invariant -1 ≤ hi
      invariant hi < ↑arr.size
      -- All elements before lo have been ruled out
      invariant ∀ k : Int, 0 ≤ k → k < lo → arr[k.toNat]! ≠ target
      -- All elements after hi have been ruled out
      invariant ∀ k : Int, hi < k → k < ↑arr.size → arr[k.toNat]! ≠ target
      -- Result tracking: either not found yet, or found at a valid index
      invariant result = -1 ∨ (0 ≤ result ∧ result < ↑arr.size ∧ arr[result.toNat]! = target)
      done_with result ≠ -1 ∨ lo > hi
      decreasing (hi - lo + 1).toNat
    do
      let mid := (lo + hi) / 2

      if arr[mid.toNat]! = target then
        result := mid
        break
      else if arr[mid.toNat]! < target then
        lo := mid + 1
      else
        hi := mid - 1

    return result

-- ============================================================
-- Correctness proof
-- ============================================================

prove_correct binarySearch by
  loom_solve
