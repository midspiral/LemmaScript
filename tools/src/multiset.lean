/-!
  Multiset (bag) operations — Lean counterpart of `multiset.ts` /
  `multiset.dfy` / `multisetAlt.dfy`.

  Each operation here is a thin wrapper around mathlib's native
  `Multiset α`. The wrappers exist so user-facing names line up with
  the TS and Dafny interfaces; for verification purposes each `def`
  unfolds (often via `rfl`) to the underlying mathlib operator.

  Performance note: in performance-sensitive code prefer mathlib's
  operators (`+`, `-`, `∪`, `∩`, `=`, `≤`, `m.card`, etc.) directly.
  These wrappers are kept simple so they reduce away in proofs.

  ## Mapping to multiset.dfy

  | TS / Dafny  | Lean wrapper           | Underlying           |
  |-------------|------------------------|----------------------|
  | Empty       | `empty`                | `0`                  |
  | FromSeq     | `fromList`             | `(s : Multiset α)`   |
  | FromString  | `fromString`           | `(s.data : Multiset Char)` |
  | Size        | `size m`               | `m.card`             |
  | Count       | `count m x`            | `Multiset.count x m` |
  | Add         | `add m x`              | `x ::ₘ m`            |
  | Remove      | `remove m x`           | `m.erase x`          |
  | AddN        | `addN m x n`           | `m + Multiset.replicate n x` |
  | RemoveN     | `removeN m x n`        | `m - Multiset.replicate n x` |
  | Equals      | `equals a b : Bool`    | `decide (a = b)`     |
  | Subset      | `subset a b : Bool`    | `decide (a ≤ b)`     |
  | Union       | `union a b`            | `a ∪ b`              |
  | Intersection| `intersection a b`     | `a ∩ b`              |
  | Difference  | `difference a b`       | `a - b`              |
  | Sum         | `sum a b`              | `a + b`              |
  | ToSeq       | `toList m`             | `m.toList`           |
  | IsAnagram   | `isAnagram s t`        | `multiset(s) = multiset(t)` |
-/

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Lattice

namespace TSMultiset

universe u
variable {α : Type u}

-- ── Constructors ──────────────────────────────────────────────

/-- Empty multiset. -/
def empty : Multiset α := 0

/-- Multiset from a list — uses the standard `List → Multiset` coercion. -/
def fromList (s : List α) : Multiset α := (s : Multiset α)

/-- Multiset of characters from a string. -/
def fromString (s : String) : Multiset Char := (s.data : Multiset Char)

-- ── Queries ──────────────────────────────────────────────────

/-- Total cardinality (counting multiplicity). -/
def size (m : Multiset α) : Nat := m.card

/-- Multiplicity of `x` in `m`. -/
def count [DecidableEq α] (m : Multiset α) (x : α) : Nat :=
  Multiset.count x m

-- ── Immutable updates ────────────────────────────────────────

/-- Add one instance of `x`. -/
def add (m : Multiset α) (x : α) : Multiset α := x ::ₘ m

/-- Remove one instance of `x` (no-op if absent). -/
def remove [DecidableEq α] (m : Multiset α) (x : α) : Multiset α :=
  m.erase x

/-- Add `n` instances of `x`. -/
def addN (m : Multiset α) (x : α) (n : Nat) : Multiset α :=
  m + Multiset.replicate n x

/-- Remove up to `n` instances of `x` (clamped at zero). -/
def removeN [DecidableEq α] (m : Multiset α) (x : α) (n : Nat) : Multiset α :=
  m - Multiset.replicate n x

-- ── Relations ────────────────────────────────────────────────

/-- Decidable equality of multisets. -/
def equals [DecidableEq α] (a b : Multiset α) : Bool := decide (a = b)

/-- `a` is a sub-multiset of `b`. -/
def subset [DecidableEq α] (a b : Multiset α) : Bool := decide (a ≤ b)

-- ── Set-like operations ──────────────────────────────────────

/-- Union — element-wise maximum multiplicity. -/
def union [DecidableEq α] (a b : Multiset α) : Multiset α := a ∪ b

/-- Intersection — element-wise minimum multiplicity. -/
def intersection [DecidableEq α] (a b : Multiset α) : Multiset α := a ∩ b

/-- Difference — `a` with multiplicities of `b` removed (clamped at zero). -/
def difference [DecidableEq α] (a b : Multiset α) : Multiset α := a - b

/-- Sum — element-wise addition of multiplicities. -/
def sum (a b : Multiset α) : Multiset α := a + b

-- ── Conversion ───────────────────────────────────────────────

/-- A flat list representation. -/
def toList (m : Multiset α) : List α := m.toList

-- ── Anagram check ────────────────────────────────────────────

/-- Two strings are anagrams iff their character multisets are equal. -/
def isAnagram (s t : String) : Bool :=
  equals (fromString s) (fromString t)

-- ── Trivial spec equivalences (sanity checks) ────────────────
-- Each wrapper is `rfl`-equal to the underlying mathlib operator,
-- so callers can rewrite back and forth freely in proofs.

@[simp] theorem empty_eq : (empty : Multiset α) = 0 := rfl
@[simp] theorem fromList_eq (s : List α) : fromList s = (s : Multiset α) := rfl
@[simp] theorem size_eq (m : Multiset α) : size m = m.card := rfl
@[simp] theorem count_eq [DecidableEq α] (m : Multiset α) (x : α) :
    count m x = Multiset.count x m := rfl
@[simp] theorem add_eq (m : Multiset α) (x : α) : add m x = x ::ₘ m := rfl
@[simp] theorem remove_eq [DecidableEq α] (m : Multiset α) (x : α) :
    remove m x = m.erase x := rfl
@[simp] theorem addN_eq (m : Multiset α) (x : α) (n : Nat) :
    addN m x n = m + Multiset.replicate n x := rfl
@[simp] theorem removeN_eq [DecidableEq α] (m : Multiset α) (x : α) (n : Nat) :
    removeN m x n = m - Multiset.replicate n x := rfl
@[simp] theorem equals_eq [DecidableEq α] (a b : Multiset α) :
    equals a b = decide (a = b) := rfl
@[simp] theorem subset_eq [DecidableEq α] (a b : Multiset α) :
    subset a b = decide (a ≤ b) := rfl
@[simp] theorem union_eq [DecidableEq α] (a b : Multiset α) :
    union a b = a ∪ b := rfl
@[simp] theorem intersection_eq [DecidableEq α] (a b : Multiset α) :
    intersection a b = a ∩ b := rfl
@[simp] theorem difference_eq [DecidableEq α] (a b : Multiset α) :
    difference a b = a - b := rfl
@[simp] theorem sum_eq (a b : Multiset α) : sum a b = a + b := rfl
@[simp] theorem toList_eq (m : Multiset α) : toList m = m.toList := rfl

end TSMultiset
