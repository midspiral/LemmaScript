import «binarySearch.types»

/-! `Pure.sortedFrom` (compiled from `binarySearch.ts`) only relates adjacent
    elements. These lemmas lift it to the pairwise form binary search reasons
    with: `i ≤ j → arr[i]! ≤ arr[j]!`. -/

theorem sortedFrom_step (arr : Array Int) (i : Nat) (h : i + 1 < arr.size)
    (hs : Pure.sortedFrom arr i = true) :
    arr[i]! ≤ arr[i + 1]! ∧ Pure.sortedFrom arr (i + 1) = true := by
  rw [Pure.sortedFrom, if_neg (by omega)] at hs
  simpa using hs

theorem sortedFrom_suffix (arr : Array Int) (i j : Nat) (hij : i ≤ j)
    (hs : Pure.sortedFrom arr i = true) : Pure.sortedFrom arr j = true := by
  induction j, hij using Nat.le_induction with
  | base => exact hs
  | succ n _ ih =>
    by_cases hsz : n + 1 < arr.size
    · exact (sortedFrom_step arr n hsz ih).2
    · rw [Pure.sortedFrom, if_pos (by omega)]

theorem sorted_mono (arr : Array Int) (hs : Pure.sorted arr = true) (i j : Nat)
    (hij : i ≤ j) : j < arr.size → arr[i]! ≤ arr[j]! := by
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ n _ ih =>
    intro hlt
    have h1 : arr[i]! ≤ arr[n]! := ih (by omega)
    have h2 : arr[n]! ≤ arr[n + 1]! :=
      (sortedFrom_step arr n hlt (sortedFrom_suffix arr 0 n (Nat.zero_le n) hs)).1
    exact le_trans h1 h2
