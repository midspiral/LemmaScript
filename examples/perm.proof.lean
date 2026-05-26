import «perm.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

namespace PermProof

-- Peel the head off the count: for nonempty `xs`, the number of `true` flags is
-- the head's contribution plus the count over the `.extract 1 _` tail. The tail
-- is `xs.toList.drop 1` (extract from 1 keeps everything past the head), so this
-- is just `List.count_cons` after re-associating the array view as a list.
theorem count_peel (xs : Array Bool) (h : xs.size ≠ 0) :
    xs.toList.count true =
      (if xs[0]! = true then 1 else 0) + (xs.extract 1 xs.size).toList.count true := by
  have hpos : 0 < xs.size := Nat.pos_of_ne_zero h
  have hlen : 0 < xs.toList.length := by rw [Array.length_toList]; exact hpos
  have hdroplen : (xs.toList.drop 1).length = xs.size - 1 := by
    rw [List.length_drop, Array.length_toList]
  rw [Array.toList_extract, List.extract_eq_drop_take, ← hdroplen, List.take_length]
  have hhead : xs[0]! = xs.toList[0]! := by
    rw [getElem!_pos xs 0 hpos, ← Array.getElem_toList,
        getElem!_pos xs.toList 0 hlen]
  rw [hhead]
  conv_lhs => rw [← List.take_append_drop 1 xs.toList, List.count_append]
  congr 1
  rw [List.take_one]
  cases hl : xs.toList with
  | nil => rw [hl] at hlen; simp at hlen
  | cons a t => simp [List.count_cons]

theorem countOn_eq_count (xs : Array Bool) :
    Pure.countOn xs = (xs.toList.count true : Int) := by
  induction xs using Pure.countOn.induct with
  | case1 xs h =>
    have hnil : xs.toList = [] := by
      rw [Array.toList_eq_nil_iff]; exact Array.size_eq_zero_iff.mp h
    rw [Pure.countOn]; simp [h, hnil]
  | case2 xs h ih =>
    rw [Pure.countOn, if_neg h, ih, count_peel xs h]
    push_cast
    split <;> rfl

-- A count is non-negative and bounded by the length — the `countOn` postcondition.
theorem countOn_bounds (xs : Array Bool) :
    0 ≤ Pure.countOn xs ∧ Pure.countOn xs ≤ xs.size := by
  rw [countOn_eq_count]
  have hle := List.count_le_length (a := true) (l := xs.toList)
  rw [Array.length_toList] at hle
  omega

end PermProof

prove_correct countOn by
  loom_solve
  · exact (PermProof.countOn_bounds xs).2
  · exact (PermProof.countOn_bounds xs).1

prove_correct permRefl by
  unfold Pure.permRefl; loom_solve

prove_correct permSymm by
  unfold Pure.permSymm; loom_solve

prove_correct permConcatComm by
  unfold Pure.permConcatComm; loom_solve

-- The payoff: `countOn` is permutation-invariant. `countOn` is the multiplicity
-- of `true` (countOn_eq_count), and `List.Perm.count_eq` makes any count equal
-- across permutations.
prove_correct countOnPerm by
  unfold Pure.countOnPerm
  loom_solve
  rw [PermProof.countOn_eq_count, PermProof.countOn_eq_count]
  exact_mod_cast require_1.count_eq true
