import «setSpread.types»

namespace SetSpread

theorem extended_size : extended.size = 6 := by
  unfold extended
  rw [Std.HashSet.Equiv.size_eq Std.HashSet.ofList_equiv_foldl]
  simp [firstMethods, _imported0_methods, _imported1_extraMethods,
    _imported2_emptyMethods, List.foldl, Std.HashSet.size_insert]

theorem mem_iff_index (xs : Array String) (x : String) :
    x ∈ xs ↔ ∃ i : Nat, i < xs.size ∧ xs[i]! = x := by
  rw [Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, by simpa [getElem!_pos xs i hi] using hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, by simpa [getElem!_pos xs i hi] using hx⟩

end SetSpread
