import «setFromArray.def»

set_option velvet.semantics.termination "total"

prove_correct member by
  velvet_vcgen [member]
  all_goals expose_names
  simp only [Pure.member, Std.HashSet.contains_ofList, List.contains_iff_mem,
    Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, by simpa [getElem!_pos arr i hi] using hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, by simpa [getElem!_pos arr i hi] using hx⟩
