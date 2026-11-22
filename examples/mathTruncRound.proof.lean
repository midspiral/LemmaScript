import «mathTruncRound.def»

set_option velvet.semantics.termination "total"

prove_correct truncDivision by
  velvet_vcgen [truncDivision] with finish [Pure.truncDivision]

prove_correct truncDiv by
  velvet_vcgen [truncDiv] <;> simp only [Pure.truncDiv]
  · intro hb ha
    exact Int.tdiv_nonneg ha (Int.le_of_lt hb)
  · intro hb ha
    have h := Int.tdiv_nonneg (Int.neg_nonneg_of_nonpos ha) (Int.le_of_lt hb)
    rw [Int.neg_tdiv] at h
    omega

prove_correct truncNatQuotient by
  velvet_vcgen [truncNatQuotient] with finish [Pure.truncNatQuotient]

prove_correct truncMixed by
  velvet_vcgen [truncMixed]
  simp [Pure.truncMixed, Int.neg_tdiv]

prove_correct elementAt by
  velvet_vcgen [elementAt] with finish [Pure.elementAt]

prove_correct truncInt by
  velvet_vcgen [truncInt] with finish [Pure.truncInt]

prove_correct roundInt by
  velvet_vcgen [roundInt] with finish [Pure.roundInt]
