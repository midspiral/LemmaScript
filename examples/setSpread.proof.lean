import «setSpread.def»

set_option velvet.semantics.termination "total"

prove_correct isKnown by
  velvet_vcgen [isKnown] with
    (tactic => simp [Pure.isKnown, known, _imported0_methods])

prove_correct isExtendedKnown by
  velvet_vcgen [isExtendedKnown] with
    (tactic => simp [Pure.isExtendedKnown, extended, firstMethods,
      _imported0_methods, _imported1_extraMethods, _imported2_emptyMethods,
      or_left_comm, or_comm])

prove_correct distinctMethodCount by
  velvet_vcgen [distinctMethodCount] with
    (tactic => simp [Pure.distinctMethodCount, SetSpread.extended_size])

prove_correct emptyMethodCount by
  velvet_vcgen [emptyMethodCount] with (tactic => decide)

prove_correct hasFromEither by
  velvet_vcgen [hasFromEither] with
    (tactic => simp [Pure.hasFromEither, SetSpread.mem_iff_index])
