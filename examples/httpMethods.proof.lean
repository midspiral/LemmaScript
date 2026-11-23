import «httpMethods.def»

set_option velvet.semantics.termination "total"

prove_correct isBaseMethod by
  velvet_vcgen [isBaseMethod] with
    (tactic => simp [Pure.isBaseMethod, methods])
