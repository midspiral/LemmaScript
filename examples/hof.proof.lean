import «hof.def»

set_option velvet.semantics.termination "total"

prove_correct doubleAll by
  velvet_vcgen [doubleAll] with finish [Pure.doubleAll]
