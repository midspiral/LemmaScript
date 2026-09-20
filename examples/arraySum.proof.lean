import «arraySum.def»

set_option velvet.semantics.termination "total"

prove_correct arraySum by
  velvet_vcgen [arraySum] with finish
