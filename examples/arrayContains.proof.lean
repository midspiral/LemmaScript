import «arrayContains.def»

set_option velvet.semantics.termination "total"

prove_correct arrayContains by
  velvet_vcgen [arrayContains] with finish
