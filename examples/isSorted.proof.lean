import «isSorted.def»

set_option velvet.semantics.termination "total"

prove_correct isSorted by
  velvet_vcgen [isSorted] with finish
