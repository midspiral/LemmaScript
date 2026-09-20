import «linearSearch.def»

set_option velvet.semantics.termination "total"

prove_correct linearSearch by
  velvet_vcgen [linearSearch] with finish
