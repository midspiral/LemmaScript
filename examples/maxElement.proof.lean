import «maxElement.def»

set_option velvet.semantics.termination "total"

prove_correct maxElement by
  velvet_vcgen [maxElement] with finish
