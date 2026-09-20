import «clampAll.def»

set_option velvet.semantics.termination "total"

prove_correct clampElement by
  velvet_vcgen [clampElement] with finish

prove_correct clampAll by
  velvet_vcgen [clampAll] with finish
