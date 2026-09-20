import «clamp.def»

set_option velvet.semantics.termination "total"

prove_correct clamp by
  velvet_vcgen [clamp] with finish
