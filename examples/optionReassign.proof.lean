import «optionReassign.def»

set_option velvet.semantics.termination "total"

prove_correct reassignInIf by
  velvet_vcgen [reassignInIf] with finish

prove_correct reassignAfterEarlyReturn by
  velvet_vcgen [reassignAfterEarlyReturn] with finish

prove_correct reassignOptionalField by
  velvet_vcgen [reassignOptionalField] with finish
