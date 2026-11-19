import «optionalLookup.def»

set_option velvet.semantics.termination "total"

prove_correct optionalLookup by
  velvet_vcgen [optionalLookup] with finish [Pure.optionalLookup]
