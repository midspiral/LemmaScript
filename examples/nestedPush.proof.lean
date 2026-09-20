import «nestedPush.def»

set_option velvet.semantics.termination "total"

prove_correct pushItem by
  velvet_vcgen [pushItem] with finish
