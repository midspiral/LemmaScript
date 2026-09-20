import «switchEnumField.def»

set_option velvet.semantics.termination "total"

prove_correct weight by
  velvet_vcgen [weight] with finish [Pure.weight]

prove_correct pickPlainString by
  velvet_vcgen [pickPlainString] with finish
