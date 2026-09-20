import «tuples.def»

set_option velvet.semantics.termination "total"

prove_correct swap by
  velvet_vcgen [swap] with finish [Pure.swap]

prove_correct middle by
  velvet_vcgen [middle] with finish [Pure.middle]

prove_correct addFirstTwo by
  velvet_vcgen [addFirstTwo] with finish [Pure.addFirstTwo]

prove_correct homogeneousStaysSeq by
  velvet_vcgen [homogeneousStaysSeq] with finish [Pure.homogeneousStaysSeq]
