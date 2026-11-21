import «safeInteger.def»

set_option velvet.semantics.termination "total"

prove_correct isSafeInteger by
  velvet_vcgen [isSafeInteger] with finish [Pure.isSafeInteger]

prove_correct isSafeBigInt by
  velvet_vcgen [isSafeBigInt] with finish [Pure.isSafeBigInt]

prove_correct integerBoundaries by
  velvet_vcgen [integerBoundaries] with finish [Pure.integerBoundaries]

prove_correct isSafeBigIntQuotient by
  velvet_vcgen [isSafeBigIntQuotient] with finish [Pure.isSafeBigIntQuotient]

prove_correct checkedBigInt by
  velvet_vcgen [checkedBigInt] with finish

prove_correct isSafeBigIntCall by
  velvet_vcgen [isSafeBigIntCall] with finish
