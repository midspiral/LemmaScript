import «destructuringDefaults.def»

set_option velvet.semantics.termination "total"

prove_correct optionalDefault by
  velvet_vcgen [optionalDefault] with finish [Pure.optionalDefault]

prove_correct nullableDefault by
  velvet_vcgen [nullableDefault] with finish [Pure.nullableDefault]

prove_correct nullDefault by
  velvet_vcgen [nullDefault] with finish [Pure.nullDefault]

prove_correct nullishDefault by
  velvet_vcgen [nullishDefault] with finish [Pure.nullishDefault]

prove_correct nullishArrayDefault by
  velvet_vcgen [nullishArrayDefault] with finish [Pure.nullishArrayDefault]

prove_correct mixedDefault by
  velvet_vcgen [mixedDefault] with finish [Pure.mixedDefault]

prove_correct mixedArrayDefault by
  velvet_vcgen [mixedArrayDefault] with finish [Pure.mixedArrayDefault]

prove_correct nullableArrayDefault by
  velvet_vcgen [nullableArrayDefault] with finish [Pure.nullableArrayDefault]

prove_correct optionalArrayDefault by
  velvet_vcgen [optionalArrayDefault] with finish [Pure.optionalArrayDefault]

prove_correct nullableParameterDefault by
  velvet_vcgen [nullableParameterDefault] with finish [Pure.nullableParameterDefault]

prove_correct renamedNullableParameterDefault by
  velvet_vcgen [renamedNullableParameterDefault] with finish [Pure.renamedNullableParameterDefault]

prove_correct nullishParameterDefault by
  velvet_vcgen [nullishParameterDefault] with finish [Pure.nullishParameterDefault]

prove_correct parameterDefault by
  velvet_vcgen [parameterDefault] with finish [Pure.parameterDefault]

prove_correct renamedParameterDefault by
  velvet_vcgen [renamedParameterDefault] with finish [Pure.renamedParameterDefault]

prove_correct genericParameterDefault by
  velvet_vcgen [genericParameterDefault] with finish [Pure.genericParameterDefault]

prove_correct unreachableDefault by
  velvet_vcgen [unreachableDefault] with finish [Pure.unreachableDefault]
