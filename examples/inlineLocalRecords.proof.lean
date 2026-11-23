import «inlineLocalRecords.def»

set_option velvet.semantics.termination "total"

prove_correct sumA by
  velvet_vcgen [sumA] with finish [Pure'.sumA]

prove_correct mk by
  velvet_vcgen [mk] with finish [Pure'.mk]

prove_correct localAfterAssignment by
  velvet_vcgen [localAfterAssignment] with finish

prove_correct optionalLocal by
  velvet_vcgen [optionalLocal] with finish [Pure'.optionalLocal]

prove_correct localFallback by
  velvet_vcgen [localFallback] with finish [Pure'.localFallback]
