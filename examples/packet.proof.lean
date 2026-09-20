import «packet.def»

set_option velvet.semantics.termination "total"

prove_correct nextSeq by
  velvet_vcgen [nextSeq] with finish [Pure.nextSeq]
