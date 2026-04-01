import «packet.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct nextSeq by
  unfold Pure.nextSeq; loom_solve
