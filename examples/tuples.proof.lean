import «tuples.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct swap by
  unfold Pure.swap; loom_solve

prove_correct middle by
  unfold Pure.middle; loom_solve

prove_correct addFirstTwo by
  unfold Pure.addFirstTwo; loom_solve

prove_correct homogeneousStaysSeq by
  unfold Pure.homogeneousStaysSeq; loom_solve
