import «hof.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct doubleAll by
  unfold Pure.doubleAll; loom_solve
