import «closureLift.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct flush by
  loom_solve
