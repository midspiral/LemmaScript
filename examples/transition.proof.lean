import «transition.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct transition by
  loom_solve

prove_correct runSession by
  loom_solve
