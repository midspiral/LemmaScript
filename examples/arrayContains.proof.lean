import «arrayContains.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct arrayContains by
  loom_solve
