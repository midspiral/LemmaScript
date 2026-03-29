import «arraySum.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct arraySum by
  loom_solve
