import «clampAll.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct clampElement by
  loom_solve

prove_correct clampAll by
  loom_solve
