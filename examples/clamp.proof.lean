import «clamp.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct clamp by
  loom_solve

prove_correct clampAll by
  loom_solve
