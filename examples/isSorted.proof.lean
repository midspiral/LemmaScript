import «isSorted.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct isSorted by
  loom_solve
