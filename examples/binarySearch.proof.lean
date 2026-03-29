import «binarySearch.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct binarySearch by
  loom_solve
