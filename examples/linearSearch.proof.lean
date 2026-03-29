import «linearSearch.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct linearSearch by
  loom_solve
