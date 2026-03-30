import «maxElement.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct maxElement by
  loom_solve
