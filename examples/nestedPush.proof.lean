import «nestedPush.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct pushItem by
  loom_solve
