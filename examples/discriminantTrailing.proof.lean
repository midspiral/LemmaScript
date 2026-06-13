import «discriminantTrailing.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct tally by
  cases s <;> loom_solve
