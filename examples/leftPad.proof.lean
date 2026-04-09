import «leftPad.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct leftPad by
  loom_solve
