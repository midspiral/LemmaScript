import «forContinue.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct countOdds by
  loom_solve

prove_correct copyNonzero by
  loom_solve

prove_correct countPositivesNonNested by
  loom_solve

prove_correct countKeep by
  loom_solve
