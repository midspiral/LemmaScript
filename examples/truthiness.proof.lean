import «truthiness.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct boolCond by
  loom_solve

prove_correct numCond by
  loom_solve

prove_correct numNot by
  loom_solve

prove_correct numTernary by
  loom_solve

prove_correct strCond by
  loom_solve

prove_correct strNot by
  loom_solve

prove_correct arrCond by
  loom_solve

prove_correct arrNot by
  loom_solve

prove_correct optNumCond by
  loom_solve

prove_correct optNumNot by
  loom_solve

prove_correct optStrCond by
  loom_solve

prove_correct optPresent by
  loom_solve
