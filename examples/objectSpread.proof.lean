import «objectSpread.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct withSpreadLast by
  loom_solve
  simp [Pure.withSpreadLast]

prove_correct withFieldLast by
  loom_solve
  simp [Pure.withFieldLast]
