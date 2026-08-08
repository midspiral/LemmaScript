import «switchEnumField.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct weight by
  unfold Pure.weight
  loom_solve

prove_correct pickPlainString by
  loom_solve
