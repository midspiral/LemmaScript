import «discriminantTrailing.def»

set_option velvet.semantics.termination "total"

prove_correct tally by
  intro s
  cases s <;> velvet_vcgen [tally]
  all_goals expose_names
  all_goals try grind
