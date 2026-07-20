import «optChainDiscriminantTernary.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

-- Expression-bodied, so each method delegates to its `Pure.*` mirror; unfold it
-- and split on the optional so the discriminant/field `match` in each arm
-- reduces (mirrors truthiness.proof's optional cases).
prove_correct textOr by
  loom_goals_intro
  loom_unfold
  all_goals (cases e <;> simp_all [Pure.textOr])

prove_correct textOrFlipped by
  loom_goals_intro
  loom_unfold
  all_goals (cases e <;> simp_all [Pure.textOrFlipped])

prove_correct bodyOr by
  loom_goals_intro
  loom_unfold
  all_goals (cases r <;> simp_all [Pure.bodyOr])

prove_correct firstText by
  loom_goals_intro
  loom_unfold
  all_goals (cases e <;> simp_all [Pure.firstText])
