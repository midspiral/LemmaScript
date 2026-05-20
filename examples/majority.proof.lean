import «majority.def»
import «majority.spec»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct occOf by
  loom_solve

prove_correct majority by
  loom_goals_intro
  loom_unfold
  all_goals (try simp only [loomAbstractionSimp] at *)
  all_goals grind (splits := 20)
