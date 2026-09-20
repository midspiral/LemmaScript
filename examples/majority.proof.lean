import «majority.def»
import «majority.spec»

set_option velvet.semantics.termination "total"

prove_correct occOf by
  velvet_vcgen [occOf] with finish

prove_correct majority by
  velvet_vcgen [majority]
  all_goals expose_names
  all_goals try dsimp (zetaDelta := true) only [Named.mk] at *
  all_goals (try simp only [occOf_zero, occOf_step] at *)
  all_goals grind (splits := 20)
