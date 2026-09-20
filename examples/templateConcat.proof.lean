import «templateConcat.def»

set_option velvet.semantics.termination "total"

prove_correct bracketed by
  velvet_vcgen [bracketed] with try finish
  all_goals expose_names
  simp only [Pure.bracketed, String.length_append]
  have h1 : "[".length = 1 := by decide
  have h2 : "][".length = 2 := by decide
  have h3 : "]".length = 1 := by decide
  omega
