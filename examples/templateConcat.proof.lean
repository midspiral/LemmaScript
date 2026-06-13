import «templateConcat.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct bracketed by
  loom_solve
  simp only [Pure.bracketed, String.length_append]
  have h1 : "[".length = 1 := by decide
  have h2 : "][".length = 2 := by decide
  have h3 : "]".length = 1 := by decide
  omega
