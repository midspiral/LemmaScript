import «truthiness.def»

set_option velvet.semantics.termination "total"

-- These functions are expression-bodied, so the Lean backend emits a `Pure.*`
-- mirror and the method just delegates (`return Pure.f x`). The verifier
-- treats that mirror as opaque, so we discharge each postcondition by
-- unfolding the mirror and simplifying — the `simp` IS the truthiness check.

prove_correct boolCond by
  velvet_vcgen [boolCond]
  all_goals expose_names
  all_goals (cases b <;> simp_all [Pure.boolCond])

prove_correct numCond by
  velvet_vcgen [numCond]
  all_goals expose_names
  all_goals simp_all [Pure.numCond]

prove_correct numNot by
  velvet_vcgen [numNot]
  all_goals expose_names
  all_goals simp_all [Pure.numNot]

prove_correct numTernary by
  velvet_vcgen [numTernary]
  all_goals expose_names
  all_goals simp_all [Pure.numTernary]

prove_correct strCond by
  velvet_vcgen [strCond]
  all_goals expose_names
  all_goals simp_all [Pure.strCond]

prove_correct strNot by
  velvet_vcgen [strNot]
  all_goals expose_names
  all_goals (simp only [Pure.strNot, ← String.length_eq_zero_iff]; split <;> omega)

prove_correct arrCond by
  velvet_vcgen [arrCond]
  all_goals expose_names
  all_goals simp_all [Pure.arrCond]

prove_correct arrNot by
  velvet_vcgen [arrNot]
  all_goals expose_names
  all_goals simp_all [Pure.arrNot]

-- The optional cases also need an explicit split on `o` so the `match o` in each
-- postcondition reduces; then simp closes each arm.
prove_correct optNumCond by
  velvet_vcgen [optNumCond]
  all_goals expose_names
  all_goals (cases o <;> simp_all [Pure.optNumCond])

prove_correct optNumNot by
  velvet_vcgen [optNumNot]
  all_goals expose_names
  all_goals (cases o <;> simp_all [Pure.optNumNot])

prove_correct optStrCond by
  velvet_vcgen [optStrCond]
  all_goals expose_names
  all_goals (cases o <;> simp_all [Pure.optStrCond, String.length_eq_zero_iff])

prove_correct optPresent by
  velvet_vcgen [optPresent]
  all_goals expose_names
  all_goals (cases o <;> simp_all [Pure.optPresent])
