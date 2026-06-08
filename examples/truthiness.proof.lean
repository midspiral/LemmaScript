import «truthiness.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

-- These functions are expression-bodied, so the Lean backend emits a `Pure.*`
-- mirror and the method just delegates (`return Pure.f x`). `loom_solve`'s SMT
-- backend treats that mirror as opaque, so we discharge each postcondition by
-- unfolding the mirror and simplifying — the `simp` IS the truthiness check.

-- This pinned toolchain has no `String.length_eq_zero_iff`; reconstruct it from
-- the underlying char list so the string-truthiness `optStrCond` arm can close.
private theorem str_length_eq_zero_iff {s : String} : s.length = 0 ↔ s = "" := by
  cases s
  simp [String.length, String.ext_iff, List.length_eq_zero_iff]

prove_correct boolCond by
  loom_goals_intro
  loom_unfold
  all_goals (cases b <;> simp_all [Pure.boolCond])

prove_correct numCond by
  loom_goals_intro
  loom_unfold
  all_goals simp_all [Pure.numCond]

prove_correct numNot by
  loom_goals_intro
  loom_unfold
  all_goals simp_all [Pure.numNot]

prove_correct numTernary by
  loom_goals_intro
  loom_unfold
  all_goals simp_all [Pure.numTernary]

prove_correct strCond by
  loom_goals_intro
  loom_unfold
  all_goals simp_all [Pure.strCond]

prove_correct strNot by
  loom_goals_intro
  loom_unfold
  all_goals (simp only [Pure.strNot, ← str_length_eq_zero_iff]; split <;> omega)

prove_correct arrCond by
  loom_goals_intro
  loom_unfold
  all_goals simp_all [Pure.arrCond]

prove_correct arrNot by
  loom_goals_intro
  loom_unfold
  all_goals simp_all [Pure.arrNot]

-- The optional cases also need an explicit split on `o` so the `match o` in each
-- postcondition reduces; then simp closes each arm.
prove_correct optNumCond by
  loom_goals_intro
  loom_unfold
  all_goals (cases o <;> simp_all [Pure.optNumCond])

prove_correct optNumNot by
  loom_goals_intro
  loom_unfold
  all_goals (cases o <;> simp_all [Pure.optNumNot])

prove_correct optStrCond by
  loom_goals_intro
  loom_unfold
  all_goals (cases o <;> simp_all [Pure.optStrCond, str_length_eq_zero_iff])

prove_correct optPresent by
  loom_goals_intro
  loom_unfold
  all_goals (cases o <;> simp_all [Pure.optPresent])
