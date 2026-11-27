import «unionReassign.def»

set_option velvet.semantics.termination "total"

prove_correct sharedFieldAfterReassignToNext by
  intro input next
  cases input <;> cases next <;> velvet_vcgen [sharedFieldAfterReassignToNext] with finish

prove_correct tagChangingSpread by
  intro input
  cases input <;> velvet_vcgen [tagChangingSpread] with finish

prove_correct binderNoCapture by
  intro input _f1
  cases input <;> velvet_vcgen [binderNoCapture] with finish
