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

prove_correct popUnionField by
  intro input
  cases input <;> velvet_vcgen [popUnionField] with finish

prove_correct makeA by
  velvet_vcgen [makeA] with finish [Pure.makeA]

prove_correct bumpMixed by
  intro sh nextVal
  cases sh <;> velvet_vcgen [bumpMixed] with finish [Pure.bumpMixed]
