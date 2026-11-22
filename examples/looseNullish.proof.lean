import «looseNullish.def»

prove_correct looseIsNullish by
  velvet_vcgen [looseIsNullish] with finish [Pure.looseIsNullish]

prove_correct looseOptional by
  velvet_vcgen [looseOptional] with finish [Pure.looseOptional]

prove_correct looseNullable by
  velvet_vcgen [looseNullable] with finish [Pure.looseNullable]

prove_correct looseDefault by
  velvet_vcgen [looseDefault] with finish [Pure.looseDefault]

prove_correct looseEarlyReturn by
  velvet_vcgen [looseEarlyReturn] with finish [Pure.looseEarlyReturn]

prove_correct loosePositive by
  velvet_vcgen [loosePositive] with finish [Pure.loosePositive]

prove_correct looseAbsentOrPositive by
  velvet_vcgen [looseAbsentOrPositive] with finish [Pure.looseAbsentOrPositive]

prove_correct looseField by
  velvet_vcgen [looseField] with finish [Pure.looseField]

prove_correct looseCompare by
  velvet_vcgen [looseCompare] with
    (expose_names; tactic => cases a <;> cases b <;> simp_all [Pure.looseCompare] <;> grind)

example : Pure.looseIsNullish none = true := by decide
example : Pure.looseIsNullish (some none) = true := by decide
example : Pure.looseIsNullish (some (some 0)) = false := by decide
example : Pure.looseOptional none = true := by decide
example : Pure.looseOptional (some 0) = false := by decide
example : Pure.looseNullable none = false := by decide
example : Pure.looseNullable (some 0) = true := by decide
example : Pure.looseDefault none = 7 := by decide
example : Pure.looseDefault (some none) = 7 := by decide
example : Pure.looseDefault (some (some 0)) = 0 := by decide
example : Pure.looseEarlyReturn none = 7 := by decide
example : Pure.looseEarlyReturn (some none) = 7 := by decide
example : Pure.looseEarlyReturn (some (some 0)) = 0 := by decide
example : Pure.looseField ⟨none⟩ = 7 := by decide
example : Pure.looseField ⟨some none⟩ = 7 := by decide
example : Pure.looseField ⟨some (some 0)⟩ = 0 := by decide
example : Pure.looseCompare none none = true := by decide
example : Pure.looseCompare (some 0) none = false := by decide
example : Pure.looseCompare none (some 0) = false := by decide
example : Pure.looseCompare (some 0) (some 0) = true := by decide
example : Pure.looseCompare (some 0) (some 1) = false := by decide
