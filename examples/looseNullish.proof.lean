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

example : Pure.looseIsNullish .Undefined = true := by decide
example : Pure.looseIsNullish .Null = true := by decide
example : Pure.looseIsNullish (.Value 0) = false := by decide
example : Pure.looseOptional none = true := by decide
example : Pure.looseOptional (some 0) = false := by decide
example : Pure.looseNullable none = false := by decide
example : Pure.looseNullable (some 0) = true := by decide
example : Pure.looseDefault .Undefined = 7 := by decide
example : Pure.looseDefault .Null = 7 := by decide
example : Pure.looseDefault (.Value 0) = 0 := by decide
example : Pure.looseEarlyReturn .Undefined = 7 := by decide
example : Pure.looseEarlyReturn .Null = 7 := by decide
example : Pure.looseEarlyReturn (.Value 0) = 0 := by decide
example : Pure.looseField ⟨.Undefined⟩ = 7 := by decide
example : Pure.looseField ⟨.Null⟩ = 7 := by decide
example : Pure.looseField ⟨.Value 0⟩ = 0 := by decide
example : Pure.looseCompare none none = true := by decide
example : Pure.looseCompare (some 0) none = false := by decide
example : Pure.looseCompare none (some 0) = false := by decide
example : Pure.looseCompare (some 0) (some 0) = true := by decide
example : Pure.looseCompare (some 0) (some 1) = false := by decide
