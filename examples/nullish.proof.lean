import «nullish.def»

prove_correct classify by
  velvet_vcgen [classify] with finish [Pure.classify]

prove_correct reverse by
  velvet_vcgen [reverse] with finish [Pure.reverse]

prove_correct disjunction by
  velvet_vcgen [disjunction] with finish [Pure.disjunction]

prove_correct retainNull by
  velvet_vcgen [retainNull] with finish [Pure.retainNull]

prove_correct retainUndefined by
  velvet_vcgen [retainUndefined] with finish [Pure.retainUndefined]

prove_correct positive by
  velvet_vcgen [positive] with finish [Pure.positive]

prove_correct absentOrPositive by
  velvet_vcgen [absentOrPositive] with finish [Pure.absentOrPositive]

example : Pure.classify none = 1 := by decide
example : Pure.classify (some none) = 2 := by decide
example : Pure.classify (some (some 9)) = 9 := by decide
example : Pure.reverse none = 1 := by decide
example : Pure.reverse (some none) = 2 := by decide
example : Pure.reverse (some (some 9)) = 9 := by decide
example : Pure.disjunction (some (some 9)) = 9 := by decide
example : Pure.retainNull (some none) = none := by decide
example : Pure.retainUndefined none = none := by decide
example : Pure.positive (some (some 1)) = true := by decide
example : Pure.positive (some none) = false := by decide
example : Pure.absentOrPositive none = true := by decide
example : Pure.absentOrPositive (some (some (-1))) = false := by decide
