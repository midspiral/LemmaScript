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

prove_correct isUndefined by
  velvet_vcgen [isUndefined] with finish [Pure.isUndefined]

prove_correct isNull by
  velvet_vcgen [isNull] with finish [Pure.isNull]

prove_correct widenUndefined by
  velvet_vcgen [widenUndefined] with finish [Pure.widenUndefined]

prove_correct widenNull by
  velvet_vcgen [widenNull] with finish [Pure.widenNull]

prove_correct classifyMethod by
  velvet_vcgen [classifyMethod] with
    (expose_names; tactic => cases x <;>
      simp_all [LemmaScript.Nullish.isValue, LemmaScript.Nullish.isNull, LemmaScript.Nullish.get] <;>
      cases h_x)

prove_correct lookupNullable by
  velvet_vcgen [lookupNullable] with finish [Pure.lookupNullable]

prove_correct notNull by
  velvet_vcgen [notNull] with finish [Pure.notNull]

prove_correct gatedNull by
  velvet_vcgen [gatedNull] with finish [Pure.gatedNull]

prove_correct filterAbsent by
  velvet_vcgen [filterAbsent] with finish [Pure.filterAbsent]

prove_correct guardedIdentity by
  velvet_vcgen [guardedIdentity] with
    (expose_names; tactic => cases x <;> simp_all [Pure.guardedIdentity])

prove_correct keepDefined by
  velvet_vcgen [keepDefined] with finish [Pure.keepDefined, Array.size_filterMap_le]

prove_correct overwriteOptional by
  velvet_vcgen [overwriteOptional] with finish

example : Pure.classify .Undefined = 1 := by decide
example : Pure.classify .Null = 2 := by decide
example : Pure.classify (.Value 9) = 9 := by decide
example : Pure.reverse .Undefined = 1 := by decide
example : Pure.reverse .Null = 2 := by decide
example : Pure.reverse (.Value 9) = 9 := by decide
example : Pure.disjunction (.Value 9) = 9 := by decide
example : Pure.retainNull .Null = none := by decide
example : Pure.retainUndefined .Undefined = none := by decide
example : Pure.positive (.Value 1) = true := by decide
example : Pure.positive .Null = false := by decide
example : Pure.absentOrPositive .Undefined = true := by decide
example : Pure.absentOrPositive (.Value (-1)) = false := by decide
example : Pure.isUndefined .Undefined = true := by decide
example : Pure.isUndefined .Null = false := by decide
example : Pure.isUndefined (.Value 0) = false := by decide
example : Pure.isNull .Undefined = false := by decide
example : Pure.isNull .Null = true := by decide
example : Pure.isNull (.Value 0) = false := by decide
example : Pure.widenUndefined none = .Undefined := by decide
example : Pure.widenUndefined (some 0) = .Value 0 := by decide
example : Pure.widenNull none = .Null := by decide
example : Pure.widenNull (some 0) = .Value 0 := by decide

example : Pure.notNull .Null = false := by decide
example : Pure.notNull .Undefined = true := by decide
example : Pure.notNull (.Value 7) = true := by decide
example : Pure.gatedNull .Null true = true := by decide
example : Pure.gatedNull .Null false = false := by decide
example : Pure.gatedNull .Undefined true = false := by decide
example : Pure.gatedNull (.Value (∅ : Std.HashMap Int Int)) true = false := by decide
example : Pure.filterAbsent #[.Null, .Undefined, .Value 7] false = #[.Undefined] := by decide
example : Pure.filterAbsent #[.Null, .Undefined, .Value 7] true = #[.Null, .Undefined, .Value 7] := by decide
example : Pure.guardedIdentity none false = none := by decide
example : Pure.guardedIdentity none true = none := by decide
example : Pure.guardedIdentity (some 7) false = some 7 := by decide
example : Pure.guardedIdentity (some 7) true = some 7 := by decide
example : Pure.keepDefined #[.Undefined, .Null, .Value 7] = #[none, some 7] := by decide
