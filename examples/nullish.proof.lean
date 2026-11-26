import «nullish.def»

set_option velvet.semantics.termination "total"

prove_correct classifyNullish by
  velvet_vcgen [classifyNullish] with
    (expose_names; tactic =>
      cases value <;>
        simp_all [Pure.classifyNullish, Nullish.isNull, Nullish.isUndefined,
          Nullish.isValue, Nullish.get])

prove_correct defaultNullish by
  velvet_vcgen [defaultNullish] with
    (expose_names; tactic =>
      cases value <;>
        simp_all [Pure.defaultNullish, Nullish.isValue, Nullish.get])

prove_correct widenNullish by
  velvet_vcgen [widenNullish] with
    (expose_names; tactic =>
      cases value <;> cases fallback <;> cases useValue <;>
        simp_all [Pure.widenNullish, Nullish.isNull, Nullish.isUndefined])

prove_correct incrementNullish by
  velvet_vcgen [incrementNullish] with
    (expose_names; tactic =>
      cases value <;>
        simp_all [Nullish.isNull, Nullish.isUndefined, Nullish.isValue, Nullish.get] <;>
        simp [Nullish.isNull, Nullish.isUndefined] at *)
