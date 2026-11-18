import «stringIndex.def»

set_option velvet.semantics.termination "total"

prove_correct firstIsA by
  velvet_vcgen [firstIsA] with finish [Pure.firstIsA]

prove_correct sameAt by
  velvet_vcgen [sameAt] with finish [Pure.sameAt, StringIndexExample.index_eq_slice]

prove_correct indexedChar by
  velvet_vcgen [indexedChar] with finish
    [Pure.indexedChar, StringIndexExample.index_eq_slice, StringIndexExample.index_length]
