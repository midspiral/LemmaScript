import «forContinue.def»

set_option velvet.semantics.termination "total"

prove_correct countOdds by
  velvet_vcgen [countOdds] with finish

prove_correct copyNonzero by
  velvet_vcgen [copyNonzero] with finish

prove_correct countPositivesNonNested by
  velvet_vcgen [countPositivesNonNested] with finish

prove_correct countKeep by
  velvet_vcgen [countKeep] with finish
