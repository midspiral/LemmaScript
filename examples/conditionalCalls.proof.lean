import «conditionalCalls.def»

set_option velvet.semantics.termination "total"

prove_correct checkedIncrement by
  velvet_vcgen [checkedIncrement] with finish

prove_correct chooseThen by
  velvet_vcgen [chooseThen] with finish

prove_correct chooseElse by
  velvet_vcgen [chooseElse] with finish

prove_correct chooseBoth by
  velvet_vcgen [chooseBoth] with finish

prove_correct guardedAnd by
  velvet_vcgen [guardedAnd] with finish

prove_correct guardedOr by
  velvet_vcgen [guardedOr] with finish

prove_correct nestedChoice by
  velvet_vcgen [nestedChoice] with finish

prove_correct choiceArgument by
  velvet_vcgen [choiceArgument] with finish

prove_correct optionalChoice by
  velvet_vcgen [optionalChoice] with finish
