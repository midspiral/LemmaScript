import «spec.def»

set_option velvet.semantics.termination "total"

-- Pure functions: unfold their compiled definitions.
prove_correct evalPartial by
  velvet_vcgen [evalPartial] with finish [Pure.evalPartial]

prove_correct evalSwitch by
  velvet_vcgen [evalSwitch] with finish [Pure.evalSwitch]

prove_correct isHighPriority by
  velvet_vcgen [isHighPriority] with finish [Pure.isHighPriority]

prove_correct defaultConfig by
  velvet_vcgen [defaultConfig] with finish [Pure.defaultConfig]

prove_correct withThreshold by
  velvet_vcgen [withThreshold] with finish [Pure.withThreshold]

prove_correct clampTernary by
  velvet_vcgen [clampTernary] with finish [Pure.clampTernary]

prove_correct demoteOnFail by
  velvet_vcgen [demoteOnFail] with finish [Pure.demoteOnFail]

prove_correct makeHighItem by
  velvet_vcgen [makeHighItem] with finish [Pure.makeHighItem]

prove_correct midpoint by
  velvet_vcgen [midpoint] with finish [Pure.midpoint]

prove_correct exactBigIntLiteral by
  velvet_vcgen [exactBigIntLiteral] with finish [Pure.exactBigIntLiteral]

prove_correct exactNegativeBigIntLiteral by
  velvet_vcgen [exactNegativeBigIntLiteral] with finish [Pure.exactNegativeBigIntLiteral]

prove_correct wrapOne by
  velvet_vcgen [wrapOne] with finish [Pure.wrapOne]

prove_correct threeElems by
  velvet_vcgen [threeElems]
  all_goals simp [Pure.threeElems]

prove_correct append by
  velvet_vcgen [append] with finish [Pure.append]

-- HOFs
prove_correct doubleAll by
  velvet_vcgen [doubleAll] with finish [Pure.doubleAll]

prove_correct keepPositive by
  velvet_vcgen [keepPositive] with finish [Pure.keepPositive]

prove_correct allBelow by
  velvet_vcgen [allBelow] with finish [Pure.allBelow]

prove_correct anyNegative by
  velvet_vcgen [anyNegative] with finish [Pure.anyNegative]

-- Pure function call in HOF lambda
prove_correct negate by
  velvet_vcgen [negate] with finish [Pure.negate]

prove_correct negateAll by
  velvet_vcgen [negateAll] with finish [Pure.negateAll]

prove_correct hasValue by
  velvet_vcgen [hasValue] with finish [Pure.hasValue]

prove_correct replaceAt by
  velvet_vcgen [replaceAt] with finish [Pure.replaceAt]

prove_correct replaceAtInt by
  velvet_vcgen [replaceAtInt] with finish [Pure.replaceAtInt]

-- String ops
prove_correct findSubstr by
  velvet_vcgen [findSubstr] with finish [Pure.findSubstr]

prove_correct getSlice by
  velvet_vcgen [getSlice] with finish [Pure.getSlice]

-- While loops
prove_correct countAbove by
  velvet_vcgen [countAbove] with finish

prove_correct search by
  velvet_vcgen [search] with finish

-- Monadic lifting (calls search)
prove_correct sumSearchResults by
  velvet_vcgen [sumSearchResults] with finish

-- For-of loop
prove_correct forOfContains by
  velvet_vcgen [forOfContains] with finish

-- Monadic lifting in records and nested args
prove_correct clampedItem by
  velvet_vcgen [clampedItem] with finish
prove_correct clampedMidpoint by
  velvet_vcgen [clampedMidpoint] with finish

-- Deep-path narrowing: body and ensures both use nested Some/None matches
prove_correct deepAccess by
  velvet_vcgen [deepAccess] with finish [Pure.deepAccess]

-- Negative truthiness `!x` and bare optional truthiness `if (x)`
prove_correct negVar by
  velvet_vcgen [negVar] with finish [Pure.negVar]

prove_correct negField by
  velvet_vcgen [negField] with finish [Pure.negField]

prove_correct truthyVar by
  velvet_vcgen [truthyVar] with finish [Pure.truthyVar]

-- Nullish coalescing
prove_correct nullishVar by
  velvet_vcgen [nullishVar] with finish [Pure.nullishVar]

prove_correct nullishMapGet by
  velvet_vcgen [nullishMapGet] with finish [Pure.nullishMapGet]

-- `k in m ? m[k] : default` narrowing (ruleConditionalInMap)
prove_correct inCheckRecordGet by
  velvet_vcgen [inCheckRecordGet] with finish [Pure.inCheckRecordGet]

-- Map-index narrowing via requires / if / assert / while invariants
prove_correct requiresInMap by
  velvet_vcgen [requiresInMap] with finish [Pure.requiresInMap]

prove_correct ifInMapBlock by
  velvet_vcgen [ifInMapBlock] with finish [Pure.ifInMapBlock]

prove_correct ifNotInMapEarlyReturn by
  velvet_vcgen [ifNotInMapEarlyReturn] with finish [Pure.ifNotInMapEarlyReturn]

prove_correct assertInMap by
  velvet_vcgen [assertInMap] with finish

prove_correct whileInvariantInMap by
  velvet_vcgen [whileInvariantInMap] with finish

-- Chained && of optional checks in ternary
prove_correct nestedAndTernary by
  velvet_vcgen [nestedAndTernary] with finish [Pure.nestedAndTernary]

-- Discriminated-union narrowing
prove_correct area by
  velvet_vcgen [area] with finish [Pure.area]

prove_correct describeIfCircle by
  velvet_vcgen [describeIfCircle] with finish [Pure.describeIfCircle]

-- Ternary in spec with optional narrowing (parallels truthyVar)
prove_correct ternarySpecOpt by
  velvet_vcgen [ternarySpecOpt] with finish [Pure.ternarySpecOpt]

-- Optional chaining
prove_correct ocField by
  velvet_vcgen [ocField] with finish [Pure.ocField]

prove_correct ocChain by
  velvet_vcgen [ocChain] with finish [Pure.ocChain]

prove_correct ocMethodCall by
  velvet_vcgen [ocMethodCall] with finish [Pure.ocMethodCall]

prove_correct ocIndex by
  velvet_vcgen [ocIndex] with finish [Pure.ocIndex]
