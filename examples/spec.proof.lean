import «spec.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

-- Pure functions: unfold + loom_solve
prove_correct evalPartial by
  unfold Pure.evalPartial; loom_solve

prove_correct evalSwitch by
  unfold Pure.evalSwitch; loom_solve

prove_correct isHighPriority by
  unfold Pure.isHighPriority; loom_solve

prove_correct defaultConfig by
  unfold Pure.defaultConfig; loom_solve

prove_correct withThreshold by
  unfold Pure.withThreshold; loom_solve

prove_correct clampTernary by
  unfold Pure.clampTernary; loom_solve

prove_correct demoteOnFail by
  unfold Pure.demoteOnFail; loom_solve

prove_correct makeHighItem by
  unfold Pure.makeHighItem; loom_solve

prove_correct midpoint by
  unfold Pure.midpoint; loom_solve

prove_correct wrapOne by
  unfold Pure.wrapOne; loom_solve

prove_correct threeElems by
  unfold Pure.threeElems; loom_solve

prove_correct append by
  unfold Pure.append; loom_solve

-- HOFs
prove_correct doubleAll by
  unfold Pure.doubleAll; loom_solve

prove_correct keepPositive by
  unfold Pure.keepPositive; loom_solve

prove_correct allBelow by
  unfold Pure.allBelow; loom_solve

prove_correct anyNegative by
  unfold Pure.anyNegative; loom_solve

-- Pure function call in HOF lambda
prove_correct negate by
  unfold Pure.negate; loom_solve

prove_correct negateAll by
  unfold Pure.negateAll; loom_solve

prove_correct hasValue by
  unfold Pure.hasValue; loom_solve

prove_correct replaceAt by
  unfold Pure.replaceAt; loom_solve

prove_correct replaceAtInt by
  unfold Pure.replaceAtInt; loom_solve

-- String ops
prove_correct findSubstr by
  unfold Pure.findSubstr; loom_solve

prove_correct getSlice by
  unfold Pure.getSlice; loom_solve

-- While loops
prove_correct countAbove by
  loom_solve

prove_correct search by
  loom_solve

-- Monadic lifting (calls search)
prove_correct sumSearchResults by
  loom_solve

-- For-of loop
prove_correct forOfContains by
  loom_solve

-- Monadic lifting in records and nested args
prove_correct clampedItem by loom_solve
prove_correct clampedMidpoint by loom_solve

-- Deep-path narrowing: body and ensures both use nested Some/None matches
prove_correct deepAccess by
  unfold Pure.deepAccess; loom_solve

-- Negative truthiness `!x` and bare optional truthiness `if (x)`
prove_correct negVar by
  unfold Pure.negVar; loom_solve

prove_correct negField by
  unfold Pure.negField; loom_solve

prove_correct truthyVar by
  unfold Pure.truthyVar; loom_solve

-- Nullish coalescing
prove_correct nullishVar by
  unfold Pure.nullishVar; loom_solve

prove_correct nullishMapGet by
  unfold Pure.nullishMapGet; loom_solve

-- `k in m ? m[k] : default` narrowing (ruleConditionalInMap)
prove_correct inCheckRecordGet by
  unfold Pure.inCheckRecordGet; loom_solve

-- Map-index narrowing via requires / if / assert / while invariants
prove_correct requiresInMap by
  unfold Pure.requiresInMap; loom_solve

prove_correct ifInMapBlock by
  unfold Pure.ifInMapBlock; loom_solve

prove_correct ifNotInMapEarlyReturn by
  unfold Pure.ifNotInMapEarlyReturn; loom_solve

prove_correct assertInMap by
  loom_solve

prove_correct whileInvariantInMap by
  loom_solve

-- Chained && of optional checks in ternary
prove_correct nestedAndTernary by
  unfold Pure.nestedAndTernary; loom_solve

-- Discriminated-union narrowing
prove_correct area by
  unfold Pure.area; loom_solve

prove_correct describeIfCircle by
  unfold Pure.describeIfCircle; loom_solve

-- Ternary in spec with optional narrowing (parallels truthyVar)
prove_correct ternarySpecOpt by
  unfold Pure.ternarySpecOpt; loom_solve

-- Optional chaining
prove_correct ocField by
  unfold Pure.ocField; loom_solve

prove_correct ocChain by
  unfold Pure.ocChain; loom_solve

prove_correct ocMethodCall by
  unfold Pure.ocMethodCall; loom_solve

prove_correct ocIndex by
  unfold Pure.ocIndex; loom_solve
