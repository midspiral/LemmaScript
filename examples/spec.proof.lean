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
