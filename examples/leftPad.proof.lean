import «leftPad.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

-- `loom_solve` alone can't discharge the loop invariant `(ch ++ result).length
-- = str.length + (i + 1)`: the solver doesn't know how `++` and `.length`
-- interact. Feeding `String.length_append` into the pre-solve simp set rewrites
-- the goal to linear arithmetic, which closes automatically.
attribute [loomLogicSimp] String.length_append

prove_correct leftPad by
  loom_solve
