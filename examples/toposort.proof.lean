import «toposort.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct topologicalSort by
  sorry
