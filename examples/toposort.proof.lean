import «toposort.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"
set_option maxHeartbeats 3200000

prove_correct topologicalSort by
  loom_goals_intro
  all_goals (first | loom_unfold; loom_solver | skip)
  all_goals sorry
