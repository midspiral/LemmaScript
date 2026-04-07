import «toposort.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"
set_option maxHeartbeats 3200000

section TopoProof
set_option loom.solver "custom"
set_option hygiene false in
macro_rules
| `(tactic|loom_solver) => `(tactic| first
  | grind (splits := 30)
  | omega
  | (simp only [WithName, typeWithName, WithName.mk', WithName.erase] at *;
     simp_all [Array.size_push]; omega))

prove_correct topologicalSort by
  loom_goals_intro
  all_goals (first | (loom_unfold; loom_solver) | skip)
  -- Remaining: queue.push(neighbor).size ≤ nodeIds.size
  -- Needs ghost tracking (enqueued ⊆ nodeIds) as in the Dafny proof
  all_goals sorry

end TopoProof
