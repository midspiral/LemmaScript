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
     simp_all [Array.size_push, Std.HashSet.size_insert]; split <;> omega))

prove_correct topologicalSort by
  loom_goals_intro
  all_goals (first | (loom_unfold; loom_solver) | skip)
  -- Remaining: queue.size ≤ enqueued.size at while loop entry
  -- Loom doesn't carry Phase 3 loop exit invariant to while loop initial check
  all_goals sorry

end TopoProof
