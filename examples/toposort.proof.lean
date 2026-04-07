import «toposort.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"
set_option maxHeartbeats 12800000

section TopoProof
set_option loom.solver "custom"
set_option hygiene false in
macro_rules
| `(tactic|loom_solver) => `(tactic| first
  | grind (splits := 30)
  | omega
  | (simp only [WithName] at *;
     simp only [Array.size_push, Std.HashSet.size_insert];
     (try (generalize Std.HashSet.size _ = _es at *));
     split <;> omega)
  | (simp only [WithName] at *; omega))

prove_correct topologicalSort by
  loom_goals_intro
  all_goals (first | (loom_unfold; loom_solver) | skip)
  -- 3 remaining goals: (queue.push x).size ≤ (enqueued.insert x).size
  -- and (enqueued.insert x).size ≤ nodeIds.size
  -- Root cause: omega can't parse Std.HashSet.size in the GOAL after split.
  -- It creates an atom for HashSet.size from hypotheses but not from the goal.
  -- The ∈ case (n+1 ≤ n) is unprovable and needs algorithm-specific reasoning
  -- to show x ∉ enqueued (each node is enqueued at most once).
  all_goals sorry

end TopoProof
