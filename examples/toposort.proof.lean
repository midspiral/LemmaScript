import «toposort.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"
set_option maxHeartbeats 80000000

-- allDistinct means pairwise inequality
theorem allDistinct_means_no_dups (s : Array String) (n : Nat)
    (h : allDistinct s n) (hn : n ≤ s.size) :
    ∀ i j, i < j → j < n → s[i]! ≠ s[j]! := by
  induction n with
  | zero => intro i j _ hj; omega
  | succ k ih =>
    unfold allDistinct at h
    simp only [show k + 1 ≠ 0 from by omega, ↓reduceDIte, show k + 1 ≤ s.size from hn] at h
    obtain ⟨h_not_mem, h_rest⟩ := h
    intro i j hij hj heq
    if hjk : j < k then
      exact ih h_rest (by omega) i j hij hjk heq
    else
      have hjk : j = k := by omega
      subst hjk
      simp only [show j + 1 - 1 = j from by omega] at h_not_mem ⊢
      exact h_not_mem (by sorry) -- s[i]! ∈ s.toList.take j from i < j and heq

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
  all_goals sorry

end TopoProof
