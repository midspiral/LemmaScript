import «toposort.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"
set_option maxHeartbeats 80000000

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
      apply h_not_mem; rw [← heq]
      have him : i < s.size := by omega
      simp only [getElem!, Array.get!Internal, Array.getD, him,
                 dite_true, Array.getInternal, List.get_eq_getElem]
      have htl : i < (s.toList.take j).length := by simp; omega
      rw [show s.toList[i] = (s.toList.take j)[i] from
        List.getElem_take' (show i < s.toList.length by simp; omega) hij]
      exact List.getElem_mem htl

-- Helper: if all enqueued elements come from nodeIds[0..i] and nodeIds are distinct,
-- then nodeIds[i] is not enqueued.
theorem not_enqueued_of_distinct (nodeIds : Array String) (enqueued : Std.HashSet String)
    (i : Nat) (hi : i < nodeIds.size)
    (hdist : allDistinct nodeIds nodeIds.size)
    (hsub : ∀ k, enqueued.contains k = true → ∃ j, 0 ≤ j ∧ j < i ∧ nodeIds[j]! = k) :
    ¬(enqueued.contains nodeIds[i]! = true) := by
  intro hc
  obtain ⟨j, _, hjlt, hjeq⟩ := hsub _ hc
  exact allDistinct_means_no_dups nodeIds nodeIds.size hdist (Nat.le_refl _)
    j i hjlt hi (by rw [hjeq])

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
  -- Handle assert and remaining goals
  all_goals (first
    | (simp only [WithName] at *;
       apply not_enqueued_of_distinct _ _ _ (by omega) (by assumption)
         (by intro k hk; simp only [WithName] at *; exact ‹_› k hk))
    | sorry)

end TopoProof
