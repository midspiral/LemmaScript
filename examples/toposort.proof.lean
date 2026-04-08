import «toposort.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"
set_option maxHeartbeats 1600000

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
    (hsub : ∀ k, enqueued.contains k = true → ∃ j : Int, 0 ≤ j ∧ j < ↑i ∧ nodeIds[j.toNat]! = k) :
    ¬(enqueued.contains nodeIds[i]! = true) := by
  intro hc
  obtain ⟨j, hj0, hjlt, hjeq⟩ := hsub _ hc
  have hj_nat : j.toNat < i := by omega
  exact allDistinct_means_no_dups nodeIds nodeIds.size hdist (Nat.le_refl _)
    j.toNat i hj_nat hi (by rw [hjeq])

-- HashMap get! + insert helpers (the Std API uses getElem! not get!)
theorem hashmap_get!_insert_self_string {m : Std.HashMap String Int} {k : String} {v : Int} :
    (m.insert k v).get! k = v := by
  show (m.insert k v)[k]! = v; simp

theorem hashmap_get!_insert_ne_string {m : Std.HashMap String Int} {k a : String} {v : Int}
    (h : ¬(k = a)) : (m.insert k v).get! a = m.get! a := by
  show (m.insert k v)[a]! = m[a]!
  rw [Std.HashMap.getElem!_insert]; split
  · next heq => exact absurd (eq_of_beq heq) h
  · rfl

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
  -- Handle remaining goals
  all_goals (first
    | (simp only [WithName] at *;
       exact not_enqueued_of_distinct _ _ _ (by omega) (by assumption) (by assumption))
    | skip)
  -- Goal 1: Phase 3 push — subset invariant after enqueued.insert
  next => simp only [WithName] at *; intro k hk
          simp [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hk
          rcases hk with rfl | hk
          · exact ⟨↑i_4, by omega, by omega, rfl⟩
          · obtain ⟨j, hj0, hjlt, hjeq⟩ := invariant_15 k hk; exact ⟨j, hj0, by omega, hjeq⟩
  -- Goal 2: Phase 3 no-push — weaken j < i_4 to j < i_4+1
  next => simp only [WithName] at *; intro k hk
          obtain ⟨j, hj0, hjlt, hjeq⟩ := invariant_15 k hk; exact ⟨j, hj0, by omega, hjeq⟩
  -- Goal 3: Inner loop insert — enqueued size bound (TODO: needs extra invariant)
  next => sorry
  -- Goal 4: Inner loop push — inDegree invariant (enqueued.insert, newDeg = 0)
  next => simp only [WithName] at *; intro k hk
          simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hk
          rcases hk with rfl | hk
          · -- k = neighbor: use insert_self
            refine ⟨?_, ?_⟩
            · simp [Std.HashMap.contains_insert_self]
            · simp_all [hashmap_get!_insert_self_string]
          · -- k ∈ enqueued_2, k ≠ neighbor
            obtain ⟨hc, hg⟩ := invariant_31 k hk
            have hne : ¬(((i_2.get? queue_2[qHead.toNat]!).get ‹_›)[i_6]! = k) :=
              fun h => a_2 (h ▸ hk)
            refine ⟨?_, ?_⟩
            · simp only [Std.HashMap.contains_insert, Bool.or_eq_true]; right; exact hc
            · rw [hashmap_get!_insert_ne_string hne]; exact hg
  -- Goal 5: Inner loop no-push — inDegree invariant (enqueued unchanged, newDeg ≠ 0)
  next => simp only [WithName] at *; intro k hk
          obtain ⟨hc, hg⟩ := invariant_31 k hk
          refine ⟨?_, ?_⟩
          · simp only [Std.HashMap.contains_insert, Bool.or_eq_true]; right; exact hc
          · by_cases heq : ((i_2.get? queue_2[qHead.toNat]!).get ‹_›)[i_6]! = k
            · simp_all [hashmap_get!_insert_self_string]; omega
            · rw [hashmap_get!_insert_ne_string heq]; exact hg

end TopoProof
