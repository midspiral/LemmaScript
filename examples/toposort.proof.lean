import «toposort.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"
set_option maxHeartbeats 400000

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

/-- Generic preservation of a `∀ k < i, m.contains s[k]!` invariant under
    `m.insert s[i]! v`. Closes the Phase-1 inDegree carrier and similar
    shapes in Phase 1 / Phase 3. -/
theorem contains_invariant_preserved_int
    {m : Std.HashMap String Int} (s : Array String) (i : Nat) (v : Int)
    (hold : ∀ k : Int, 0 ≤ k → k < ↑i → m.contains s[k.toNat]! = true) :
    ∀ k : Int, 0 ≤ k → k < ↑(i + 1) → (m.insert s[i]! v).contains s[k.toNat]! = true := by
  intro k h0 hlt
  rw [Std.HashMap.contains_insert]
  simp only [Bool.or_eq_true, beq_iff_eq]
  by_cases hke : k.toNat = i
  · left; rw [hke]
  · right; exact hold k h0 (by omega)

/-- Same but for `Std.HashSet`. -/
theorem hashset_contains_invariant_preserved
    (s : Array String) (i : Nat) (h : Std.HashSet String)
    (hold : ∀ k : Nat, k < i → h.contains s[k]! = true) :
    ∀ k : Nat, k < i + 1 → (h.insert s[i]!).contains s[k]! = true := by
  intro k hlt
  rw [Std.HashSet.contains_insert]
  simp only [Bool.or_eq_true, beq_iff_eq]
  by_cases hke : k = i
  · left; rw [hke]
  · right; exact hold k (by omega)

-- TEST: confirm contains_invariant_preserved_int matches the goal shape
example (inDegree : Std.HashMap String Int) (nodeIds : Array String) (i : Nat)
    (h : ∀ (k : ℤ), 0 ≤ k → k < ↑i → inDegree.contains nodeIds[k.toNat]! = true) :
    ∀ (k : ℤ), 0 ≤ k → k < ↑(i + 1) →
      (inDegree.insert nodeIds[i]! 0).contains nodeIds[k.toNat]! = true := by
  apply contains_invariant_preserved_int <;> assumption

/-- Preservation of `∀ k ∈ enqueued, ∃ j < i, nodeIds[j] = k` under
    `enqueued.insert nodeIds[i]!`. Phase 3's invariant_21 / invariant_17. -/
theorem enqueued_witness_preserved
    (nodeIds : Array String) (enqueued : Std.HashSet String) (i : Nat)
    (hold : ∀ k : String, enqueued.contains k = true →
            ∃ j : Int, 0 ≤ j ∧ j < ↑i ∧ nodeIds[j.toNat]! = k) :
    ∀ k : String, (enqueued.insert nodeIds[i]!).contains k = true →
      ∃ j : Int, 0 ≤ j ∧ j < ↑(i + 1) ∧ nodeIds[j.toNat]! = k := by
  intro k hk
  rw [Std.HashSet.contains_insert] at hk
  simp only [Bool.or_eq_true, beq_iff_eq] at hk
  rcases hk with h | h
  · refine ⟨↑i, by omega, by omega, ?_⟩
    rw [Int.toNat_natCast]; exact h
  · obtain ⟨j, h0, hlt, hjeq⟩ := hold k h
    refine ⟨j, h0, ?_, hjeq⟩; omega

/-- Trivial widening of `< i` to `< i + 1` in the witness existential. -/
theorem enqueued_witness_bound_widen
    (nodeIds : Array String) (enqueued : Std.HashSet String) (i : Nat)
    (hold : ∀ k : String, enqueued.contains k = true →
            ∃ j : Int, 0 ≤ j ∧ j < ↑i ∧ nodeIds[j.toNat]! = k) :
    ∀ k : String, enqueued.contains k = true →
      ∃ j : Int, 0 ≤ j ∧ j < ↑(i + 1) ∧ nodeIds[j.toNat]! = k := by
  intro k hk
  obtain ⟨j, h0, hlt, hjeq⟩ := hold k hk
  exact ⟨j, h0, by omega, hjeq⟩

/-- Joint insert preservation for Phase 4 invariant_41:
    `∀ k ∈ enqueued.insert v, (inDegree.insert v newDeg).contains k ∧
                              (inDegree.insert v newDeg).get! k ≤ 0`.
    Uses `newDeg ≤ 0` from the if-newDeg-0 branch and the previous invariant. -/
theorem joint_insert_preserves_inDegree_le_zero
    (enqueued : Std.HashSet String) (inDegree : Std.HashMap String Int)
    (v : String) (newDeg : Int)
    (hv_new : newDeg ≤ 0)
    (hold : ∀ k : String, enqueued.contains k = true →
            inDegree.contains k = true ∧ inDegree.get! k ≤ 0) :
    ∀ k : String, (enqueued.insert v).contains k = true →
      (inDegree.insert v newDeg).contains k = true ∧
      (inDegree.insert v newDeg).get! k ≤ 0 := by
  intro k hk
  rw [Std.HashSet.contains_insert] at hk
  simp only [Bool.or_eq_true, beq_iff_eq] at hk
  rw [Std.HashMap.contains_insert]
  refine ⟨?_, ?_⟩
  · simp only [Bool.or_eq_true, beq_iff_eq]
    rcases hk with h | h
    · left; exact h
    · right; exact (hold k h).1
  · show (inDegree.insert v newDeg)[k]! ≤ 0
    rw [Std.HashMap.getElem!_insert]
    rcases hk with h | h
    · simp [h]; exact hv_new
    · by_cases hkv : (v == k) = true
      · simp [hkv]; exact hv_new
      · simp [hkv]; exact (hold k h).2

/-- Else-branch variant: only inDegree is inserted with `newDeg = oldDeg - 1`.
    For k ∈ enqueued: if k = v, newDeg = inDegree[v] - 1 ≤ -1 ≤ 0; else unchanged.
    Uses `[v]!` (getElem) syntax to match Loom's emitted form. -/
theorem inDegree_insert_preserves_decrement
    (enqueued : Std.HashSet String) (inDegree : Std.HashMap String Int)
    (v : String)
    (hold : ∀ k : String, enqueued.contains k = true →
            inDegree.contains k = true ∧ inDegree.get! k ≤ 0) :
    ∀ k : String, enqueued.contains k = true →
      (inDegree.insert v (inDegree[v]! - 1)).contains k = true ∧
      (inDegree.insert v (inDegree[v]! - 1)).get! k ≤ 0 := by
  intro k hk
  rw [Std.HashMap.contains_insert]
  refine ⟨?_, ?_⟩
  · simp only [Bool.or_eq_true, beq_iff_eq]
    right; exact (hold k hk).1
  · show (inDegree.insert v (inDegree[v]! - 1))[k]! ≤ 0
    rw [Std.HashMap.getElem!_insert]
    by_cases hkv : (v == k) = true
    · simp [hkv]
      have heq : v = k := eq_of_beq hkv
      subst heq
      have h1 : inDegree.get! v ≤ 0 := (hold v hk).2
      have h2 : inDegree.get! v = inDegree[v]! := rfl
      omega
    · simp [hkv]; exact (hold k hk).2

/-- Establishment of `∀ v ∈ adjacency[id]!, nodeIdSet.contains v`
    when `adjacency.contains id` and the outer adjacency invariant holds. -/
theorem neighbors_in_nodeIdSet
    (adjacency : Std.HashMap String (Array String))
    (nodeIdSet : Std.HashSet String) (id : String)
    (hid : adjacency.contains id = true)
    (hold : ∀ k : String, adjacency.contains k = true →
            ∀ v : String, (adjacency.get! k).contains v = true → nodeIdSet.contains v = true) :
    ∀ v : String, adjacency[id]!.contains v = true → nodeIdSet.contains v = true := by
  intro v hv
  exact hold id hid v hv

/-- Phase-1 emptiness invariants: after inserting `id ↦ #[]`,
    every keyed array remains `#[]`. -/
theorem adjacency_emptyArrays_preserved
    (m : Std.HashMap String (Array String)) (id : String)
    (hold : ∀ k : String, m.contains k = true → m.get! k = #[]) :
    ∀ k : String, (m.insert id #[]).contains k = true → (m.insert id #[]).get! k = #[] := by
  intro k hk
  show (m.insert id #[])[k]! = #[]
  rw [Std.HashMap.getElem!_insert]
  rw [Std.HashMap.contains_insert] at hk
  by_cases hkeq : (id == k) = true
  · simp [hkeq]
  · simp [hkeq] at hk
    simp [hkeq]
    show m[k]! = _
    have := hold k hk
    show m.get! k = _
    exact this

@[grind →]
theorem adj_invariant_preserved
    (adjacency : Std.HashMap String (Array String))
    (nodeIdSet : Std.HashSet String)
    (id dep : String)
    (hid : nodeIdSet.contains id = true)
    (hdep : adjacency.contains dep = true)
    (hold : ∀ k : String, adjacency.contains k = true →
            ∀ v : String, (adjacency.get! k).contains v = true → nodeIdSet.contains v = true) :
    ∀ k : String,
      (adjacency.insert dep (adjacency[dep]! ++ #[id])).contains k = true →
      ∀ v : String,
        ((adjacency.insert dep (adjacency[dep]! ++ #[id])).get! k).contains v = true →
        nodeIdSet.contains v = true := by
  intro k hk v hv
  have hv' : ((adjacency.insert dep (adjacency.get! dep ++ #[id]))[k]!).contains v = true := hv
  rw [Std.HashMap.contains_insert] at hk
  rw [Std.HashMap.getElem!_insert] at hv'
  by_cases hkd : (dep == k) = true
  · simp [hkd, Array.mem_push] at hv'
    have hkd' : dep = k := eq_of_beq hkd
    subst hkd'
    rcases hv' with h | h
    · exact hold dep hdep v (Array.contains_iff.mpr h)
    · subst h; exact hid
  · simp [hkd] at hv'
    have hk' : adjacency.contains k = true := by simp [hkd] at hk; exact hk
    exact hold k hk' v (Array.contains_iff.mpr hv')

section TopoProof
set_option loom.solver "custom"
set_option hygiene false in
macro_rules
| `(tactic|loom_solver) => `(tactic| first
  | (strip_withname; grind (splits := 30))
  | (strip_withname; omega)
  -- Specifically discharge the adjacency-preservation VC
  | (strip_withname; apply adj_invariant_preserved <;> assumption)
  -- Preservation by helper lemmas
  | (strip_withname; apply contains_invariant_preserved_int <;> assumption)
  | (strip_withname; apply hashset_contains_invariant_preserved <;> assumption)
  | (strip_withname; apply adjacency_emptyArrays_preserved <;> assumption)
  | (strip_withname; apply enqueued_witness_preserved <;> assumption)
  | (strip_withname; apply enqueued_witness_bound_widen <;> assumption)
  -- Distinctness assertion: nodeIds[i] not yet enqueued
  | (strip_withname; apply not_enqueued_of_distinct <;> assumption)
  -- Size bound: enqueued.insert v ≤ nodeIdSet.size when v is "new"
  | (strip_withname
     apply Nat.le_trans
     · apply hashset_subset_insert_size <;> assumption
     · assumption)
  -- Joint insert preservation for invariant_41
  | (strip_withname
     apply joint_insert_preserves_inDegree_le_zero <;> (first | assumption | omega))
  | (strip_withname
     apply inDegree_insert_preserves_decrement <;> assumption)
  -- Establishment of inner-loop neighbor invariant
  | (strip_withname
     apply neighbors_in_nodeIdSet <;> assumption)
  | (strip_withname;
     simp only [Array.size_push, Std.HashSet.size_insert];
     (try (generalize Std.HashSet.size _ = _es at *));
     split <;> omega)
  | (strip_withname; omega))

set_option maxHeartbeats 16000000 in
prove_correct topologicalSort by
  loom_solve!

end TopoProof
