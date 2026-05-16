import LemmaScript

@[grind, loomAbstractionSimp]
def allDistinct (s : Array String) (n : Nat) : Prop :=
  if h : n = 0 then True
  else if h2 : n ≤ s.size then
    s[n - 1]! ∉ (s.toList.take (n - 1)) ∧ allDistinct s (n - 1)
  else True

-- ── Helper lemmas ─────────────────────────────────────────────

/-- Subset + a witness of slack gives strict insert-size bound on Std.HashSet.
    Counterpart of Dafny's `subset_size + distinct_seq_in_set_bound` combo
    used at lines 188–191 / 221–222 of `toposort.dfy`.
    Bridge through `toList`: NoDup pigeonhole on `x :: a.toList ⊆ b.toList`. -/
theorem hashset_subset_insert_size {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (a b : Std.HashSet α) (x : α)
    (hsub : ∀ y, a.contains y = true → b.contains y = true)
    (hxb : b.contains x = true) (hxa : ¬ a.contains x = true) :
    (a.insert x).size ≤ b.size := by
  have ha_nodup : a.toList.Nodup := by
    have hpw := Std.HashSet.distinct_toList (m := a)
    exact List.Pairwise.imp (fun {a b} h => fun heq => by simp [heq] at h) hpw
  have hxa' : x ∉ a.toList := by
    intro hmem
    rw [Std.HashSet.mem_toList] at hmem
    exact hxa (Std.HashSet.contains_iff_mem.mpr hmem)
  have hcons_nodup : (x :: a.toList).Nodup := List.nodup_cons.mpr ⟨hxa', ha_nodup⟩
  have hsub' : (x :: a.toList) ⊆ b.toList := by
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hya
    · exact (Std.HashSet.mem_toList).mpr (Std.HashSet.contains_iff_mem.mp hxb)
    · rw [Std.HashSet.mem_toList] at hya
      exact (Std.HashSet.mem_toList).mpr
        (Std.HashSet.contains_iff_mem.mp (hsub _ (Std.HashSet.contains_iff_mem.mpr hya)))
  have hlen : (x :: a.toList).length ≤ b.toList.length :=
    (List.Nodup.subperm hcons_nodup hsub').length_le
  have h1 : (a.insert x).size = a.size + 1 := by
    rw [Std.HashSet.size_insert]
    simp [show ¬ x ∈ a from fun h => hxa (Std.HashSet.contains_iff_mem.mpr h)]
  have h2 : a.size = a.toList.length := (Std.HashSet.length_toList).symm
  have h3 : b.size = b.toList.length := (Std.HashSet.length_toList).symm
  simp only [List.length_cons] at hlen
  omega
