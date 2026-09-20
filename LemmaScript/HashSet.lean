/-
  Simp lemmas and tactics for Std.HashSet operations in LemmaScript proofs.
-/
import Velvet

@[grind, simp]
theorem hashset_insert_size_le [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {s : Std.HashSet α} {k : α} :
    (s.insert k).size ≤ s.size + 1 :=
  Std.HashSet.size_insert_le

@[grind, simp]
theorem hashset_size_le_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {s : Std.HashSet α} {k : α} :
    s.size ≤ (s.insert k).size :=
  Std.HashSet.size_le_size_insert

@[grind, simp]
theorem array_contains_getElem! [BEq α] [LawfulBEq α] [Inhabited α]
    (arr : Array α) (i : Nat) (h : i < arr.size) : arr.contains arr[i]! = true := by
  rw [getElem!_pos arr i h, Array.contains_iff]
  exact Array.getElem_mem h
