/-
  Simp lemmas for Std.HashSet.insert size reasoning.
  Makes omega work with HashSet size bounds in LemmaScript proofs.
-/
import Velvet.Syntax

@[loomAbstractionSimp, simp]
theorem hashset_insert_size_le [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {s : Std.HashSet α} {k : α} :
    (s.insert k).size ≤ s.size + 1 :=
  Std.HashSet.size_insert_le

@[loomAbstractionSimp, simp]
theorem hashset_size_le_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {s : Std.HashSet α} {k : α} :
    s.size ≤ (s.insert k).size :=
  Std.HashSet.size_le_size_insert
