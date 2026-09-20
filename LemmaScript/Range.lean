import Velvet

/-- Expose the sequence of a zero-based range to Velvet's range proof rules. -/
@[grind =]
theorem LemmaScript.range_toList (n : Nat) : ForIn.toList [:n] = List.range n := by
  simp [Std.Internal.ForIn.toList_range, Std.Legacy.Range.size, List.range_eq_range']
