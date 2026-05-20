import «majority.types»

@[grind, loomAbstractionSimp]
theorem occOf_zero (arr : Array Int) (x : Int) :
    Pure.occOf arr x 0 = 0 := by
  unfold Pure.occOf
  simp

@[grind, loomAbstractionSimp]
theorem occOf_step (arr : Array Int) (x : Int) (n : Nat) :
    Pure.occOf arr x (n + 1) = Pure.occOf arr x n + (if arr[n]! = x then 1 else 0) := by
  conv_lhs => unfold Pure.occOf
  simp
