import Velvet.Syntax
import Velvet.Std

/-- An array is sorted iff elements are non-decreasing. -/
@[grind, loomAbstractionSimp]
def sorted (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!
