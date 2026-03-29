import Velvet.Syntax
import Velvet.Std

@[grind, loomAbstractionSimp]
def sorted (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!
