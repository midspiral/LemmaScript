import Velvet.Syntax
import Velvet.Std

@[grind, loomAbstractionSimp]
def sumTo (arr : Array Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumTo arr n + if n < arr.size then arr[n]! else 0

@[grind, loomAbstractionSimp]
theorem sumTo_step (arr : Array Int) (i : Int) (hi : 0 ≤ i) (hlt : i.toNat < arr.size) :
    sumTo arr (i + 1).toNat = sumTo arr i.toNat + arr[i.toNat]! := by
  have : (i + 1).toNat = i.toNat + 1 := by omega
  simp [this, sumTo, hlt]
