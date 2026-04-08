import LemmaScript

@[grind, loomAbstractionSimp]
def allDistinct (s : Array String) (n : Nat) : Prop :=
  if h : n = 0 then True
  else if h2 : n ≤ s.size then
    s[n - 1]! ∉ (s.toList.take (n - 1)) ∧ allDistinct s (n - 1)
  else True
