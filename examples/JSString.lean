/-
  JSString — Lean definitions matching JavaScript string semantics (ASCII).
  Used by LemmaScript-generated code.
-/

namespace JSString

/-- JS `String.indexOf(sub)`: character index of first occurrence, or -1. -/
def indexOf (s : String) (sub : String) : Int :=
  go s.data sub.data 0
where
  go : List Char → List Char → Nat → Int
  | [], _, _ => -1
  | c :: cs, sub, idx =>
    if sub.isPrefixOf (c :: cs) then (idx : Int)
    else go cs sub (idx + 1)

/-- JS `String.slice(start, end)`: substring from character index `start`
    up to (but not including) `end`. -/
def slice (s : String) (start stop : Int) : String :=
  ⟨(s.data.drop start.toNat).take (stop.toNat - start.toNat)⟩

end JSString
