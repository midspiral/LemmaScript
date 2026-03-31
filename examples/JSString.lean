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

private theorem go_bound (chars : List Char) (sub : List Char) (idx : Nat) :
    indexOf.go chars sub idx = -1 ∨
    (0 ≤ indexOf.go chars sub idx ∧ indexOf.go chars sub idx < ↑(idx + chars.length)) := by
  induction chars generalizing idx with
  | nil => simp [indexOf.go]
  | cons c cs ih =>
    simp only [indexOf.go]
    split
    · right; exact ⟨Int.natCast_nonneg idx, by simp [List.length_cons]; omega⟩
    · have := ih (idx + 1)
      simp [Nat.add_right_comm] at this
      exact this

theorem indexOf_lt_length (s : String) (sub : String) (h : indexOf s sub ≠ -1) :
    0 ≤ indexOf s sub ∧ indexOf s sub < ↑s.length := by
  unfold indexOf at *
  have := go_bound s.data sub.data 0
  simp [String.length] at this ⊢
  omega

end JSString
