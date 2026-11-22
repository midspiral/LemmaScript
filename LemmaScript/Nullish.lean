namespace LemmaScript

/-- The three distinct cases of TypeScript's `T | null | undefined`. -/
inductive Nullish (α : Type u) where
  | Undefined
  | Null
  | Value (value : α)
deriving Repr, DecidableEq, Inhabited

@[simp] def Nullish.isValue : Nullish α → Bool
  | .Undefined => false
  | .Null => false
  | .Value _ => true

@[simp] def Nullish.isNull : Nullish α → Bool
  | .Undefined => false
  | .Null => true
  | .Value _ => false

/-- Payload projection used under an `isValue` guard in generated methods. -/
@[simp] def Nullish.get : (x : Nullish α) → x.isValue = true → α
  | .Value value, _ => value

@[simp, grind =] theorem Nullish.value_get {x : Nullish α} (h : x.isValue = true) :
    Nullish.Value (x.get h) = x := by
  cases x with
  | Undefined => cases h
  | Null => cases h
  | Value _ => rfl

end LemmaScript
