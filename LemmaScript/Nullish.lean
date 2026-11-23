import Velvet

namespace LemmaScript

open Std.Internal.Do

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

@[simp] def Nullish.isUndefined : Nullish α → Bool
  | .Undefined => true
  | .Null => false
  | .Value _ => false

@[simp] def Nullish.get : (x : Nullish α) → x.isValue = true → α
  | .Value value, _ => value

@[simp, grind =] theorem Nullish.value_get {x : Nullish α} (h : x.isValue = true) :
    Nullish.Value (x.get h) = x := by
  cases x with
  | Undefined => cases h
  | Null => cases h
  | Value _ => rfl

@[simp] def Nullish.excludeUndefined : (x : Nullish α) → x.isUndefined = false → Option α
  | .Value v, _ => some v
  | .Null, _ => none

@[simp] def Nullish.excludeNull : (x : Nullish α) → x.isNull = false → Option α
  | .Value v, _ => some v
  | .Undefined, _ => none

@[simp, grind =] theorem Nullish.isSome_excludeUndefined {x : Nullish α} (h : x.isUndefined = false) :
    (x.excludeUndefined h).isSome = x.isValue := by
  cases x with | Undefined => cases h | Null => rfl | Value _ => rfl

@[simp, grind =] theorem Nullish.isSome_excludeNull {x : Nullish α} (h : x.isNull = false) :
    (x.excludeNull h).isSome = x.isValue := by
  cases x with | Undefined => rfl | Null => cases h | Value _ => rfl

@[simp, grind =] theorem Nullish.excludeUndefined_eq_some {x : Nullish α}
    (h1 : x.isUndefined = false) (h2 : x.isValue = true) :
    x.excludeUndefined h1 = some (x.get h2) := by
  cases x with | Undefined => cases h1 | Null => cases h2 | Value _ => rfl

@[simp, grind =] theorem Nullish.excludeNull_eq_some {x : Nullish α}
    (h1 : x.isNull = false) (h2 : x.isValue = true) :
    x.excludeNull h1 = some (x.get h2) := by
  cases x with | Undefined => cases h2 | Null => cases h1 | Value _ => rfl

@[simp] def Nullish.ofOptionUndefined : Option α → Nullish α
  | some v => .Value v
  | none => .Undefined

@[simp] def Nullish.ofOptionNull : Option α → Nullish α
  | some v => .Value v
  | none => .Null

@[grind] theorem Nullish.trichotomy (x : Nullish α) :
    (x.isUndefined = true ∧ x.isNull = false ∧ x.isValue = false) ∨
    (x.isUndefined = false ∧ x.isNull = true ∧ x.isValue = false) ∨
    (x.isUndefined = false ∧ x.isNull = false ∧ x.isValue = true) := by
  cases x <;> simp

@[grind =] theorem Nullish.isValue_Value (v : α) : (Nullish.Value v).isValue = true := rfl
@[grind =] theorem Nullish.isNull_Value (v : α) : (Nullish.Value v).isNull = false := rfl
@[grind =] theorem Nullish.isUndefined_Value (v : α) : (Nullish.Value v).isUndefined = false := rfl
@[grind =] theorem Nullish.isValue_Null : (Nullish.Null : Nullish α).isValue = false := rfl
@[grind =] theorem Nullish.isNull_Null : (Nullish.Null : Nullish α).isNull = true := rfl
@[grind =] theorem Nullish.isUndefined_Null : (Nullish.Null : Nullish α).isUndefined = false := rfl
@[grind =] theorem Nullish.isValue_Undefined : (Nullish.Undefined : Nullish α).isValue = false := rfl
@[grind =] theorem Nullish.isNull_Undefined : (Nullish.Undefined : Nullish α).isNull = false := rfl
@[grind =] theorem Nullish.isUndefined_Undefined : (Nullish.Undefined : Nullish α).isUndefined = true := rfl

/-- Velvet checked projections for `Nullish`. -/
def nullishValue (x : Nullish α) : Option α :=
  match x with
  | .Value v => some v
  | .Null => none
  | .Undefined => none

@[spec]
theorem nullishValue_spec (x : Nullish α) :
    Triple (nullishValue x) (x.isValue = true)
      (fun v => x = .Value v) False := by
  constructor
  intro h
  cases x with
  | Undefined => cases h
  | Null => cases h
  | Value v => simp [nullishValue, WP.wp, WP.wpTrans]

def nullishExcludeUndefined (x : Nullish α) : Option (Option α) :=
  match x with
  | .Value v => some (some v)
  | .Null => some none
  | .Undefined => none

@[spec]
theorem nullishExcludeUndefined_spec (x : Nullish α) :
    Triple (nullishExcludeUndefined x) (x.isUndefined = false)
      (fun r => Nullish.ofOptionNull r = x) False := by
  constructor
  intro h
  cases x with
  | Undefined => cases h
  | Null => simp [nullishExcludeUndefined, WP.wp, WP.wpTrans]
  | Value v => simp [nullishExcludeUndefined, WP.wp, WP.wpTrans]

def nullishExcludeNull (x : Nullish α) : Option (Option α) :=
  match x with
  | .Value v => some (some v)
  | .Undefined => some none
  | .Null => none

@[spec]
theorem nullishExcludeNull_spec (x : Nullish α) :
    Triple (nullishExcludeNull x) (x.isNull = false)
      (fun r => Nullish.ofOptionUndefined r = x) False := by
  constructor
  intro h
  cases x with
  | Null => cases h
  | Undefined => simp [nullishExcludeNull, WP.wp, WP.wpTrans]
  | Value v => simp [nullishExcludeNull, WP.wp, WP.wpTrans]

end LemmaScript
