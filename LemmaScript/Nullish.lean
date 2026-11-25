/-
  Nullish — three-case Lean datatype for TypeScript `T | null | undefined`.
  Preserves `null ≠ undefined` while keeping `Option` for single-sentinel
  `T | undefined` and `T | null` types.
-/

inductive Nullish (α : Type) where
  | undefined : Nullish α
  | null : Nullish α
  | value : α → Nullish α
  deriving Repr, BEq, DecidableEq

instance {α : Type} : Inhabited (Nullish α) := ⟨.undefined⟩

namespace Nullish

def isValue {α : Type} : Nullish α → Bool
  | .value _ => true
  | _ => false

def isUndefined {α : Type} : Nullish α → Bool
  | .undefined => true
  | _ => false

def isNull {α : Type} : Nullish α → Bool
  | .null => true
  | _ => false

def get {α : Type} : (x : Nullish α) → x.isValue = true → α
  | .value v, _ => v

@[grind =] theorem isValue_eq_true {α : Type} (x : Nullish α) :
    x.isValue = true ↔ ∃ v, x = .value v := by
  cases x <;> simp [isValue]

@[grind =] theorem isNull_eq_true {α : Type} (x : Nullish α) :
    x.isNull = true ↔ x = .null := by
  cases x <;> simp [isNull]

@[grind =] theorem isUndefined_eq_true {α : Type} (x : Nullish α) :
    x.isUndefined = true ↔ x = .undefined := by
  cases x <;> simp [isUndefined]

@[grind =] theorem isValue_of_ne {α : Type} (x : Nullish α) :
    x.isNull = false → x.isUndefined = false → x.isValue = true := by
  cases x <;> simp [isNull, isUndefined, isValue]

end Nullish
