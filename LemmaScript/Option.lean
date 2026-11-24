import Velvet

namespace LemmaScript

open Std.Internal.Do

-- Presence tests and constructor matches describe the same storage value.
attribute [grind =] Option.not_isSome_iff_eq_none
attribute [grind →] Option.eq_some_of_isSome

/-- Reading a narrowed optional must prove that its payload exists. -/
def optionValue (value : Option α) : Option α := value

@[spec]
theorem optionValue_spec (value : Option α) :
    Triple (optionValue value) (value.isSome = true)
      (fun result => value = some result) False := by
  constructor
  intro h
  cases value with
  | none => cases h
  | some v => simp [optionValue, WP.wp, WP.wpTrans]

/-- Connect a checked lookup result to the map operations used in invariants. -/
@[grind →]
theorem hashmap_get?_eq_some {α β : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {m : Std.HashMap α β} {k : α} {v : β} (h : m.get? k = some v) :
    m.contains k = true ∧ m.get! k = v := by
  have lookup : m[k]? = some v := h
  constructor
  · rw [Std.HashMap.contains_iff_mem, Std.HashMap.mem_iff_isSome_getElem?]
    simp [lookup]
  · show m[k]! = v
    grind

end LemmaScript
