import Velvet

namespace LemmaScript

open Std.Internal.Do

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

/-- Bridge `Std.HashMap.get?` (returned by `map.get`) with `contains` and `getElem!`
    so `grind` connects narrowed `optionValue (m.get? k)` bindings to map invariants. -/
@[grind →]
theorem hashmap_get?_eq_some_contains {α β : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    {m : Std.HashMap α β} {k : α} {v : β} (h : m.get? k = some v) :
    m.contains k = true := by
  have h1 : m[k]? = some v := h
  rw [Std.HashMap.contains_iff_mem, Std.HashMap.mem_iff_isSome_getElem?]
  simp [h1]

@[grind →]
theorem hashmap_get?_eq_some_getElem! {α β : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {m : Std.HashMap α β} {k : α} {v : β} (h : m.get? k = some v) :
    m[k]! = v := by
  have h1 : m[k]? = some v := h
  grind

@[grind →]
theorem hashmap_get?_eq_some_get! {α β : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {m : Std.HashMap α β} {k : α} {v : β} (h : m.get? k = some v) :
    m.get! k = v :=
  hashmap_get?_eq_some_getElem! h

end LemmaScript
