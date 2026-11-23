import Velvet

namespace LemmaScript

open Std.Internal.Do

/-- Reading a narrowed optional must prove that its payload exists. -/
def optionValue (value : Option α) : Option α := value

@[spec]
theorem optionValue_spec (value : Option α) :
    Triple (optionValue value) (∃ result, value = some result)
      (fun result => value = some result) False := by
  constructor
  rintro ⟨result, rfl⟩
  simp [optionValue, WP.wp, WP.wpTrans]

end LemmaScript
