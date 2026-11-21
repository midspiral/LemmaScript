import «mathMinMaxInt.types»

-- Convert indexed bounds to membership so append and map simplify uniformly.
theorem minMax_bounds_iff_mem {α : Type} [Inhabited α] (xs : Array α) (p : α → Prop) :
    (∀ i, i < xs.size → p xs[i]!) ↔ ∀ x ∈ xs, p x := by
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
    simpa only [getElem!_pos xs i hi] using h i hi
  · intro h i hi
    simpa only [getElem!_pos xs i hi] using h xs[i] (Array.getElem_mem hi)
