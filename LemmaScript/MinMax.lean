import Velvet
import Init.Data.List.MinMax

/-! Integer spread extrema. Empty input fails, so callers must establish
nonemptiness before these operations can satisfy total correctness. -/

namespace LemmaScript

open Std.Internal.Do

def maxOfArray (xs : Array Int) : Option Int := xs.toList.max?

def minOfArray (xs : Array Int) : Option Int := xs.toList.min?

@[spec]
theorem maxOfArray_spec (xs : Array Int) :
    Triple (maxOfArray xs) (0 < xs.size)
      (fun result => (∀ i, i < xs.size → xs[i]! ≤ result) ∧
        ∃ i, i < xs.size ∧ xs[i]! = result) False := by
  constructor
  intro h
  have hn : xs.toList ≠ [] := by
    intro he
    have : xs.size = 0 := by
      simpa only [Array.length_toList, List.length_nil] using congrArg List.length he
    omega
  obtain ⟨result, hr⟩ := Option.isSome_iff_exists.mp (List.isSome_max?_of_ne_nil hn)
  have facts := List.max?_eq_some_iff.mp hr
  simp only [maxOfArray, hr, WP.wp, WP.wpTrans]
  constructor
  · intro i hi
    apply facts.2
    exact Array.mem_toList_iff.mpr (by simpa only [getElem!_pos xs i hi] using Array.getElem_mem hi)
  · obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp facts.1)
    exact ⟨i, hi, by simpa [getElem!_pos xs i hi] using he⟩

@[spec]
theorem minOfArray_spec (xs : Array Int) :
    Triple (minOfArray xs) (0 < xs.size)
      (fun result => (∀ i, i < xs.size → result ≤ xs[i]!) ∧
        ∃ i, i < xs.size ∧ xs[i]! = result) False := by
  constructor
  intro h
  have hn : xs.toList ≠ [] := by
    intro he
    have : xs.size = 0 := by
      simpa only [Array.length_toList, List.length_nil] using congrArg List.length he
    omega
  obtain ⟨result, hr⟩ := Option.isSome_iff_exists.mp (List.isSome_min?_of_ne_nil hn)
  have facts := List.min?_eq_some_iff.mp hr
  simp only [minOfArray, hr, WP.wp, WP.wpTrans]
  constructor
  · intro i hi
    apply facts.2
    exact Array.mem_toList_iff.mpr (by simpa only [getElem!_pos xs i hi] using Array.getElem_mem hi)
  · obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp facts.1)
    exact ⟨i, hi, by simpa [getElem!_pos xs i hi] using he⟩

end LemmaScript
