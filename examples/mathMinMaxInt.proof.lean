import «mathMinMaxInt.def»

set_option velvet.semantics.termination "total"

prove_correct singleValue by
  velvet_vcgen [singleValue] with finish [Pure.singleValue]

prove_correct highestInteger by
  velvet_vcgen [highestInteger] with finish [Pure.highestInteger]

prove_correct lowestNatural by
  velvet_vcgen [lowestNatural] with finish [Pure.lowestNatural]

prove_correct lowestMixed by
  velvet_vcgen [lowestMixed] with finish [Pure.lowestMixed]

prove_correct highestInArray by
  velvet_vcgen [highestInArray] with finish

prove_correct lowestInArray by
  velvet_vcgen [lowestInArray] with finish

prove_correct lowestOrZero by
  velvet_vcgen [lowestOrZero] with (expose_names; try finish)
  · have bounds := (minMax_bounds_iff_mem _ (fun x => a ≤ x)).mp h.1
    simpa using bounds 0 (by simp)
  · have bounds := (minMax_bounds_iff_mem _ (fun x => a ≤ x)).mp h.1
    apply (minMax_bounds_iff_mem _ (fun x => a ≤ x)).mpr
    intro x hx
    exact bounds x (by simp [hx])

prove_correct highestMixedArrays by
  velvet_vcgen [highestMixedArrays] with (expose_names; try finish)
  · have bounds := (minMax_bounds_iff_mem _ (fun x => x ≤ a)).mp h.1
    apply (minMax_bounds_iff_mem _ (fun (x : Nat) => (x : Int) ≤ a)).mpr
    intro x hx
    exact bounds (Int.ofNat x) (Array.mem_append.mpr (Or.inl (Array.mem_map.mpr ⟨x, hx, rfl⟩)))
  · have bounds := (minMax_bounds_iff_mem _ (fun x => x ≤ a)).mp h.1
    apply (minMax_bounds_iff_mem _ (fun x => x ≤ a)).mpr
    intro x hx
    exact bounds x (Array.mem_append.mpr (Or.inr hx))

prove_correct highestWithNatural by
  velvet_vcgen [highestWithNatural] with (expose_names; try finish)
  · have bounds := (minMax_bounds_iff_mem _ (fun x => x ≤ a)).mp h.1
    exact bounds (Int.ofNat n) (by simp)
  · have bounds := (minMax_bounds_iff_mem _ (fun x => x ≤ a)).mp h.1
    apply (minMax_bounds_iff_mem _ (fun x => x ≤ a)).mpr
    intro x hx
    exact bounds x (Array.mem_append.mpr (Or.inl hx))

prove_correct arrayRange by
  velvet_vcgen [arrayRange] with finish

prove_correct guardedHighest by
  velvet_vcgen [guardedHighest] with finish

-- An unchecked empty spread fails even through a source-level caller.
example : highestInArray #[] = none := rfl
example : lowestInArray #[] = none := rfl
example : arrayRange #[] = none := rfl
example : guardedHighest #[] = some 0 := rfl

-- Even a vacuous postcondition cannot verify an empty spread as total.
example : ¬ Std.Internal.Do.Triple (arrayRange #[]) True (fun _ => True) False := by
  intro h
  simpa [arrayRange, highestInArray, LemmaScript.maxOfArray,
    Std.Internal.Do.WP.wp, Std.Internal.Do.WP.wpTrans] using h.le_wp trivial
