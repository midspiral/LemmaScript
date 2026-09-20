import Velvet

/-! Specifications for the monadic array operations emitted by LemmaScript.
Generated methods use `Option`: total correctness requires every invoked callback
to succeed. Mapping also preserves the input length.
-/

open Std.Internal.Do

private theorem listMapM_some (f : α → Option β) (xs : List α)
    (hf : ∀ a ∈ xs, ∃ b, f a = some b) :
    ∃ ys, xs.mapM f = some ys ∧ ys.length = xs.length := by
  induction xs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons a xs ih =>
    obtain ⟨b, hb⟩ := hf a (by simp)
    obtain ⟨bs, hbs, hlen⟩ := ih (fun x hx => hf x (by simp [hx]))
    exact ⟨b :: bs, by simp [List.mapM_cons, hb, hbs], by simp [hlen]⟩

@[spec]
theorem LemmaScript.arrayMapM (f : α → Option β) (xs : Array α) (pre : Prop)
    (hf : ∀ a ∈ xs, Triple (f a) pre (fun _ => True) False) :
    Triple (xs.mapM f) pre (fun ys => ys.size = xs.size) False := by
  constructor
  intro hp
  have hh : ∀ a ∈ xs.toList, ∃ b, f a = some b := by
    intro a ha
    have h := (hf a (by simpa using ha)).le_wp hp
    cases he : f a with
    | none => simp [WP.wp, WP.wpTrans, he] at h
    | some b => exact ⟨b, rfl⟩
  obtain ⟨bs, hbs, hlen⟩ := listMapM_some f xs.toList hh
  simpa [Array.mapM_eq_mapM_toList, hbs, WP.wp, WP.wpTrans] using hlen

private theorem callback_some (f : α → Option β) (xs : Array α) (pre : Prop)
    (hf : ∀ a ∈ xs, Triple (f a) pre (fun _ => True) False) (hp : pre) :
    ∀ a ∈ xs.toList, ∃ b, f a = some b := by
  intro a ha
  have h := (hf a (by simpa using ha)).le_wp hp
  cases he : f a with
  | none => simp [WP.wp, WP.wpTrans, he] at h
  | some b => exact ⟨b, rfl⟩

private theorem listFilterAuxM_some (f : α → Option Bool) (xs : List α)
    (hf : ∀ a ∈ xs, ∃ b, f a = some b) :
    ∀ acc, ∃ ys, List.filterAuxM f xs acc = some ys := by
  induction xs with
  | nil => intro acc; exact ⟨acc, rfl⟩
  | cons a xs ih =>
    intro acc
    obtain ⟨b, hb⟩ := hf a (by simp)
    obtain ⟨ys, hys⟩ := ih (fun x hx => hf x (by simp [hx])) (cond b (a :: acc) acc)
    exact ⟨ys, by simpa [List.filterAuxM, hb] using hys⟩

private theorem listFilterM_some (f : α → Option Bool) (xs : List α)
    (hf : ∀ a ∈ xs, ∃ b, f a = some b) : ∃ ys, xs.filterM f = some ys := by
  obtain ⟨ys, hys⟩ := listFilterAuxM_some f xs hf []
  exact ⟨ys.reverse, by simp [List.filterM, hys]⟩

private theorem listAllM_some (f : α → Option Bool) (xs : List α)
    (hf : ∀ a ∈ xs, ∃ b, f a = some b) : ∃ b, xs.allM f = some b := by
  induction xs with
  | nil => exact ⟨true, rfl⟩
  | cons a xs ih =>
    obtain ⟨b, hb⟩ := hf a (by simp)
    obtain ⟨c, hc⟩ := ih (fun x hx => hf x (by simp [hx]))
    cases b
    · exact ⟨false, by simp [List.allM, hb]⟩
    · exact ⟨c, by simp [List.allM, hb, hc]⟩

private theorem listAnyM_some (f : α → Option Bool) (xs : List α)
    (hf : ∀ a ∈ xs, ∃ b, f a = some b) : ∃ b, xs.anyM f = some b := by
  induction xs with
  | nil => exact ⟨false, rfl⟩
  | cons a xs ih =>
    obtain ⟨b, hb⟩ := hf a (by simp)
    obtain ⟨c, hc⟩ := ih (fun x hx => hf x (by simp [hx]))
    cases b
    · exact ⟨c, by simp [List.anyM, hb, hc]⟩
    · exact ⟨true, by simp [List.anyM, hb]⟩

@[spec]
theorem LemmaScript.arrayFilterM (f : α → Option Bool) (xs : Array α) (pre : Prop)
    (hf : ∀ a ∈ xs, Triple (f a) pre (fun _ => True) False) :
    Triple (xs.filterM f) pre (fun _ => True) False := by
  constructor
  intro hp
  obtain ⟨ys, hys⟩ := listFilterM_some f xs.toList (callback_some f xs pre hf hp)
  have he : xs.filterM f = List.toArray <$> (xs.toList.filterM f) := by
    simpa using (List.filterM_toArray (l := xs.toList) (p := f))
  simp [he, hys, WP.wp, WP.wpTrans]

@[spec]
theorem LemmaScript.arrayAllM (f : α → Option Bool) (xs : Array α) (pre : Prop)
    (hf : ∀ a ∈ xs, Triple (f a) pre (fun _ => True) False) :
    Triple (xs.allM f) pre (fun _ => True) False := by
  constructor
  intro hp
  obtain ⟨b, hb⟩ := listAllM_some f xs.toList (callback_some f xs pre hf hp)
  rw [← Array.allM_toList]
  simp [hb, WP.wp, WP.wpTrans]

@[spec]
theorem LemmaScript.arrayAnyM (f : α → Option Bool) (xs : Array α) (pre : Prop)
    (hf : ∀ a ∈ xs, Triple (f a) pre (fun _ => True) False) :
    Triple (xs.anyM f) pre (fun _ => True) False := by
  constructor
  intro hp
  obtain ⟨b, hb⟩ := listAnyM_some f xs.toList (callback_some f xs pre hf hp)
  rw [← Array.anyM_toList]
  simp [hb, WP.wp, WP.wpTrans]
