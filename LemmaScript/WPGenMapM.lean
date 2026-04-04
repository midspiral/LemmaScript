/-
  WPGen rule for Array.mapM — allows loom_solve to handle monadic map operations.

  Proof strategy:
  1. Define `wpListMapM_wp`: a recursive WP for List.mapM using `wp` directly
     (not WPGen.get), so monotonicity is free via `wp_cons`.
  2. Prove `wpListMapM_wp_le`: soundness w.r.t. the true wp of List.mapM.
  3. Prove `wpListMapM_wp_of_forall`: if every callback's wp-precondition holds,
     then wpListMapM_wp is satisfiable for any size-correct postcondition.
  4. Combine into `WPGen.arrayMapM` using Array.mapM_eq_mapM_toList, connecting
     WPGen.get to wp via WPGen.prop.
-/
import Velvet.Syntax
import Velvet.Std

universe u v

noncomputable def wpListMapM_wp
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {l : Type u} [CompleteBooleanAlgebra l] [MAlgOrdered m l]
    {α β : Type u} (f : α → m β) :
    (xs : List α) → Cont l (List β)
  | [] => fun post => post []
  | a :: xs => fun post => wp (f a) (fun b => wpListMapM_wp f xs (fun bs => post (b :: bs)))

theorem wpListMapM_wp_le
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {l : Type u} [CompleteBooleanAlgebra l] [MAlgOrdered m l]
    {α β : Type u} (f : α → m β) :
    ∀ (xs : List α) (post : List β → l),
    wpListMapM_wp f xs post ≤ wp (List.mapM f xs) post := by
  intro xs; induction xs with
  | nil => intro post; simp [wpListMapM_wp, List.mapM_nil, wp_pure]
  | cons a tl ih =>
    intro post; rw [List.mapM_cons]; simp only [wpListMapM_wp]; rw [wp_bind]
    apply wp_cons; intro b; rw [wp_bind]
    apply le_trans; exact ih _; apply wp_cons; intro bs; rw [wp_pure]

theorem wpListMapM_wp_of_forall
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MAlgOrdered m Prop]
    {α β : Type} (f : α → m β) (xs : List α)
    (h_pre : ∀ a, a ∈ xs → wp (f a) (fun _ => True))
    (post : List β → Prop) (h_post : ∀ bs, bs.length = xs.length → post bs) :
    wpListMapM_wp f xs post := by
  induction xs generalizing post with
  | nil => simp [wpListMapM_wp]; exact h_post [] rfl
  | cons a tl ih =>
    simp only [wpListMapM_wp]
    have htl : ∀ b, wpListMapM_wp f tl (fun bs => post (b :: bs)) :=
      fun b => ih (fun a' ha' => h_pre a' (List.mem_cons_of_mem _ ha'))
        _ (fun bs hlen => h_post (b :: bs) (by simp [hlen]))
    exact wp_cons (f a) _ _ (fun b _ => htl b) (h_pre a (List.mem_cons.mpr (Or.inl rfl)))

@[loomSpec, loomWpSimp]
noncomputable def WPGen.arrayMapM
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MAlgOrdered m Prop]
    {α β : Type} {f : α → m β} {arr : Array α}
    (wpgf : ∀ a, WPGen (f a)) :
    WPGen (arr.mapM f) where
  get := fun post =>
    (∀ i : Fin arr.size, (wpgf arr[i]).get (fun _ => True)) ∧
    (∀ result : Array β, result.size = arr.size → post result)
  prop := by
    intro post; intro ⟨h_pre, h_post⟩
    rw [Array.mapM_eq_mapM_toList, wp_map]
    have key : wpListMapM_wp f arr.toList (fun bs => post bs.toArray) := by
      apply wpListMapM_wp_of_forall
      · intro a ha
        obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp ha
        rw [← heq]
        exact (wpgf arr.toList[i]).prop _ (h_pre ⟨i, by rwa [Array.length_toList] at hi⟩)
      · intro bs hlen; apply h_post; simp [hlen]
    exact wpListMapM_wp_le f arr.toList _ key
