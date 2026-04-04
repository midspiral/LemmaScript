/-
  WPGen rules for monadic Array HOFs: mapM, filterM, allM, anyM.

  Each rule follows the same pattern:
  1. Define a recursive WP over List using `wp` directly (not WPGen.get),
     so monotonicity comes free via `wp_cons`.
  2. Prove soundness w.r.t. the true wp of the List operation.
  3. Prove a "forall" helper: if every callback's wp-precondition holds,
     then the recursive WP is satisfiable.
  4. Combine into a WPGen rule for the Array operation, connecting
     WPGen.get to wp via WPGen.prop.
-/
import Velvet.Syntax
import Velvet.Std

universe u v

/-! ## Shared helper: array membership → callback wp-precondition -/

private theorem wpgf_pre_of_mem
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MAlgOrdered m Prop]
    {α β : Type} {f : α → m β} {arr : Array α}
    (wpgf : ∀ a, WPGen (f a))
    (h_pre : ∀ i : Fin arr.size, (wpgf arr[i]).get (fun _ => True))
    (a : α) (ha : a ∈ arr.toList) :
    wp (f a) (fun _ => True) := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp ha
  rw [← heq]
  exact (wpgf arr.toList[i]).prop _ (h_pre ⟨i, by rwa [Array.length_toList] at hi⟩)

/-! ## mapM -/

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
    exact wpListMapM_wp_le f arr.toList _
      (wpListMapM_wp_of_forall f arr.toList (wpgf_pre_of_mem wpgf h_pre)
        _ (fun bs hlen => h_post bs.toArray (by simp [hlen])))

/-! ## filterM -/

private theorem array_filterM_eq
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    {α : Type} (f : α → m Bool) (arr : Array α) :
    arr.filterM f = List.toArray <$> (arr.toList.filterM f) := by
  conv_lhs => rw [show arr = arr.toList.toArray from by simp]
  exact List.filterM_toArray

private theorem wp_filterAuxM_post
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MAlgOrdered m Prop]
    {α : Type} (f : α → m Bool)
    {post : List α → Prop} (h_post : ∀ result, post result) :
    ∀ (xs : List α) (acc : List α),
    (∀ a, a ∈ xs → wp (f a) (fun _ => True)) →
    wp (List.filterAuxM f xs acc) post := by
  intro xs; induction xs with
  | nil => intro acc _; simp [List.filterAuxM, wp_bind, wp_pure]; exact h_post _
  | cons a tl ih =>
    intro acc h_pre
    simp only [List.filterAuxM]; rw [wp_bind]
    apply wp_cons (f a) _ _ _ (h_pre a (List.mem_cons.mpr (Or.inl rfl)))
    intro b _; cases b <;> simp <;>
      exact ih _ (fun a' ha' => h_pre a' (List.mem_cons_of_mem _ ha'))

@[loomSpec, loomWpSimp]
noncomputable def WPGen.arrayFilterM
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MAlgOrdered m Prop]
    {α : Type} {f : α → m Bool} {arr : Array α}
    (wpgf : ∀ a, WPGen (f a)) :
    WPGen (arr.filterM f) where
  get := fun post =>
    (∀ i : Fin arr.size, (wpgf arr[i]).get (fun _ => True)) ∧
    (∀ result : Array α, post result)
  prop := by
    intro post; intro ⟨h_pre, h_post⟩
    rw [array_filterM_eq, wp_map]
    simp only [List.filterM]; rw [wp_bind]; simp only [wp_pure]
    exact wp_filterAuxM_post f (fun r => h_post r.reverse.toArray) arr.toList []
      (wpgf_pre_of_mem wpgf h_pre)

/-! ## allM -/

noncomputable def wpListAllM_wp
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MAlgOrdered m Prop]
    {α : Type} (f : α → m Bool) :
    (xs : List α) → (Bool → Prop) → Prop
  | [], post => post true
  | a :: xs, post => wp (f a) (fun b =>
      if b then wpListAllM_wp f xs post else post false)

theorem wpListAllM_wp_le
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MAlgOrdered m Prop]
    {α : Type} (f : α → m Bool) :
    ∀ (xs : List α) (post : Bool → Prop),
    wpListAllM_wp f xs post ≤ wp (xs.allM f) post := by
  intro xs; induction xs with
  | nil => intro post; simp [wpListAllM_wp, List.allM, wp_pure]
  | cons a tl ih =>
    intro post; simp only [wpListAllM_wp, List.allM]; rw [wp_bind]
    apply wp_cons; intro b; cases b
    · simp; rw [wp_pure]; exact id
    · simp; exact ih _

theorem wpListAllM_wp_of_forall
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MAlgOrdered m Prop]
    {α : Type} (f : α → m Bool) (xs : List α)
    (h_pre : ∀ a, a ∈ xs → wp (f a) (fun _ => True))
    (post : Bool → Prop) (h_post : ∀ b, post b) :
    wpListAllM_wp f xs post := by
  induction xs generalizing post with
  | nil => simp [wpListAllM_wp]; exact h_post true
  | cons a tl ih =>
    simp only [wpListAllM_wp]
    apply wp_cons (f a) _ _ _ (h_pre a (List.mem_cons.mpr (Or.inl rfl)))
    intro b _; cases b <;> simp
    · exact h_post false
    · exact ih (fun a' ha' => h_pre a' (List.mem_cons_of_mem _ ha')) _ h_post

@[loomSpec, loomWpSimp]
noncomputable def WPGen.arrayAllM
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MAlgOrdered m Prop]
    {α : Type} {f : α → m Bool} {arr : Array α}
    (wpgf : ∀ a, WPGen (f a)) :
    WPGen (arr.allM f) where
  get := fun post =>
    (∀ i : Fin arr.size, (wpgf arr[i]).get (fun _ => True)) ∧ (∀ b : Bool, post b)
  prop := by
    intro post; intro ⟨h_pre, h_post⟩
    rw [← Array.allM_toList]
    exact wpListAllM_wp_le f arr.toList _
      (wpListAllM_wp_of_forall f arr.toList (wpgf_pre_of_mem wpgf h_pre) _ h_post)

/-! ## anyM -/

noncomputable def wpListAnyM_wp
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MAlgOrdered m Prop]
    {α : Type} (f : α → m Bool) :
    (xs : List α) → (Bool → Prop) → Prop
  | [], post => post false
  | a :: xs, post => wp (f a) (fun b =>
      if b then post true else wpListAnyM_wp f xs post)

theorem wpListAnyM_wp_le
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MAlgOrdered m Prop]
    {α : Type} (f : α → m Bool) :
    ∀ (xs : List α) (post : Bool → Prop),
    wpListAnyM_wp f xs post ≤ wp (xs.anyM f) post := by
  intro xs; induction xs with
  | nil => intro post; simp [wpListAnyM_wp, List.anyM, wp_pure]
  | cons a tl ih =>
    intro post; simp only [wpListAnyM_wp, List.anyM]; rw [wp_bind]
    apply wp_cons; intro b; cases b
    · simp; exact ih _
    · simp; rw [wp_pure]; exact id

theorem wpListAnyM_wp_of_forall
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MAlgOrdered m Prop]
    {α : Type} (f : α → m Bool) (xs : List α)
    (h_pre : ∀ a, a ∈ xs → wp (f a) (fun _ => True))
    (post : Bool → Prop) (h_post : ∀ b, post b) :
    wpListAnyM_wp f xs post := by
  induction xs generalizing post with
  | nil => simp [wpListAnyM_wp]; exact h_post false
  | cons a tl ih =>
    simp only [wpListAnyM_wp]
    apply wp_cons (f a) _ _ _ (h_pre a (List.mem_cons.mpr (Or.inl rfl)))
    intro b _; cases b <;> simp
    · exact ih (fun a' ha' => h_pre a' (List.mem_cons_of_mem _ ha')) _ h_post
    · exact h_post true

@[loomSpec, loomWpSimp]
noncomputable def WPGen.arrayAnyM
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MAlgOrdered m Prop]
    {α : Type} {f : α → m Bool} {arr : Array α}
    (wpgf : ∀ a, WPGen (f a)) :
    WPGen (arr.anyM f) where
  get := fun post =>
    (∀ i : Fin arr.size, (wpgf arr[i]).get (fun _ => True)) ∧ (∀ b : Bool, post b)
  prop := by
    intro post; intro ⟨h_pre, h_post⟩
    rw [← Array.anyM_toList]
    exact wpListAnyM_wp_le f arr.toList _
      (wpListAnyM_wp_of_forall f arr.toList (wpgf_pre_of_mem wpgf h_pre) _ h_post)
