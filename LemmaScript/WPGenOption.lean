/-
  WPGen rules for Option branching and dependent if-then-else (dite).
-/
import Velvet.Syntax
import Velvet.Std

universe u v

/-- WPGen for dependent if-then-else (dite): `if h : p then f h else g h` -/
@[loomSpec high, loomWpSimp]
noncomputable def WPGen.dite
    {l : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [CompleteBooleanAlgebra l] [MAlgOrdered m l]
    {α : Type u} {p : Prop} {hd : Decidable p}
    {f : p → m α} {g : ¬p → m α}
    (wpgf : ∀ h, WPGen (f h)) (wpgg : ∀ h, WPGen (g h)) :
    WPGen (@dite (m α) p hd f g) where
  get := fun post =>
    (⨅ hc : WithName p (Lean.Name.anonymous.mkStr "if_pos"), (wpgf hc).get post) ⊓
    (⨅ hc : WithName (¬p) (Lean.Name.anonymous.mkStr "if_neg"), (wpgg hc).get post)
  prop := by
    intro post
    split
    · refine inf_le_of_left_le ?_
      apply iInf_le_iff.mpr
      rename_i hc
      intro b hi
      exact le_trans (hi hc) ((wpgf hc).prop post)
    · refine inf_le_of_right_le ?_
      apply iInf_le_iff.mpr
      rename_i hc
      intro b hi
      exact le_trans (hi hc) ((wpgg hc).prop post)
