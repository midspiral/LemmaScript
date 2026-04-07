/-
  Simp lemmas and tactics for Std.HashSet operations in LemmaScript proofs.
-/
import Velvet.Syntax
import Lean

@[loomAbstractionSimp, simp]
theorem hashset_insert_size_le [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {s : Std.HashSet α} {k : α} :
    (s.insert k).size ≤ s.size + 1 :=
  Std.HashSet.size_insert_le

@[loomAbstractionSimp, simp]
theorem hashset_size_le_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {s : Std.HashSet α} {k : α} :
    s.size ≤ (s.insert k).size :=
  Std.HashSet.size_le_size_insert

open Lean Elab Tactic Meta

/-- Strip `WithName` from local variable types by reducing to whnf.
    Only processes variables whose type is an application of `WithName`. -/
elab "strip_withname" : tactic => do
  let ctx ← getLCtx
  for decl in ctx do
    if decl.isImplementationDetail then continue
    let ty := decl.type
    -- Only process if the type head is WithName
    unless ty.isAppOf ``WithName do continue
    let ty' ← whnf ty
    if ty == ty' then continue
    try
      let goal ← getMainGoal
      let newGoal ← goal.changeLocalDecl decl.fvarId ty'
      replaceMainGoal [newGoal]
    catch _ => pure ()
