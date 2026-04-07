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

open Lean Elab Tactic Meta in
private partial def stripOnce : TacticM Bool := do
  let goal ← getMainGoal
  let ctx ← goal.getDecl >>= fun d => pure d.lctx
  for decl in ctx do
    if decl.isImplementationDetail then continue
    let ty := decl.type
    unless ty.isAppOf ``WithName do continue
    let ty' ← whnf ty
    if ty == ty' then continue
    let newGoal ← goal.changeLocalDecl decl.fvarId ty' (checkDefEq := false)
    replaceMainGoal [newGoal]
    return true
  return false

open Lean Elab Tactic Meta in
/-- Strip `WithName` from local variable types. -/
elab "strip_withname" : tactic => do
  for _ in List.range 20 do
    unless (← stripOnce) do return
