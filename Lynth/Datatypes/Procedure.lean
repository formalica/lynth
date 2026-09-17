import Lean
import Lynth.Procedure
import Lynth.Euf.Procedure

/-!
Datatypes theory procedure: constructor injectivity + discrimination
as an EUF sub-procedure.

Driven by Lean core's bounded `injections` fixpoint
(`maxDepth` + `forbidden` set): same-constructor equations splinter
into per-argument equalities kept as shared facts; contradictory
equations (distinct constructors) close the goal outright. Only
equations touching constructors are processed — plain variable
equalities stay EUF's job (passed via `forbidden`). Everything is
kernel-checked by the core tactic machinery; this procedure enriches
the context and yields unless the goal itself closes.
-/
namespace Lynth.Datatypes.Procedure

open Lean Elab Tactic Meta

/-- Does `e` (an equation side) mention a constructor application? -/
def mentionsCtor (e : Expr) : MetaM Bool := do
  if (← isConstructorApp? e).isSome then pure true
  else match e with
    | .app f a => pure ((← mentionsCtor f) || (← mentionsCtor a))
    | _ => pure false

/-- Plain (constructor-free) `Eq` hyps, forbidden from injection:
only equations touching constructors are processed, plain variable
equalities stay EUF's job. -/
def collectForbidden : TacticM FVarIdSet := do
  let mut forbid : FVarIdSet := {}
  for decl in ← getLCtx do
    if (decl.kind == .default) then
      match ← Lynth.Euf.Procedure.asEq decl.type with
      | none => pure ()
      | some (l, r) =>
        if (← mentionsCtor l) || (← mentionsCtor r) then pure ()
        else forbid := forbid.insert decl.fvarId
  pure forbid

/-- One bounded injection round over the main goal. Returns true iff
the goal closed. Enrichment (new equations) is always kept. -/
def injectRound (forbid : FVarIdSet) : TacticM Bool := do
  let mvar ← getMainGoal
  try
    match ← Lean.Meta.injections mvar [] 3 forbid with
    | .solved =>
      if (← getUnsolvedGoals).isEmpty then pure true else pure false
    | .subgoal mvar' _ _ =>
      replaceMainGoal [mvar']
      pure false
  catch _ => pure false

/-- Run: inject constructor equations (Ne goals via intro first).
Closes on contradiction, else yields with enriched context. -/
def run : TacticM ProcedureOutcome := do
  let goal ← getMainTarget
  match ← Lynth.Euf.Procedure.asEq goal with
  | some _ =>
    -- Eq goals: only a contradictory context can close here
    let forbid ← collectForbidden
    if ← injectRound forbid then return .success
    else
      logInfo "[lynth:datatypes] injected constructor equations"
      return .failure []
  | none =>
    match ← Lynth.Euf.Procedure.asNe goal with
    | none =>
      if (← whnfR goal).isConstOf ``False then
        let forbid ← collectForbidden
        if ← injectRound forbid then return .success
        else return .failure []
      else return .failure []
    | some _ =>
      let introStx ← `(tactic| intro h_dt_ne)
      try evalTactic introStx catch _ => return .failure []
      -- re-focus: `intro` changes the main goal's context, refresh it
      withMainContext do
        let forbid ← collectForbidden
        if ← injectRound forbid then return .success
        else return .failure []

end Lynth.Datatypes.Procedure
