import Lean
import Lynth.Procedure
import Lynth.Euf.Procedure
import Lynth.Array.Rules

/-!
Array theory procedure: extensional-array reasoning as an EUF
sub-procedure.

The internal language is `select`/`store` nodes (`Rules.asSelect`,
`Rules.asStore`); the decision step adds read-over-write edges (R1/R2
with core-lemma proofs) to the EUF edge set and runs the shared
congruence closure. `select`-congruence at proof-identical positions
comes from closure itself; dependent-proof positions fall through to
later procedures. On failure, derived equalities are shared like EUF.
-/
namespace Lynth.Array.Procedure

open Lean Elab Tactic Meta
open Lynth.Array.Rules

/-- Try to close the goal with array rules + EUF closure. -/
def run : TacticM ProcedureOutcome := do
  let snapshot ← saveState
  let goal ← getMainTarget
  -- seeds: goal + context subterms
  let mut seeds : List Expr := Lynth.Euf.Procedure.collectSubterms goal
  for decl in ← getLCtx do
    if (decl.kind == .default) then
      seeds := seeds ++ Lynth.Euf.Procedure.collectSubterms decl.type
  let edges0 ← Lynth.Euf.Procedure.collectEdges
  let arrEdges ← Rules.ruleEdges seeds
  if !arrEdges.isEmpty then
    logInfo m!"[lynth:array] added {arrEdges.size} rule edges"
  let edges0 := edges0 ++ arrEdges.toList
  match ← Lynth.Euf.Procedure.asEq goal with
  | some (lhs, rhs) =>
    if lhs == rhs then
      let rfl ← `(tactic| rfl)
      evalTactic rfl
      if (← getUnsolvedGoals).isEmpty then return .success
      else
        restoreState snapshot
        return .failure []
    else
      -- assert rule edges as hypotheses so the shared closer (and all
      -- later procedures) see them; then close over enriched context
      for i in List.range arrEdges.size do
        let (l, r, prf) := arrEdges[i]!
        try
          let ty ← mkAppM ``Eq #[l, r]
          let mvar ← getMainGoal
          let (_, mvar') ← mvar.note
            (Name.mkStr1 s!"lynth_arr_{i}") prf (some ty)
          replaceMainGoal [mvar']
        catch _ => pure ()
      -- NOTE: re-focus *after* asserting — `note` changes the main
      -- goal's context, leaving ambient `getLCtx` stale otherwise.
      withMainContext do
        match ← Lynth.Euf.Procedure.closeEq lhs rhs with
        | true => return .success
        | false =>
          logInfo "[lynth:array] no equality path; sharing derived facts"
          let _ ← Lynth.Euf.Procedure.shareDerived
          return .failure []
  | none =>
    match ← Lynth.Euf.Procedure.asNe goal with
    | none =>
      if (← whnfR goal).isConstOf ``False then
        if ← Lynth.Euf.Procedure.closeFalse then return .success
        else return .failure []
      else return .failure []
    | some _ =>
      let introStx ← `(tactic| intro h_arr_ne)
      try evalTactic introStx catch _ => return .failure []
      withMainContext do
        if ← Lynth.Euf.Procedure.closeFalse then return .success
        else
          restoreState snapshot
          return .failure []

end Lynth.Array.Procedure
