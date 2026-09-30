import Lynth.Procedure
import Lynth.Interval.Goals.Approx

/-!
# The `interval` procedure of `lynth`

Recognizes goals with real/complex numerical content and dispatches them to the
goal handlers in `Lynth/Interval/Goals`.  Yields (`.failure []`, goal
untouched) on anything it does not handle.
See `docs/interval/01-architecture.md §3, §6`.
-/

namespace Lynth.Interval.Procedure

open Lean Meta Elab Tactic

initialize registerTraceClass `lynth.interval

/-- does the goal mention real or complex numbers -/
def relevant (ty : Lean.Expr) : Bool :=
  (ty.find? fun e => e.isConstOf ``Real || e.isConstOf ``Complex).isSome

def run : TacticM ProcedureOutcome := do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  unless relevant ty do return .failure []
  let s ← saveState
  try
    if (← isProp ty) && !ty.hasFVar && !ty.hasMVar then
      if let some pf ← Goals.proveClosed? ty then
        goal.assign pf
        replaceMainGoal []
        return .success
    else if !(← isProp ty) then
      let ty' ← whnfR ty
      if let some pf ← Goals.proveRatSubtype? ty' then
        goal.assign pf
        replaceMainGoal []
        return .success
  catch e =>
    trace[lynth.interval] "interval: {e.toMessageData}"
  s.restore
  return .failure []

end Lynth.Interval.Procedure
