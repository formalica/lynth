import Lean
import Mathlib.Tactic.Linarith
import Lynth.Procedure

/-!
Nonlinear arithmetic procedure: polynomial inequalities by `nlinarith`.
-/

namespace Lynth.Nlin.Procedure

open Lean Elab Tactic

/-- Try to close a nonlinear arithmetic goal with `nlinarith`.
Like `Ring`, this procedure delegates search to a kernel-checked
normalizer (Positivstellensatz-style products); the internal theory is
owned by Mathlib's engine. -/
def run : TacticM ProcedureOutcome := do
  let snapshot ← saveState
  try
    let n ← `(tactic| nlinarith)
    evalTactic n
    let goals ← getUnsolvedGoals
    if goals.isEmpty then return .success
    restoreState snapshot
  catch _ =>
    restoreState snapshot
  return .failure []

end Lynth.Nlin.Procedure
