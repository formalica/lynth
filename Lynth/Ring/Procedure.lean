-- Ring-normalization procedure: semiring identities by `ring`.
--
-- Nonlinear goals (`(a + b)^2 = …`, `x * y` manipulation) fall outside
-- every linear fragment; like Z3's `grobner`/`polynomial` theory
-- (`src/math/grobner`, `src/math/polynomial`), this procedure owns its
-- normalizer. Reconstruction is kernel-checked `ring` itself.
import Lean
import Mathlib.Tactic.Ring
import Lynth.Procedure

namespace Lynth.Ring.Procedure

open Lean Elab Tactic

/-- Try to close a (semi)ring identity with `ring`. -/
def run : TacticM ProcedureOutcome := do
  let snapshot ← saveState
  try
    let r ← `(tactic| ring)
    evalTactic r
    let goals ← getUnsolvedGoals
    if goals.isEmpty then return .success
    restoreState snapshot
  catch _ =>
    restoreState snapshot
  return .failure []

end Lynth.Ring.Procedure
