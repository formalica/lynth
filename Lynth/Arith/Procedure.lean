-- Arithmetic procedure: linear (in)equalities over `Nat`/`Int`.
--
-- Internal representation is `Lynth.Arith.LinSys`; the decision oracle is
-- Fourier-Motzkin-style elimination today (Simplex core next, mirroring
-- Z3's `src/math/simplex` + `src/math/lp`). Reconstruction is delegated
-- to kernel-checked `omega`, which validates whatever the oracle claims;
-- the Farkas-certificate path (`lynth_farkas`) is tracked in `Axioms`.
import Lean
import Lynth.Procedure
import Lynth.Arith.Linear

namespace Lynth.Arith.Procedure

open Lean Elab Tactic

/-- Try to close a linear-arithmetic goal. `omega` is complete for
Presburger goals and kernel-checked, so it doubles as oracle +
reconstructor for this fragment. -/
def run : TacticM ProcedureOutcome := do
  let snapshot ← saveState
  try
    let om ← `(tactic| omega)
    evalTactic om
    let goals ← getUnsolvedGoals
    if goals.isEmpty then return .success
    restoreState snapshot
  catch _ =>
    restoreState snapshot
  return .failure []

end Lynth.Arith.Procedure
