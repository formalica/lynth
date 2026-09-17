import Lean
import Std.Tactic.BVDecide
import Lynth.Procedure
import Lynth.BV.Blast
import Lynth.BV.Recognize

/-!
Bitvector procedure: fixed-width `BitVec` goals via bit-blasting.

The goal is translated to the procedure's own language (`BvTerm`);
the blast + CDCL oracle (`Blast.checkValidEq/Ne`) decides validity
with full certificates (models + resolution traces); reconstruction
is kernel-checked `bv_decide`. Nonlinear-by-arithmetic but
bitwise-finite — the Z3 bit-blaster role.
-/
namespace Lynth.BV.Procedure

open Lean Elab Tactic
open Lynth.BV

/-- Try to close a `BitVec` (dis)equality: blast oracle, then
kernel-checked `bv_decide`. Yields immediately on non-BV goals. -/
def run : TacticM ProcedureOutcome := do
  let snapshot ← saveState
  let sys ←
    try Recognize.asBvGoal (← getMainTarget)
    catch _ => pure none
  match sys with
  | none => return .failure []
  | some (isEq, t1, t2) =>
    -- oracle attempt (no goal modification)
    try
      let ok := if isEq then checkValidEq t1 t2 10000
        else checkValidNe t1 t2 10000
      if ok then logInfo "[lynth:bv] blast refutation found"
      else logInfo "[lynth:bv] blast inconclusive"
    catch _ => pure ()
    -- kernel-checked reconstruction
    try
      let b ← `(tactic| bv_decide)
      evalTactic b
      let goals ← getUnsolvedGoals
      if goals.isEmpty then return .success
      restoreState snapshot
    catch _ =>
      restoreState snapshot
    return .failure []

end Lynth.BV.Procedure
