-- Arithmetic procedure: linear (in)equalities over `Nat`/`Int`.
--
-- Internal pipeline mirrors Z3's arithmetic theory solver split: the goal
-- + hypotheses are translated to the procedure's own language
-- (`Fourier.LeC` systems via `Recognize`), the FM elimination oracle
-- (`Fourier.solve`, standing in for Z3's Simplex core) searches for a
-- refutation with Farkas lineage, and reconstruction is kernel-checked
-- `omega` (complete for Presburger goals). The computed certificate is
-- traced; `lynth_farkas` tracks future direct certificate reconstruction.
import Lean
import Lynth.Procedure
import Lynth.Arith.Linear
import Lynth.Arith.Fourier
import Lynth.Arith.Recognize

namespace Lynth.Arith.Procedure

open Lean Elab Tactic

/-- Try to close a linear-arithmetic goal. Runs the FM oracle for a
refutation certificate, then closes with kernel-checked `omega`. -/
def run : TacticM ProcedureOutcome := do
  let snapshot ← saveState
  -- FM oracle attempt (pure MetaM read; no goal modification).
  try
    match ← Recognize.buildSys with
    | some sys =>
      match Fourier.solve sys 128 with
      | some cert =>
        logInfo m!"[lynth:arith] FM refutation found (Farkas size {cert.length})"
      | none =>
        logInfo "[lynth:arith] FM inconclusive (relaxation SAT or nonlinear)"
    | none => pure ()
  catch _ => pure ()
  restoreState snapshot
  -- Kernel-checked reconstruction (complete for Presburger `Int`/`Nat`).
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
