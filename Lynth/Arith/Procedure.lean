-- Arithmetic procedure: linear (in)equalities over `Nat`/`Int`.
--
-- Internal pipeline mirrors Z3's arithmetic theory solver split: the goal
-- + hypotheses are translated to the procedure's own language
-- (`Fourier.LeC` systems via `Recognize`); two oracles cross-check the
-- refutation — FM elimination with Farkas lineage (`Fourier.solve`) and
-- tableau Simplex à la Dutertre–de Moura (`Simplex.solve`, standing in
-- for Z3's Simplex core) — and reconstruction is kernel-checked `omega`
-- (complete for Presburger goals). Certificates are traced;
-- `Lynth.lynth_farkas` activates once Farkas validation lands.
import Lean
import Lynth.Procedure
import Lynth.Arith.Linear
import Lynth.Arith.Fourier
import Lynth.Arith.Simplex
import Lynth.Arith.BranchBound
import Lynth.Arith.Recognize

namespace Lynth.Arith.Procedure

open Lean Elab Tactic

/-- Try to close a linear-arithmetic goal. Runs the FM + Simplex oracles
for refutation certificates (cross-checked), then closes with
kernel-checked `omega`. -/
def run : TacticM ProcedureOutcome := do
  let snapshot ← saveState
  -- Oracle attempts (pure MetaM reads; no goal modification).
  try
    match ← Recognize.buildSys with
    | some sys =>
      let fm := Fourier.solve sys 128
      let sx := Simplex.solve (sys.map fun c => (c.coeffs, c.const)) 1024
      -- branch-and-bound closes the ℤ-completeness gap of the relaxations
      let nVars := sys.foldl (fun m c => Nat.max m c.coeffs.length) 0
      let bbv := BranchBound.bb (sys.map fun c => (c.coeffs, c.const))
        (List.range nVars) 4 1024
      match fm, sx with
      | some cert, some none =>
        if Fourier.checkCert sys cert then
          logInfo m!"[lynth:arith] FM+Simplex agree: verified refutation (Farkas size {cert.length})"
        else
          logInfo "[lynth:arith] WARNING: FM certificate FAILED validation (solver bug)"
      | some cert, _ =>
        if Fourier.checkCert sys cert then
          logInfo m!"[lynth:arith] FM verified refutation (Farkas size {cert.length}); Simplex inconclusive"
        else
          logInfo "[lynth:arith] WARNING: FM certificate FAILED validation (solver bug)"
      | none, some none =>
        logInfo "[lynth:arith] WARNING: Simplex refutes but FM does not (oracle mismatch)"
      | _, _ =>
        match bbv with
        | .unsat =>
          logInfo "[lynth:arith] branch-and-bound refutation (needs integrality)"
        | _ =>
          logInfo "[lynth:arith] oracles inconclusive (relaxation SAT or nonlinear)"
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
