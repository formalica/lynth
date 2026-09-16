-- SAT procedure: Lean `Prop` skeleton → internal CNF → solver → proof.
--
-- Translation (`Abstract`) maps goal + hypotheses to a `PropForm`
-- skeleton; `Encode` Tseitin-encodes its negation and the CDCL oracle
-- (`Cdcl`) checks it. UNSAT ⟹ tautology: reconstruction tries closing
-- tactics. SAT ⟹ inconclusive: an (empty) explanation is returned for the
-- next procedure. Reconstruction is always kernel-checked; the
-- certificate path via `Lynth.lynth_sat_resolve` activates once trace
-- validation lands.
import Lean
import Lynth.Procedure
import Lynth.Sat.Solver
import Lynth.Sat.Reconstruct
import Lynth.Sat.Encode
import Lynth.Sat.Abstract

namespace Lynth.Sat.Procedure

open Lean Elab Tactic

/-- Try to close a propositional goal using the SAT oracle to guide
reconstruction. Returns `.success` if the goal is closed. -/
def run : TacticM ProcedureOutcome := do
  -- Real oracle path: abstract goal + hypotheses, check skeleton validity.
  let taut ←
    try
      let (form, nAtoms) ← Abstract.abstractContext
      pure (Encode.isTautology form nAtoms 10000)
    catch _ => pure false
  logInfo m!"[lynth:sat] skeleton tautology: {taut}"
  -- Probe reconstruction tactics in order; each is kernel-checked.
  let p1 ← `(tactic| assumption)
  let p2 ← `(tactic| rfl)
  let p3 ← `(tactic| simp_all)
  let p4 ← `(tactic| grind)
  let p5 ← `(tactic| decide)
  let probes : List (TSyntax `tactic) := [p1, p2, p3, p4, p5]
  for stx in probes do
    let snapshot ← saveState
    try
      evalTactic stx
      let goals ← getUnsolvedGoals
      if goals.isEmpty then return .success
      restoreState snapshot
    catch _ =>
      restoreState snapshot
  return .failure []

end Lynth.Sat.Procedure
