-- `lynth` dispatcher: runs procedures in order, threading explanations.
--
-- Pipeline (no staged SMT loop; the user states the goal via types and
-- lynth fills data + proofs):
-- 1. `Witness` — subtype/refinement goals (`{n // P n}`), computable search.
-- 2. `Sat` — propositional skeleton + closing tactics.
-- 3. `Arith` — linear arithmetic (`omega`-checked).
-- Each failure returns an explanation usable by the next procedure
-- (variable sharing = equality facts with proofs); all are traced.
import Lean
import Lynth.Procedure
import Lynth.Euf.Procedure
import Lynth.Witness
import Lynth.Sat.Procedure
import Lynth.Arith.Procedure

namespace Lynth.Frontend

open Lean Elab Tactic

/-- Run all procedures in order until one closes the goal. -/
def dispatch : TacticM Unit := do
  let procs : List (String × TacticM ProcedureOutcome) := [
    ("witness", Lynth.Witness.run),
    ("euf", Lynth.Euf.Procedure.run),
    ("sat", Lynth.Sat.Procedure.run),
    ("arith", Lynth.Arith.Procedure.run)
  ]
  let mut explanations : List Explanation := []
  for (name, proc) in procs do
    match ← proc with
    | .success =>
      logInfo m!"[lynth] procedure `{name}` closed the goal"
      return
    | .failure expl =>
      logInfo m!"[lynth] procedure `{name}` failed ({expl.length} new facts)"
      explanations := expl :: explanations
  throwError "[lynth] all procedures failed"

end Lynth.Frontend
