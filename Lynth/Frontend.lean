module

meta import Lean
import Lean
meta import all Lynth.Procedure
import all Lynth.Procedure
meta import all Lynth.Answer.Procedure
import all Lynth.Answer.Procedure
meta import all Lynth.Meta.Procedure
import all Lynth.Meta.Procedure
meta import all Lynth.FinSearch.Procedure
import all Lynth.FinSearch.Procedure
meta import all Lynth.FinSearch.ListInfer
import all Lynth.FinSearch.ListInfer
meta import all Lynth.Euf.Procedure
import all Lynth.Euf.Procedure
meta import all Lynth.Egraph.Procedure
import all Lynth.Egraph.Procedure
meta import all Lynth.Quant.Procedure
import all Lynth.Quant.Procedure
meta import all Lynth.Array.Procedure
import all Lynth.Array.Procedure
meta import all Lynth.Datatypes.Procedure
import all Lynth.Datatypes.Procedure
meta import all Lynth.BV.Procedure
import all Lynth.BV.Procedure
meta import all Lynth.Ring.Procedure
import all Lynth.Ring.Procedure
meta import all Lynth.Nlin.Procedure
import all Lynth.Nlin.Procedure
meta import all Lynth.Witness
import all Lynth.Witness
meta import all Lynth.Sat.Procedure
import all Lynth.Sat.Procedure
meta import all Lynth.Arith.Procedure
import all Lynth.Arith.Procedure
meta import all Lynth.Interval
import all Lynth.Interval

/-!
`lynth` dispatcher: runs procedures in order, threading explanations.

Pipeline (no staged SMT loop; the user states the goal via types and
lynth fills data + proofs):
0. `FinSearch` — finite-function synthesis goals (SAT-backed search);
   scalars yield to `Witness`.
   `ListInfer` — unbounded `List Nat` goals whose length and value
   bounds infer exactly, enumerated and kernel-checked.
1. `Witness` — subtype/refinement goals (`{n // P n}`), computable search.
2. `Sat` — propositional skeleton + closing tactics.
3. `Arith` — linear arithmetic (`omega`-checked).
Each failure returns an explanation usable by the next procedure
(variable sharing = equality facts with proofs); all are traced.
-/
meta section

namespace Lynth.Frontend

open Lean Elab Tactic

/-- Run all procedures in order until one closes the goal.
Failures accumulate notes; the final error reports every procedure's
outcome so users can see how far the pipeline got. -/
def dispatch : TacticM Unit := do
  let procs : List (String × TacticM ProcedureOutcome) := [
    ("interval", Lynth.Interval.Procedure.run),
    ("answer", Lynth.Answer.Procedure.run),
    ("meta", Lynth.Meta.Procedure.run),
    ("finsearch", Lynth.FinSearch.Procedure.run),
    ("listsynth", Lynth.FinSearch.ListInfer.run),
    ("witness", Lynth.Witness.run),
    ("euf", Lynth.Euf.Procedure.run),
    ("egraph", Lynth.Egraph.Procedure.run),
    ("quant", Lynth.Quant.Procedure.run),
    ("array", Lynth.Array.Procedure.run),
    ("datatypes", Lynth.Datatypes.Procedure.run),
    ("bv", Lynth.BV.Procedure.run),
    ("ring", Lynth.Ring.Procedure.run),
    ("sat", Lynth.Sat.Procedure.run),
    ("arith", Lynth.Arith.Procedure.run),
    ("nlin", Lynth.Nlin.Procedure.run)
  ]
  let mut notes : Array String := #[]
  for (name, proc) in procs do
    match ← proc with
    | .success =>
      logInfo m!"[lynth] procedure `{name}` closed the goal"
      return
    | .failure expl =>
      logInfo m!"[lynth] procedure `{name}` failed ({expl.length} new facts)"
      notes := notes.push s!"- `{name}` failed ({expl.length} new facts)"
  throwError m!"[lynth] all procedures failed:\n{"\n".intercalate notes.toList}"

end Lynth.Frontend
