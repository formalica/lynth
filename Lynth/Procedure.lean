-- Core result/explanation types for lynth procedures.
--
-- A procedure explains failure (or new inference) as a list of Lean `Prop`s
-- together with their proofs, so the next procedure can consume them directly.
-- This replaces Z3-style variable sharing: variable assignments are just
-- equality facts (`x = v`) with proofs.
import Lean

namespace Lynth

/-- A single piece of new information produced by a procedure:
a proposition together with its kernel-checked proof. -/
structure Fact where
  /-- The inferred proposition. -/
  prop : Prop
  /-- Proof of `prop`. -/
  proof : prop

/-- Explanation returned by a procedure. On failure: why it failed.
On partial success: new information inferred while trying to solve. -/
abbrev Explanation := List Fact

/-- A procedure's outcome on the current goal. -/
inductive ProcedureOutcome where
  | success : ProcedureOutcome
  | failure : Explanation → ProcedureOutcome
  deriving Inhabited

/-- A named procedure: a tactic-block-sized solver step.
Procedures may add inferred `Fact`s to the local context so that
later procedures can use them (variable sharing via explanations). -/
structure Procedure where
  name : String
  run : Lean.Elab.Tactic.TacticM ProcedureOutcome

/-- Pretty-print an explanation as trace output. -/
def traceExplanation (expl : Explanation) : Lean.Elab.Tactic.TacticM Unit := do
  Lean.logInfo m!"[lynth] procedure failed with {expl.length} inferred facts"

end Lynth
