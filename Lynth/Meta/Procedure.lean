import Lean
import Lynth.Procedure
import Lynth.Witness
import Lynth.Meta.Solver

/-!
Meta solver-function procedure: synthesize total `I → Option O`
solvers from finite candidate lists plus decidable checks.

Generic over all puzzles: recognizes `Subtype` goals whose domain is
a solver function (`I → Option O`) and whose predicate unfolds to the
three-conjunct correctness shape (soundness + completeness +
none-iff), extracts the validity predicate `P`, and builds
`enumSolve Fintype.elems (fun i o => decide (P i o))` with correctness
via `Lynth.Meta.Solver` lemmas (core axioms only). Yields gracefully
on anything else; never mentions any puzzle by name.
-/
namespace Lynth.Meta.Procedure

open Lean Elab Tactic Meta

/-- Solver domain match: `I → Option O` (non-dependent Pi). -/
def matchSolverDom (dom : Expr) : MetaM (Option (Expr × Expr)) := do
  let d ← whnf dom
  match d with
  | .forallE _ i o _ =>
    if o.hasLooseBVars then pure none
    else
      let oR ← whnf o
      match oR with
      | .app (.const ``Option _) outTy =>
        let args := oR.getAppArgs
        if args.size != 1 then pure none
        else pure (some (i, args[0]!))
      | _ => pure none
  | _ => pure none

/-- Run: intro Pi params (e.g. board size), then recognize solver
subtypes. Synthesis lands next; for now yield with a diagnostic so
recognition can be validated without behavior change. -/
def run : TacticM ProcedureOutcome := do
  let snapshot ← saveState
  -- intro Pi binders (size params like `n`) to expose the Subtype
  let mut nIntros := 0
  while true do
    let t ← whnf (← getMainTarget)
    match t with
    | .forallE _ _ _ _ =>
      try
        evalTactic (← `(tactic| intro _))
        nIntros := nIntros + 1
      catch _ => break
    | _ => break
  let goal ← getMainTarget
  let some shape ← Lynth.Witness.classify goal
    | restoreState snapshot
      return .failure []
  match ← matchSolverDom shape.dom with
  | none =>
    restoreState snapshot
    return .failure []
  | some _ =>
    -- recognized a solver-function goal; synthesis next step
    dbg_trace "[meta-dbg] solver-goal recognized"
    restoreState snapshot
    return .failure []

end Lynth.Meta.Procedure
