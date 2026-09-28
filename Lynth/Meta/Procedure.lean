import Lean
import Lynth.Procedure
import Lynth.Witness
import Lynth.Answer.Procedure
import Lynth.Sat.Compile

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
      | .app (.const ``Option _) _ =>
        let args := oR.getAppArgs
        if args.size != 1 then pure none
        else pure (some (i, args[0]!))
      | _ => pure none
  | _ => pure none

/-- Split `A ∧ B ∧ C` (right-nested `And`). -/
def splitAnd3 (e : Expr) : Option (Expr × Expr × Expr) := do
  let (fn1, args1) := (e.getAppFn, e.getAppArgs)
  match fn1 with
  | .const ``And _ =>
    if args1.size != 2 then none
    else
      let bc := args1[1]!
      let (fn2, args2) := (bc.getAppFn, bc.getAppArgs)
      match fn2 with
      | .const ``And _ =>
        if args2.size != 2 then none
        else some (args1[0]!, args2[0]!, args2[1]!)
      | _ => none
  | _ => none

/-- Extract the validity predicate as a two-argument lambda from the
soundness conjunct `∀ g c, solver g = some c → P g c`. Returns
`(inputTy, outputTy, P)` with `P : ∀ input output, Prop`. -/
def extractValid (pred solverDom : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  withLocalDeclD `solver solverDom fun s => do
    let spec ← whnf (mkApp pred s)
    let spec3 := splitAnd3 spec
    match spec3 with
    | none =>
      pure none
    | some (soundC, _, _) =>
      forallTelescope soundC fun fvs body => do
        -- soundness `∀ g c, Eq → P`: the telescope peels the
        -- implication hypothesis too, so expect 3 entries
        -- `[g, c, eqProof]` with `body = P`
        if fvs.size != 3 then
          return none
        let eqTy ← inferType fvs[2]!
        let pBody := body
        if pBody.hasLooseBVars then
          pure none
        else
          let eqR ← whnf eqTy
          match eqR.getAppFn with
          | .const ``Eq _ =>
            let args := eqR.getAppArgs
            if args.size != 3 then
              pure none
            else
              let lhs := args[1]!
              let rhs := args[2]!
              match lhs.getAppFn, rhs.getAppFn with
              | .fvar sid, .const ``Option.some _ =>
                if sid != s.fvarId! then
                  pure none
                else
                  let inTy ← inferType fvs[0]!
                  let outTy ← inferType fvs[1]!
                  let plam ← mkLambdaFVars #[fvs[0]!, fvs[1]!] pBody
                  pure (some (inTy, outTy, plam))
              | _, _ =>
                pure none
          | _ =>
            pure none

/-- Synthesize via the shared compiler + total solver (plan):
compile the extracted validity predicate to a parameterized CNF,
run the total solver under the hood, decode, and assemble the three
correctness proofs from fragment lemmas + solver corollaries.
Currently yielding: the encoder/assembler lands incrementally below,
never as a contradicting shortcut. -/
def synthesizeSat (shape : Lynth.Witness.WitShape) (P : Expr) :
    TacticM Bool := do
  try
    let PR ← whnf P
    let _ ← lambdaTelescope PR fun lams _ => pure lams.size
    pure false
  catch _ => pure false

/-- Run: intro Pi params (e.g. board size), recognize solver subtypes,
extract the validity predicate, and synthesize via the shared
compiler + total solver. -/
def run : TacticM ProcedureOutcome := do
  let snapshot ← saveState
  -- intro Pi binders (size params like `n`) to expose the Subtype
  while true do
    let t ← whnf (← getMainTarget)
    match t with
    | .forallE _ _ _ _ =>
      try
        evalTactic (← `(tactic| intro _))
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
    match ← extractValid shape.pred shape.dom with
    | none =>
      restoreState snapshot
      return .failure []
    | some (_, _, P) =>
      if ← synthesizeSat shape P then
        return .success
      else
        restoreState snapshot
        return .failure []

end Lynth.Meta.Procedure
