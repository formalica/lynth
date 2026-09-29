import Lean
import Lynth.Procedure
import Lynth.Witness
import Lynth.Answer.Procedure
import Lynth.Sat.Compile

/-!
Meta solver-function procedure: synthesize total `I → Option O`
solvers through the shared spec compiler + verified total solver.

Generic over all puzzles: recognizes `Subtype` goals whose domain is
a solver function (`I → Option O`) and whose predicate unfolds to the
three-conjunct correctness shape (soundness + completeness +
none-iff), extracts the validity predicate `P`, compiles it to a
parameterized CNF via the discrimination-tree fragment registry, and
builds the uniform `runSolver` body with correctness assembled from
fragment lemmas + solver corollaries. Yields gracefully on anything
else; never mentions any puzzle by name.
-/
namespace Lynth.Meta.Procedure

open Lean Elab Tactic Meta
open Lynth.Sat.Compile

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
correctness proofs from fragment lemmas + solver corollaries. -/
def synthesizeSat (shape : Lynth.Witness.WitShape) (P : Expr) :
    TacticM Bool := do
  try
    let some frags ← matchFrag P
      | return false
    if frags.isEmpty then return false
    -- uniform bounds from the output type; all frags must agree
    let outTy ← do
      let PR ← whnf P
      lambdaTelescope PR fun lams _ => do
        if lams.size != 2 then throwError "P shape"
        pure (← inferType lams[1]!)
    let outTyR ← whnf outTy
    let (n, k) ← match outTyR with
      | .forallE _ dom cod _ =>
        if cod.hasLooseBVars then return false
        else
          match ← finBound dom, ← finBound cod with
          | some nn, some kk => pure (nn, kk)
          | _, _ => return false
      | _ => return false
    if !(frags.all fun fr => fr.n == n && fr.k == k) then
      return false
    -- input type from `P`
    let inTy ← do
      let PR ← whnf P
      lambdaTelescope PR fun lams _ => do
        if lams.size != 2 then throwError "P shape"
        pure (← inferType lams[0]!)
    let hk ← zeroLtLit k
    let encode ← mkEncode frags n k inTy
    let decode ← mkDecode n k hk
    -- solver value: `fun input => runSolver ... input`
    let solverVal ← withLocalDeclD `input inTy fun gin => do
      let sv ← mkAppM ``Lynth.Sat.Compile.runSolver
        #[encode, decode,
          mkNatLit compileFuel, mkNatLit compileRestart, gin]
      mkLambdaFVars #[gin] sv
    unless ← isDefEq (← inferType solverVal) shape.dom do
      return false
    -- assemble `hsound` / `hcomp` from fragment masters, then close
    -- via `runSolver_*` (all first-order over Nats/Bools; `Decidable`
    -- instances are reused from `check`, never synthesized afresh)
    let aty ← assignTy
    let ok ← withLocalDeclD `input inTy fun gin =>
      withLocalDeclD `mod aty fun m => do
        -- open body + components with our fvars (single source: the
        -- closed `encode` is alpha-equal, so everything unifies)
        let (body, comps) ← mkEncodeBody gin frags n k
        -- hsound: decode every model into validity
        let hsound ← withLocalDeclD `h
          (← mkEq (mkApp (mkApp (mkConst ``Lynth.Sat.checkSat []) body) m)
            (mkConst ``Bool.true [])) fun h => do
          let helds ← splitHeld m h comps
          let mlen := comps.length
          let cellsHeld ← match helds[mlen - 1]? with
            | some e => pure e
            | none => throwError "cells held"
          let hrows ← withLocalDeclD `v (mkApp (mkConst ``Fin []) (mkNatLit n)) fun v => do
            let rh ← mkAppM ``Lynth.Sat.FinVal.cellsRows
              #[mkNatLit n, mkNatLit k, m, cellsHeld, v]
            mkLambdaFVars #[v] rh
          -- `P gin (decode m)` split into conjuncts (same order as frags)
          let decApp := mkApp decode m
          let papp := mkApp (mkApp P gin) decApp
          let pappR ← whnf (← Core.betaReduce papp)
          let conjs := splitConj pappR
          if conjs.length != frags.length then throwError "conj/frag mismatch"
          else
            let mut proofs : List Expr := []
            for (jc, (cj, fr)) in (List.range frags.length).zip (conjs.zip frags) do
              let fh ← match helds[jc]? with
                | some e => pure e
                | none => throwError "fam held"
              let pf ← forallTelescope cj fun fvs cbody => do
                if fr.kind == .ne then
                  if fvs.size != 3 then throwError "ne shape"
                  else
                    let q ← mkAppM ``Lynth.Sat.Compile.neFam_sound
                      #[inTy, mkNatLit n, mkNatLit k, hk, fr.guard, gin,
                        m, hrows, fh, fvs[0]!, fvs[1]!, fvs[2]!]
                    let qh ← mkExpectedTypeHint q cbody
                    mkLambdaFVars fvs qh
                else if fr.kind == .eq then
                  if fvs.size != 3 then throwError "eq shape"
                  else
                    let q ← mkAppM ``Lynth.Sat.Compile.eqFam_sound
                      #[inTy, mkNatLit n, mkNatLit k, hk, fr.guard, gin,
                        m, hrows, fh, fvs[0]!, fvs[1]!, fvs[2]!]
                    let qh ← mkExpectedTypeHint q cbody
                    mkLambdaFVars fvs qh
                else if fr.kind == .inj then
                  let q ← mkAppM ``Lynth.Sat.Compile.injFam_sound
                    #[mkNatLit n, mkNatLit k, hk, m, hrows, fh]
                  let qh ← mkExpectedTypeHint q cbody
                  mkLambdaFVars fvs qh
                else
                  if fvs.size != 1 then throwError "req shape"
                  else
                    let q ← mkAppM ``Lynth.Sat.Compile.reqFam_sound
                      #[inTy, mkNatLit n, mkNatLit k, hk, fr.guard, gin,
                        m, hrows, fh, fvs[0]!]
                    let qh ← mkExpectedTypeHint q cbody
                    mkLambdaFVars fvs qh
              proofs := proofs ++ [pf]
            let whole ← combineConj proofs
            let wholeH ← mkExpectedTypeHint whole papp
            mkLambdaFVars #[gin, m, h] wholeH
            -- traced by caller
        -- hcomp: every validity proof yields a satisfying model.
        -- NOTE: `f` binds the *structural* output type (not the
        -- alias): master applications need the unfolded form.
        let hcomp ← withLocalDeclD `input inTy fun gin =>
          withLocalDeclD `f outTyR fun f => do
            withLocalDeclD `hPf (mkApp (mkApp P gin) f) fun hPf => do
            -- `P gin f` split; pair conjunct-proofs with frags
            let papp2 := mkApp (mkApp P gin) f
            let pappR ← whnf (← Core.betaReduce papp2)
            let conjs := splitConj pappR
            if conjs.length != frags.length then throwError "conj/frag mismatch"
            else
              let mod ← mkAppM ``Lynth.Sat.FinVal.modelOf
                #[mkNatLit n, mkNatLit k, f]
              let cellsProof ← mkAppM ``Lynth.Sat.FinVal.cellsComplete
                #[mkNatLit n, mkNatLit k, hk, f]
              let mut famProofs : List Expr := []
              for (jc, fr) in (List.range frags.length).zip frags do
                let cp ← conjProj hPf jc frags.length
                let pf ← if fr.kind == .ne then
                  mkAppM ``Lynth.Sat.Compile.neFam_complete
                    #[inTy, mkNatLit n, mkNatLit k, hk, fr.guard,
                      gin, f, cp]
                else if fr.kind == .eq then
                  mkAppM ``Lynth.Sat.Compile.eqFam_complete
                    #[inTy, mkNatLit n, mkNatLit k, hk, fr.guard,
                      gin, f, cp]
                else if fr.kind == .inj then
                  mkAppM ``Lynth.Sat.Compile.injFam_complete
                    #[mkNatLit n, mkNatLit k, hk, f, cp]
                else
                  mkAppM ``Lynth.Sat.Compile.reqFam_complete
                    #[inTy, mkNatLit n, mkNatLit k, hk, fr.guard,
                      gin, f, cp]
                famProofs := famProofs ++ [pf]
              -- combine over components rebuilt with this `gin`
              let (_, comps2) ← mkEncodeBody gin frags n k
              let fullProof ← combineHeld mod
                (famProofs ++ [cellsProof]) comps2
              -- `∃ m, ...` with explicit predicate over the
              -- scope-local body (never a foreign closed `encode`,
              -- whose fvars would break defeq)
              let body2 ← appendChain comps2
              let aty2 ← assignTy
              let exPred ← withLocalDeclD `mm aty2 fun mm => do
                let stmt ← mkEq
                  (mkApp (mkApp (mkConst ``Lynth.Sat.checkSat []) body2) mm)
                  (mkConst ``Bool.true [])
                mkLambdaFVars #[mm] stmt
              let wit ← mkExpectedTypeHint fullProof
                (mkApp exPred mod)
              let exM := mkAppN (mkConst ``Exists.intro [Level.succ Level.zero])
                #[aty2, exPred, mod, wit]
              mkLambdaFVars #[gin, f, hPf] exM
        -- goal assembly: prove the three `Correctness` conjuncts
        -- about `solverVal` via `runSolver_*`, then close
        let hct ← inferType hcomp
        let specApp := mkApp shape.pred solverVal
        let specR ← whnf specApp
        let spec3 := splitAnd3 specR
        let (sC, cC, nC) ← match spec3 with
          | some t => pure t
          | none => throwError "resplit"
        let soundPf ← forallTelescope sC fun fvs sbody => do
          if fvs.size != 3 then throwError "sound goal shape"
          else
            let q ← mkAppM ``Lynth.Sat.Compile.runSolver_sound
              #[encode, decode, P,
                mkNatLit compileFuel, mkNatLit compileRestart,
                hsound, fvs[0]!, fvs[1]!, fvs[2]!]
            let qh ← mkExpectedTypeHint q sbody
            mkLambdaFVars fvs qh
        let completePf ← forallTelescope cC fun fvs cbody => do
          if fvs.size != 2 then throwError "complete goal shape"
          else
            let q ← mkAppM ``Lynth.Sat.Compile.runSolver_complete
              #[encode, decode, P,
                mkNatLit compileFuel, mkNatLit compileRestart,
                hcomp, fvs[0]!, fvs[1]!]
            let qh ← mkExpectedTypeHint q cbody
            mkLambdaFVars fvs qh
        let nonePf ← forallTelescope nC fun fvs nbody => do
          if fvs.size != 1 then throwError "none goal shape"
          else
            let q ← mkAppM ``Lynth.Sat.Compile.runSolver_none
              #[encode, decode, P,
                mkNatLit compileFuel, mkNatLit compileRestart,
                hsound, hcomp, fvs[0]!]
            let qh ← mkExpectedTypeHint q nbody
            mkLambdaFVars fvs qh
        let pfCC ← mkAppM ``And.intro #[completePf, nonePf]
        let pf ← mkAppM ``And.intro #[soundPf, pfCC]
        let pfH ← mkExpectedTypeHint pf specApp
        let val ← shape.mkVal solverVal pfH
        (← getMainGoal).assign val
        pure true
    if ok then return true else return false
  catch e => throw e

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
