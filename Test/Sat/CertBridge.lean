import Lynth
import Lynth.Sat.Cert

/-!
Certificates from the verified solver (`Lynth.Sat.Cert` over the
temporary axiom `Lynth.Sat.cdcl_correct`).

`cert_unsat` closes `∀ a, checkSat <cnf> a = false` and `cert_sat`
proves `∃ m, checkSat <cnf> m = true`, both through solver evidence
(`native_decide`) plus the soundness/completeness theorems. The pinned
axioms below are the whole point: every proof here must bottom out in
the solver axiom plus generated native-evaluation axioms (and core
axioms) — never `sorryAx`.
-/
open Lean Elab Tactic Meta
open Lynth.Sat
open Lynth.Sat.Cert

/-- Extract `cnfE` from a goal `∀ a, checkSat cnfE a = false`. -/
private def unsatGoalCNF : TacticM (Option Expr) := do
  let goal ← whnf (← getMainTarget)
  match goal with
  | .forallE _ _ _ _ =>
    forallTelescope goal fun xs body => do
      if xs.size != 1 then pure none
      else
        let c ← whnf body
        match c.getAppFn with
        | .const ``Eq _ =>
          let args := c.getAppArgs
          if args.size < 2 then pure none
          else
            -- NOTE: no `whnf` on the sides: it would unfold `checkSat`
            -- itself and hide the head being matched
            let lhs := args[args.size - 2]!
            match lhs.getAppFn with
            | .const n _ =>
              if n == ``checkSat then
                let cargs := lhs.getAppArgs
                if cargs.size < 2 then pure none
                else pure (some cargs[cargs.size - 2]!)
              else pure none
            | _ => pure none
        | _ => pure none
  | _ => pure none

/-- Close `∀ a, checkSat <cnf> a = false` by solver + completeness. -/
elab "cert_unsat" : tactic => do
  match ← unsatGoalCNF with
  | none => throwError "cert_unsat: goal must be ∀ a, checkSat <closed-cnf> a = false"
  | some cnfE =>
    let g ← getMainGoal
    if !(← unsatCertGoal cnfE g) then
      throwError "cert_unsat: solver did not certify UNSAT"

/-- Extract `(predE, cnfE)` from a goal `∃ m, checkSat cnfE m = true`. -/
private def satGoalCNF : TacticM (Option (Expr × Expr)) := do
  let goal ← whnf (← getMainTarget)
  match goal.getAppFn with
  | .const ``Exists _ =>
    let args := goal.getAppArgs
    if args.size != 2 then pure none
    else
      -- NOTE: the `Exists` predicate is a *lambda*, not a forall
      lambdaTelescope args[1]! fun xs body => do
        if xs.size != 1 then pure none
        else
          let c ← whnf body
          match c.getAppFn with
          | .const ``Eq _ =>
            let eargs := c.getAppArgs
            if eargs.size < 2 then pure none
            else
              -- NOTE: no `whnf` on the side (see `unsatGoalCNF`)
              let lhs := eargs[eargs.size - 2]!
              match lhs.getAppFn with
              | .const n _ =>
                if n == ``checkSat then
                  let cargs := lhs.getAppArgs
                  if cargs.size < 2 then pure none
                  else pure (some (args[1]!, cargs[cargs.size - 2]!))
                else pure none
              | _ => pure none
          | _ => pure none
  | _ => pure none

/-- The `Assignment` type expression (mirrors `Cert.assignmentTy`). -/
private def certAssignTy : Expr :=
  mkApp (mkConst ``List [Level.zero])
    (mkApp (mkConst ``Option [Level.zero]) (mkConst ``Bool []))

/-- Prove `∃ m, checkSat <cnf> m = true` by solver + soundness. -/
elab "cert_sat" : tactic => do
  match ← satGoalCNF with
  | none => throwError "cert_sat: goal must be ∃ m, checkSat <closed-cnf> m = true"
  | some (predE, cnfE) =>
    match ← satCert cnfE with
    | none => throwError "cert_sat: solver did not certify SAT"
    | some (m, prf) =>
      -- explicit predicate: higher-order unification will not infer it
      -- (`Exists` lives in `Sort 1` for `Type`-sorted domains)
      let g ← getMainGoal
      let u := Level.succ Level.zero
      let wit := toExpr m
      let full := mkApp (mkApp (mkApp (mkApp (mkConst ``Exists.intro [u])
        certAssignTy) predE) wit) prf
      g.assign full

/-- Unit clash, certified UNSAT. -/
theorem unsat_unit : ∀ _a : Assignment, checkSat [[1], [-1]] _a = false := by
  cert_unsat

/-- Pigeonhole (3 pigeons, 2 holes), certified UNSAT. -/
theorem unsat_php32 : ∀ _a : Assignment, checkSat
    [[1, 2], [3, 4], [5, 6], [-1, -3], [-1, -5], [-3, -5],
     [-2, -4], [-2, -6], [-4, -6]] _a = false := by
  cert_unsat

/-- Trivial SAT, certified with model. -/
theorem sat_unit : ∃ _m : Assignment, checkSat [[1], [2]] _m = true := by
  cert_sat

/-- info: 'unsat_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cdcl_correct,
 unsat_unit._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms unsat_unit

/-- info: 'unsat_php32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cdcl_correct,
 unsat_php32._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms unsat_php32

/-- info: 'sat_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cdcl_correct,
 sat_unit._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms sat_unit
