module

import Lean
import Lynth.Interval.Check.ReductionLemmas
import Lynth.Options
import all Lynth.Interval.Core.Const
import all Lynth.Interval.Core.Prop

/-!
# Trust driver: discharging `check … = true`

`kernel`: an auxiliary theorem checked by the kernel. Shared library lemmas
handle opaque core operations; executable checkers are unchanged.
`native`: the `native_decide` tactic (adds a per-declaration auxiliary axiom).
`auto`: kernel when the cost estimate is below `lynth.interval.kernelBudget`.
See `docs/interval/01-architecture.md §5`.
-/

namespace Lynth.Interval

inductive Trust | kernel | native | auto
deriving Repr, DecidableEq, Inhabited


def Trust.ofString : String → Trust
  | "kernel" => .kernel
  | "native" => .native
  | _ => .auto

open Lean Meta Elab Tactic

unsafe def evalBoolUnsafe (e : Lean.Expr) : MetaM Bool := evalExpr Bool (mkConst ``Bool) e

/-- run a closed `Bool` term natively (compiled / interpreted) -/
@[implemented_by evalBoolUnsafe] opaque evalBool (e : Lean.Expr) : MetaM Bool

def getTrust : CoreM Trust := do
  return Trust.ofString (lynth.interval.trust.get (← getOptions))

/-- effective trust mode for a certificate of estimated `cost` -/
def effectiveTrust (cost : Nat) : CoreM Trust := do
  match ← getTrust with
  | .auto => return if cost ≤ lynth.interval.kernelBudget.get (← getOptions) then .kernel else .native
  | t => return t

/-- proof of `lhs = true` for a closed Bool term `lhs` -/
private partial def kernelEvidence (lhs : Lean.Expr) : MetaM Lean.Expr := do
  let reflexivity ← mkEqRefl (mkConst ``Bool.true)
  -- These lemmas contain the compatibility proofs checked at library build time.
  -- Applying one does not rebuild any checker equivalences in this certificate.
  for (checker, theoremName) in [
      (``Integral.integralCheck, ``CheckReduction.integralCheck),
      (``Integral.Nested.check, ``CheckReduction.nestedCheck),
      (``Composition.integralCheck, ``CheckReduction.compositionCheck),
      (``Integral.divergenceCheck, ``CheckReduction.divergenceCheck)] do
    if lhs.isAppOf checker then
      return mkApp (mkAppN (mkConst theoremName) lhs.getAppArgs) reflexivity
  -- Eta records can occur inside arbitrary reified propositions. Abstract just
  -- the record occurrence; the shared lemma provides its compatibility proof.
  for (record, theoremName) in [
      (``Fns.etaR, ``CheckReduction.etaR), (``Fns.etaC, ``CheckReduction.etaC)] do
    if lhs.getUsedConstants.contains record then
      let original := mkConst record
      let context := .lam `function (← inferType original) (lhs.abstract #[original]) .default
      let applied := mkApp (mkConst theoremName) context
      let .forallE _ hypothesis _ _ ← inferType applied
        | throwError "lynth interval: invalid shared kernel lemma"
      let proof ← forallTelescope hypothesis fun ps result => do
        let some (_, reduced, _) := result.eq?
          | throwError "lynth interval: invalid shared kernel premise"
        mkLambdaFVars ps (← kernelEvidence reduced)
      return mkApp applied proof
  return reflexivity

/-- proof of `lhs = true` for a closed Bool term `lhs` -/
def certify (lhs : Lean.Expr) (cost : Nat) : TacticM Lean.Expr := do
  let goal ← mkEq lhs (mkConst ``Bool.true)
  match ← effectiveTrust cost with
  | .native =>
    let m ← mkFreshExprSyntheticOpaqueMVar goal
    let gs ← Tactic.run m.mvarId! (evalTactic (← `(tactic| native_decide)))
    unless gs.isEmpty do throwError "lynth interval: native_decide left goals"
    instantiateMVars m
  | _ =>
    let pf ← kernelEvidence lhs
    let name ← mkAuxLemma [] goal pf (kind? := `lynth_interval_cert)
    return mkConst name

end Lynth.Interval
