import Lynth.Interval.Check.Trust
import Lynth.Interval.Reify.Reify

/-!
# Closed propositions

`P` built from `< ≤ > ≥ ∧ ∨ ¬ →` over closed real expressions is reified to a
`PropExpr`, checked natively at increasing precision, and certified.
See `docs/interval/05-point-goals.md §1`.
-/

namespace Lynth.Interval.Goals

open Lean Meta Elab Tactic Reify

unsafe def evalPropExprUnsafe (e : Lean.Expr) : MetaM PropExpr :=
  evalExpr PropExpr (mkConst ``PropExpr) e

/-- runtime value of a reified `PropExpr` term -/
@[implemented_by evalPropExprUnsafe] opaque evalPropExpr (e : Lean.Expr) : MetaM PropExpr

def precSchedule (maxPrec : Nat) : List Nat :=
  [64, 96, 128, 192, 256, 384, 512, 768, 1024, 1536, 2048, 3072, 4096, 6144, 8192, 12288,
    16384, 24576, 32768, 49152, 65536].filter (· ≤ maxPrec)

/-- smallest scheduled precision at which `p` checks -/
def findPrec (p : PropExpr) (σ : IEnv := {}) : CoreM (Option Nat) := do
  let maxPrec := lynth.interval.maxPrec.get (← getOptions)
  for prec in precSchedule maxPrec do
    if p.check (Ctx.make prec) σ then return some prec
  return none

def emptyIEnvExpr : Lean.Expr :=
  mkApp3 (mkConst ``IEnv.mk) (mkApp (mkConst ``List.nil [0]) (mkConst ``NIval))
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Ival)) (mkApp (mkConst ``List.nil [0]) (mkConst ``CBox))

/-- rough cost of checking at precision `prec` (kernel budget units) -/
def checkCost (prec : Nat) (size : Nat) : Nat := size * (prec / 64 + 1) ^ 2

/-- Prove the closed proposition `P`, or return `none`. -/
def proveClosed? (P : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let rp ← reifyProp {} P
  let pv ← evalPropExpr rp.expr
  let some prec ← findPrec pv | return none
  let ctxE := mkApp (mkConst ``Ctx.make) (mkNatLit prec)
  let lhs := mkApp3 (mkConst ``PropExpr.check) ctxE rp.expr emptyIEnvExpr
  let h ← certify lhs (checkCost prec (rp.expr.approxDepth.toNat * 8))
  return some <| mkAppN (mkConst ``PropExpr.of_check)
    #[P, rp.expr, ctxE, mkApp (mkConst ``Ctx.make_valid) (mkNatLit prec), rp.proof, h]

end Lynth.Interval.Goals
