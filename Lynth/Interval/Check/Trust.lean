import Lean
import Lynth.Interval.Core.Const
import Lynth.Interval.Core.Prop

/-!
# Trust driver: discharging `check … = true`

`kernel`: an auxiliary theorem with value `Eq.refl true` (the kernel evaluates
the check; axioms stay `[propext, Classical.choice, Quot.sound]`).
`native`: the `native_decide` tactic (adds a per-declaration auxiliary axiom).
`auto`: kernel when the cost estimate is below `lynth.interval.kernelBudget`.
See `docs/interval/01-architecture.md §5`.
-/

namespace Lynth.Interval

inductive Trust | kernel | native | auto
deriving Repr, DecidableEq, Inhabited

register_option lynth.interval.trust : String := {
  defValue := "auto"
  descr := "lynth interval certificates: kernel | native | auto"
}

register_option lynth.interval.kernelBudget : Nat := {
  defValue := 400000
  descr := "cost units allowed for kernel checking in `auto` mode"
}

register_option lynth.interval.maxPrec : Nat := {
  defValue := 4096
  descr := "maximal working precision (bits) tried by the interval procedure"
}

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
def certify (lhs : Lean.Expr) (cost : Nat) : TacticM Lean.Expr := do
  let goal ← mkEq lhs (mkConst ``Bool.true)
  match ← effectiveTrust cost with
  | .native =>
    let m ← mkFreshExprSyntheticOpaqueMVar goal
    let gs ← Tactic.run m.mvarId! (evalTactic (← `(tactic| native_decide)))
    unless gs.isEmpty do throwError "lynth interval: native_decide left goals"
    instantiateMVars m
  | _ =>
    let pf := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    let name ← mkAuxLemma [] goal pf (kind? := `lynth_interval_cert)
    return mkConst name

end Lynth.Interval
