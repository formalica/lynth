import Lynth.Interval.Integral.Math.Integrand
import Lynth.Interval.Integral.Math.Divergence

/-! Portable semantic rules for recognized non-integrable families. -/

namespace Intgrl

inductive DivergenceRule where
  | invPower (n : ℕ)
  | shiftedInv (q : ℚ)
  | tangent
  | constant (q : ℚ)
  | linear | sine | exponential
deriving Repr, Inhabited

def classifyDivergence : Term → Option DivergenceRule
  | .unary .inv .var => some (.invPower 1)
  | .unary .inv (.pow .var n) => if 0 < n then some (.invPower n) else none
  | .binary .div (.rat q) .var =>
      if q == 1 then some (.invPower 1) else none
  | .binary .div (.rat q) (.pow .var n) =>
      if q == 1 && n > 0 then some (.invPower n) else none
  | .binary .div (.rat q) (.binary .sub (.rat p) .var) =>
      if q == 1 then some (.shiftedInv p) else none
  | .unary .inv (.binary .sub (.rat p) .var) => some (.shiftedInv p)
  | .binary .div (.unary .sin .var) (.unary .cos .var) => some .tangent
  | .rat q => if q != 0 then some (.constant q) else none
  | .var => some .linear
  | .unary .sin .var => some .sine
  | .unary .exp .var => some .exponential
  | _ => none

def Region.isFinite : Region → Bool
  | .interval | .icc | .ioc | .ico | .ioo => true
  | _ => false

def DivergenceRule.Condition (r : DivergenceRule) (k : Region) (a b : ℝ) : Prop :=
  match r with
  | .invPower n =>
    if k.isFinite then a < b ∧ a ≤ 0 ∧ 0 ≤ b ∧ 0 < n
    else if k == .univ then 0 < n
    else n = 1 ∨ (a ≤ 0 ∧ 0 < n)
  | .shiftedInv q =>
    if k.isFinite then a < b ∧ a ≤ q ∧ (q : ℝ) ≤ b
    else True
  | .tangent =>
    if k.isFinite then a < b ∧ a ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ b
    else True
  | _ => ¬ k.isFinite

theorem divergenceRule_sound {e : Term} {r : DivergenceRule}
    (hclass : classifyDivergence e = some r)
    {k : Region} {a b : ℝ} (h : r.Condition k a b) :
    ¬ k.Converges e.real a b := by
  sorry

end Intgrl
