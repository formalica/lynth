import Mathlib
import Lynth

namespace IntervalArith

/-- D01 — approximate the derivative of `exp (cos x)` at `x = 1`.
Etalon expression: `-sin 1 * exp (cos 1)`. -/
def derivativeExpCos :
    { d : Rat //
      abs (deriv (fun x : ℝ => Real.exp (Real.cos x)) 1 -
        (d : ℝ)) < 1 / 1000000 } := by
  lynth

/-- D02 — approximate the derivative of `x^3 * sin x` at `x = 1/2`.
Etalon expression: `3x^2 * sin x + x^3 * cos x` at `x = 1/2`. -/
def derivativeQuarticSin :
    { d : Rat //
      abs (deriv (fun x : ℝ => x ^ 3 * Real.sin x) (1 / 2) -
        (d : ℝ)) < 1 / 1000000 } := by
  lynth

/-- The high-level solution relation for an initial-value problem. -/
def ODESolution
    (rhs : ℝ → ℝ → ℝ)
    (t₀ y₀ : ℝ)
    (y : ℝ → ℝ) : Prop :=
  y t₀ = y₀ ∧
  ∀ t : ℝ, HasDerivAt y (rhs t (y t)) t

/-- D03 — approximate the solution of `y' = y`, `y(0) = 1`, at `t = 1`.
Etalon: `exp 1`. -/
def odeExpGoal :
    { x : Rat //
      ∃ y : ℝ → ℝ,
        ODESolution (fun _ v => v) 0 1 y ∧
        abs (y 1 - (x : ℝ)) < 1 / 10000 } := by
  lynth

#eval derivativeExpCos.1
#eval derivativeQuarticSin.1
#eval odeExpGoal.1

/-- info: 'IntervalArith.derivativeExpCos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms derivativeExpCos

/-- info: 'IntervalArith.derivativeQuarticSin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms derivativeQuarticSin

/-- info: 'IntervalArith.ODESolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ODESolution

/-- info: 'IntervalArith.odeExpGoal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odeExpGoal

end IntervalArith
