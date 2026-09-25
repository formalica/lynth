import Mathlib
import Lynth

namespace IntervalArith

noncomputable def derivativeAt
    (f : ℝ → ℝ) (k : Nat) (z : ℝ) : ℝ :=
  Function.iterate deriv k f z

/-- The rational coefficients approximate the Taylor coefficients
`f^(k)(z) / k!`. -/
def TaylorCoefficientSpec
    (f : ℝ → ℝ) (z : ℝ) (n : Nat) (tol : ℝ)
    (c : Fin (n + 1) → Rat) : Prop :=
  ∀ k : Fin (n + 1),
    abs (derivativeAt f k.val z -
      (Nat.factorial k.val : ℝ) * (c k : ℝ)) <
      tol

/-- T01 — first thirteen Taylor coefficients of `exp (cos x)` at `z = 1`. -/
def taylorMeta :
    { c : Fin 13 → Rat //
      TaylorCoefficientSpec
        (fun x : ℝ => Real.exp (Real.cos x))
        1
        12
        (1 / 100000000)
        c } := by
  lynth

#eval taylorMeta.1

/-- info: 'IntervalArith.derivativeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms derivativeAt

/-- info: 'IntervalArith.TaylorCoefficientSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TaylorCoefficientSpec

/-- info: 'IntervalArith.taylorMeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms taylorMeta

end IntervalArith
