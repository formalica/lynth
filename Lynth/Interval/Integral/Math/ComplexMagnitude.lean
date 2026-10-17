import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.Linarith

/-! Modulus bounds that avoid evaluating the real trigonometric phase. -/

namespace Intgrl

theorem norm_sin_le_cosh_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.cosh z.im := by
  have h := norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
  have h' : 2 * ‖Complex.sin z‖ ≤ Real.exp z.im + Real.exp (-z.im) := by
    calc
      2 * ‖Complex.sin z‖ = ‖(2 : ℂ) * Complex.sin z‖ := by simp
      _ = ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ := by
        rw [Complex.two_sin, norm_mul, Complex.norm_I, mul_one]
      _ ≤ ‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖ := h
      _ = _ := by simp [Complex.norm_exp, Complex.mul_re]
  rw [Real.cosh_eq]
  linarith

theorem norm_cos_le_cosh_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  have h' : 2 * ‖Complex.cos z‖ ≤ Real.exp (-z.im) + Real.exp z.im := by
    calc
      2 * ‖Complex.cos z‖ = ‖(2 : ℂ) * Complex.cos z‖ := by simp
      _ = ‖Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)‖ := by
        rw [Complex.two_cos]
      _ ≤ ‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-z * Complex.I)‖ := norm_add_le _ _
      _ = _ := by simp [Complex.norm_exp, Complex.mul_re]
  rw [Real.cosh_eq]
  linarith

theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  have h1 := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 := Real.exp_le_exp.mpr (neg_le_abs x)
  rw [Real.cosh_eq]
  linarith

theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| :=
  (norm_sin_le_cosh_im z).trans (cosh_le_exp_abs z.im)

theorem norm_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| :=
  (norm_cos_le_cosh_im z).trans (cosh_le_exp_abs z.im)

end Intgrl
