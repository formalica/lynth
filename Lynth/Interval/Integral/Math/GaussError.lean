import Lynth.Interval.Integral.Math.IntgrlDefs

/-!
P0: analytic error bound, real affine specialization, and ellipse geometry.
Send with IntgrlDefs.lean. Legendre.lean is useful proof material, but is
not needed to elaborate the statements.

Target: FLINT src/acb_calc/integrate_gl_auto_deg.c and its acb_calc docs.
The unit rule has n nodes, not n+1. The half-length factor must occur once.
Use the stronger classical bound with (1-rho^(-2))*rho^(2*n) if convenient,
then weaken it to glError.
-/

noncomputable section

open scoped BigOperators

namespace Intgrl

theorem ellipse_in_rectangle {ρ : ℝ} (hρ : 1 < ρ) {z : ℂ}
    (hz : z ∈ ellipse ρ) :
    |z.re| ≤ ellipseX ρ ∧ |z.im| ≤ ellipseY ρ := by
  sorry

theorem real_mem_ellipse {ρ t : ℝ} (hρ : 1 < ρ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (t : ℂ) ∈ ellipse ρ := by
  sorry

theorem gauss_error_complex {n : ℕ} (hn : 0 < n)
    {x : Fin n → ℝ} (hx : IsGaussNodes x)
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ) (hM : 0 ≤ M)
    (hF : AnalyticOnNhd ℂ F (ellipse ρ))
    (hbound : ∀ z ∈ ellipse ρ, ‖F z‖ ≤ M) :
    IntervalIntegrable (fun t : ℝ => F t) MeasureTheory.volume (-1) 1 ∧
      ‖(∫ t in (-1 : ℝ)..1, F t) - gaussSumC x F‖ ≤ glError n ρ M := by
  sorry

theorem gauss_error_real_affine {n : ℕ} (hn : 0 < n)
    {x : Fin n → ℝ} (hx : IsGaussNodes x)
    {f : ℝ → ℝ} {F : ℂ → ℂ} {a b ρ M : ℝ}
    (hab : a < b) (hρ : 1 < ρ) (hM : 0 ≤ M)
    (hF : AnalyticOnNhd ℂ F ((affine a b) '' ellipse ρ))
    (hbound : ∀ z ∈ ellipse ρ, ‖F (affine a b z)‖ ≤ M)
    (hagrees : ∀ t ∈ Set.Ioo a b, F t = (f t : ℂ)) :
    IntervalIntegrable f MeasureTheory.volume a b ∧
      |(∫ t in a..b, f t) -
        ((b - a) / 2) *
          gaussSum x (fun t => f ((a + b) / 2 + (b - a) / 2 * t))|
        ≤ glError n ρ (((b - a) / 2) * M) := by
  sorry

end Intgrl
