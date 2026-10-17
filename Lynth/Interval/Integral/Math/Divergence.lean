import Mathlib

/-!
P2: proof-producing divergence, entirely standalone.
No quadrature timeout or non-finite enclosure is evidence of divergence.
Basic reciprocal cases already have Mathlib lemmas; these comparisons
cover products and changes of variables without hard-coded integral values.
-/

noncomputable section

open MeasureTheory

namespace Intgrl

theorem not_integrable_endpoint_of_inv_lower {f : ℝ → ℝ} {b C : ℝ}
    (hb : 0 < b) (hC : 0 < C)
    (hbound : ∀ t ∈ Set.Ioo 0 b, C / t ≤ |f t|) :
    ¬ IntegrableOn f (Set.Ioo 0 b) volume := by
  sorry

theorem not_integrable_tail_of_inv_lower {f : ℝ → ℝ} {R C : ℝ}
    (hR : 0 < R) (hC : 0 < C)
    (hbound : ∀ t ∈ Set.Ioi R, C / t ≤ |f t|) :
    ¬ IntegrableOn f (Set.Ioi R) volume := by
  sorry

theorem not_intervalIntegrable_tan :
    ¬ IntervalIntegrable Real.tan volume 0 (Real.pi / 2) := by
  sorry

/-- A positive integral of the norm on every period rules out absolute integrability. -/
theorem not_integrable_periodic_tail {f : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T) (hperiodic : Function.Periodic f T)
    (hint : IntervalIntegrable f volume 0 T)
    (hpositive : 0 < ∫ t in (0 : ℝ)..T, |f t|) (R : ℝ) :
    ¬ IntegrableOn f (Set.Ioi R) volume := by
  sorry

end Intgrl
