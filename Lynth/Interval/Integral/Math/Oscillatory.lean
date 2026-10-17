import Mathlib

/-! Cancellation bounds near a reciprocal-phase endpoint. This theorem is
independent of the interval implementation and is mirrored in /tmp/intgrl. -/

namespace Intgrl

/-- Substitution followed by integration by parts gains one power of the
endpoint compared with the pointwise bound. The value at zero is immaterial. -/
theorem reciprocal_sin_endpoint (n : ℕ) {ω δ : ℝ} (hω : ω ≠ 0) (hδ : 0 ≤ δ) :
    IntervalIntegrable (fun x : ℝ => x^n * Real.sin (ω/x))
      MeasureTheory.volume 0 δ ∧
      |(∫ x in (0 : ℝ)..δ, x^n * Real.sin (ω/x))| ≤ 2*δ^(n+2)/|ω| := by
  sorry

end Intgrl
