import Mathlib

/-! Mathematical lemmas for endpoint envelopes and parameter integrals.
This file imports only Mathlib and is copied verbatim to `/tmp/intgrl`.
There are no interval representations, expression evaluators or certificates
in these statements. -/
noncomputable section
open MeasureTheory
open scoped Topology

namespace Intgrl

/-- Absorb logarithmic growth into half of a positive endpoint power. -/
theorem power_log_absorb {t p : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hp : 0 < p) (m : ℕ) :
    t^p * (1 - Real.log t)^m ≤
      (2:ℝ)^m * (1 + (m.factorial:ℝ) / (p/2)^m) * t^(p/2) := by
  sorry

/-- The real logarithm uses the same branch on either side of zero. -/
theorem real_log_scaled_bound {t p a : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |Real.log (t^p * a)| ≤ (|p| + |Real.log a|) * (1 - Real.log t) := by
  sorry

/-- Uniform exponential decay, including complex coefficients. -/
theorem complex_exp_scaled_bound {t p C : ℝ} {z : ℂ}
    (ht : 0 < t) (hC : 0 < C) (hz : z.re ≤ -C) (n : ℕ) :
    ‖Complex.exp (((t^p:ℝ):ℂ) * z)‖ ≤
      ((n.factorial:ℝ) / C^n) * t^((-p)*(n:ℝ)) := by
  sorry

theorem real_rpow_scaled {t p a q : ℝ} (ht : 0 < t) (ha : 0 < a) :
    (t^p * a)^q = t^(p*q) * a^q := by
  sorry

/-- Positive real scaling does not cross the principal logarithm cut. -/
theorem complex_log_scaled_bound {t p : ℝ} {z : ℂ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hz : z ≠ 0) :
    ‖Complex.log (((t^p:ℝ):ℂ) * z)‖ ≤
      (|p| + ‖Complex.log z‖) * (1 - Real.log t) := by
  sorry

/-- A bounded complex integral has a mean in the same closed rectangle. -/
theorem complex_integral_rectangle_mean {F : ℝ → ℂ} {a b l u v w : ℝ}
    (hab : a ≤ b) (hlu : l ≤ u) (hvw : v ≤ w) (hm : Measurable F)
    (hF : ∀ x ∈ Set.Ioo a b, (F x).re ∈ Set.Icc l u ∧ (F x).im ∈ Set.Icc v w) :
    IntervalIntegrable F volume a b ∧ ∃ z : ℂ,
      z.re ∈ Set.Icc l u ∧ z.im ∈ Set.Icc v w ∧
      (∫ x in a..b, F x) = ((b-a:ℝ):ℂ) * z := by
  sorry

/-- Oriented affine substitution also covers reversed and zero-width intervals. -/
theorem finite_affine_integrable {F : ℝ → ℝ} {a b : ℝ} (hm : Measurable F) :
    IntervalIntegrable F volume a b ↔
      IntervalIntegrable (fun t : ℝ => (b-a) * F (a+(b-a)*t)) volume 0 1 := by
  sorry

theorem finite_affine_value {F : ℝ → ℝ} {a b : ℝ}
    (hi : IntervalIntegrable F volume a b) :
    (∫ x in a..b, F x) = ∫ t in (0:ℝ)..1, (b-a) * F (a+(b-a)*t) := by
  sorry

/-- The constant in a bounded-interval remainder estimate need not be sharp. -/
theorem interval_remainder_bound {F : ℝ → ℝ} {a b M : ℝ}
    (hm : Measurable F) (hM : 0 ≤ M)
    (hF : ∀ x ∈ Set.uIoo a b, |F x| ≤ M) :
    IntervalIntegrable F volume a b ∧ |∫ x in a..b, F x| ≤ |b-a| * M := by
  sorry

/-- Assemble a truncated integral with two integrable endpoint remainders. -/
theorem endpoint_truncation {F : ℝ → ℂ} {a b L R : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (hl : IntervalIntegrable F volume 0 a) (hm : IntervalIntegrable F volume a b)
    (hr : IntervalIntegrable F volume b 1)
    (hL : ‖∫ t in (0:ℝ)..a, F t‖ ≤ L) (hR : ‖∫ t in b..(1:ℝ), F t‖ ≤ R) :
    IntervalIntegrable F volume 0 1 ∧
      ‖(∫ t in (0:ℝ)..1, F t) - (∫ t in a..b, F t)‖ ≤ L+R := by
  sorry

/-- General parameter spaces are necessary for genuinely nested integrals. -/
theorem parametric_finite_analytic_nd {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {S : Set E} {F : E → ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : E × ℂ => F p.1 p.2)
      (S ×ˢ (Complex.ofReal '' Set.Icc (0:ℝ) 1))) :
    AnalyticOnNhd ℂ (fun z => ∫ t in (0:ℝ)..1, F z t) S := by
  sorry

/-- Uniform power/log majorants justify holomorphic dependence through an
improper inner integral; pointwise convergence is not a sufficient hypothesis. -/
theorem parametric_endpoint_analytic_nd {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} (hU : IsOpen U) {F : E → ℂ → ℂ}
    {δ p q C D : ℝ} {m n : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hp : -1 < p) (hq : -1 < q) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : AnalyticOnNhd ℂ (fun s : E × ℂ => F s.1 s.2)
      (U ×ˢ (Complex.ofReal '' Set.Ioo (0:ℝ) 1)))
    (hleft : ∀ z ∈ U, ∀ t ∈ Set.Ioo (0:ℝ) δ,
      ‖F z t‖ ≤ C*t^p*(1-Real.log t)^m)
    (hright : ∀ z ∈ U, ∀ t ∈ Set.Ioo (0:ℝ) δ,
      ‖F z (1-t)‖ ≤ D*t^q*(1-Real.log t)^n) :
    AnalyticOnNhd ℂ (fun z => ∫ t in (0:ℝ)..1, F z t) U ∧
      ∀ z ∈ U, IntervalIntegrable (fun t : ℝ => F z t) volume 0 1 := by
  sorry

end Intgrl
