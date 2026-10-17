import Mathlib

/-!
P0/P2: direct bounds, piece assembly, uncertain endpoints and improper tails.
Entirely standalone. Keep measurable/integrable assumptions explicit:
boundedness alone is not a proof of Lebesgue integrability.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Intgrl

theorem direct_enclosure {f : ℝ → ℝ} {a b lo hi : ℝ}
    (hab : a ≤ b) (hm : Measurable f)
    (hbound : ∀ t ∈ Set.Icc a b, f t ∈ Set.Icc lo hi) :
    IntervalIntegrable f volume a b ∧
      (∫ t in a..b, f t) ∈ Set.Icc ((b - a) * lo) ((b - a) * hi) := by
  sorry

/-- Endpoint values have zero measure; this version permits piecewise analytic
branches such as floor(x) on an interval with integer endpoints. -/
theorem direct_enclosure_open {f : ℝ → ℝ} {a b lo hi : ℝ}
    (hab : a ≤ b) (hm : Measurable f)
    (hbound : ∀ t ∈ Set.Ioo a b, f t ∈ Set.Icc lo hi) :
    IntervalIntegrable f volume a b ∧
      (∫ t in a..b, f t) ∈ Set.Icc ((b - a) * lo) ((b - a) * hi) := by
  sorry

theorem partition_error {n : ℕ} {p : ℕ → ℝ} {f : ℝ → ℝ} {q e : ℕ → ℝ}
    (hp : ∀ k < n, p k ≤ p (k + 1))
    (hint : ∀ k < n, IntervalIntegrable f volume (p k) (p (k + 1)))
    (herr : ∀ k < n, |(∫ t in p k..p (k + 1), f t) - q k| ≤ e k) :
    IntervalIntegrable f volume (p 0) (p n) ∧
      |(∫ t in p 0..p n, f t) - ∑ k ∈ Finset.range n, q k|
        ≤ ∑ k ∈ Finset.range n, e k := by
  sorry

theorem uncertain_endpoints {f : ℝ → ℝ} {a b a₀ b₀ M εa εb : ℝ}
    (ha : |a - a₀| ≤ εa) (hb : |b - b₀| ≤ εb) (hM : 0 ≤ M)
    (hintA : IntervalIntegrable f volume a a₀)
    (hintMid : IntervalIntegrable f volume a₀ b₀)
    (hintB : IntervalIntegrable f volume b₀ b)
    (hboundA : ∀ t ∈ Set.uIcc a a₀, |f t| ≤ M)
    (hboundB : ∀ t ∈ Set.uIcc b b₀, |f t| ≤ M) :
    IntervalIntegrable f volume a b ∧
      |(∫ t in a..b, f t) - (∫ t in a₀..b₀, f t)| ≤ M * (εa + εb) := by
  sorry

theorem halfline_truncation {f g : ℝ → ℝ} {a R T : ℝ}
    (haR : a ≤ R) (hm : Measurable f)
    (hfinite : IntervalIntegrable f volume a R)
    (hg : IntegrableOn g (Set.Ioi R) volume)
    (hmajorant : ∀ t ∈ Set.Ioi R, |f t| ≤ g t)
    (hT : (∫ t in Set.Ioi R, g t) ≤ T) :
    IntegrableOn f (Set.Ioi a) volume ∧
      |(∫ t in Set.Ioi a, f t) - (∫ t in a..R, f t)| ≤ T := by
  sorry

theorem power_endpoint {f : ℝ → ℝ} {b C α : ℝ}
    (hb : 0 < b) (hC : 0 ≤ C) (hα : -1 < α) (hm : Measurable f)
    (hbound : ∀ t ∈ Set.Ioo 0 b, |f t| ≤ C * t ^ α) :
    IntegrableOn f (Set.Ioo 0 b) volume ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ b →
        |(∫ t in Set.Ioo 0 ε, f t)| ≤ C * ε ^ (α + 1) / (α + 1) := by
  sorry

theorem gaussian_tail {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2))) (Set.Ioi R) volume ∧
      (∫ t in Set.Ioi R, Real.exp (-(t ^ 2))) ≤ Real.exp (-(R ^ 2)) / (2 * R) := by
  sorry

/-- Together with gaussian_tail and the elementary k=1 tail, bounds polynomial Gaussians. -/
theorem gaussian_power_tail (k : ℕ) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2)) * t ^ k)
      (Set.Ioi R) volume ∧
      (∫ t in Set.Ioi R, Real.exp (-(t ^ 2)) * t ^ (k + 2)) =
        (R ^ (k + 1) * Real.exp (-(R ^ 2)) +
          ((k : ℝ) + 1) *
            (∫ t in Set.Ioi R, Real.exp (-(t ^ 2)) * t ^ k)) / 2 := by
  sorry

theorem exp_power_tail (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ k) (Set.Ioi R) volume ∧
      (∫ t in Set.Ioi R, Real.exp (-t) * t ^ k) =
        Real.exp (-R) *
          ∑ j ∈ Finset.range (k + 1),
            ((Nat.factorial k : ℝ) / (Nat.factorial j : ℝ)) * R ^ j := by
  sorry

theorem log_endpoint {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IntegrableOn Real.log (Set.Ioo 0 ε) volume ∧
      |(∫ t in Set.Ioo 0 ε, Real.log t)| = ε * (1 - Real.log ε) := by
  sorry

theorem power_tail {C α R : ℝ} (hC : 0 ≤ C) (hα : 1 < α) (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => C * t ^ (-α)) (Set.Ioi R) volume ∧
      (∫ t in Set.Ioi R, C * t ^ (-α)) = C * R ^ (1 - α) / (α - 1) := by
  sorry

theorem sech_power_tail (k : ℕ) (hk : 0 < k) {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun t : ℝ => (Real.cosh t)⁻¹ ^ k) (Set.Ioi R) volume ∧
      (∫ t in Set.Ioi R, (Real.cosh t)⁻¹ ^ k) ≤
        (2 : ℝ) ^ k / (k : ℝ) * Real.exp (-(k : ℝ) * R) := by
  sorry

theorem sqrt_weight_substitution {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (-1 : ℝ) 1)) :
    IntegrableOn (fun t => g t / Real.sqrt (1 - t ^ 2))
      (Set.Ioo (-1 : ℝ) 1) volume ∧
      (∫ t in Set.Ioo (-1 : ℝ) 1, g t / Real.sqrt (1 - t ^ 2)) =
        ∫ θ in (-Real.pi / 2)..(Real.pi / 2), g (Real.sin θ) := by
  sorry

end Intgrl
