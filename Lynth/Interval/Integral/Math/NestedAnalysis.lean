import Lynth.Interval.Integral.Math.NestedDefs
import Lynth.Interval.Integral.Math.IntgrlDefs

/-! Portable proof obligations for recursive real quadrature. No interval
representation, search state or tactic code occurs in these statements.
The placeholders are deliberately isolated for independent Mathlib proofs. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Intgrl

theorem parametric_finite_analytic {F : ℂ → ℂ → ℂ} {z : ℂ}
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AnalyticAt ℂ (fun p : ℂ × ℂ => F p.1 p.2) (z,(t : ℂ))) :
    AnalyticAt ℂ (fun w => ∫ t in (0 : ℝ)..1, F w t) z := by
  sorry

theorem parametric_finite_norm {F : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hi : IntervalIntegrable F volume 0 1)
    (hb : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ‖F t‖ ≤ M) :
    ‖∫ t in (0 : ℝ)..1, F t‖ ≤ M := by
  sorry

/-- Applied to truncated improper integrals whose endpoint majorants are
uniform on a complex parameter neighborhood. Pointwise convergence alone
is deliberately insufficient. -/
theorem parametric_improper_analytic {U : Set ℂ} (hU : IsOpen U)
    {F : ℂ → ℂ} {G : ℕ → ℂ → ℂ}
    (hG : ∀ n, AnalyticOnNhd ℂ (G n) U)
    (hlim : TendstoLocallyUniformlyOn G F atTop U) : AnalyticOnNhd ℂ F U := by
  sorry

theorem right_substitution {f : ℝ → ℝ} {a : ℝ} (hm : Measurable f) :
    IntegrableOn f (Set.Ioi a) ↔
      IntervalIntegrable (fun t => f (a+t/(1-t))/(1-t)^2) volume 0 1 := by
  sorry

theorem right_substitution_value {f : ℝ → ℝ} {a : ℝ}
    (hi : IntegrableOn f (Set.Ioi a)) :
    (∫ x in Set.Ioi a, f x) =
      ∫ t in (0 : ℝ)..1, f (a+t/(1-t))/(1-t)^2 := by
  sorry

theorem left_substitution {f : ℝ → ℝ} {a : ℝ} (hm : Measurable f) :
    IntegrableOn f (Set.Iio a) ↔
      IntervalIntegrable (fun t => f (a-t/(1-t))/(1-t)^2) volume 0 1 := by
  sorry

theorem left_substitution_value {f : ℝ → ℝ} {a : ℝ}
    (hi : IntegrableOn f (Set.Iio a)) :
    (∫ x in Set.Iio a, f x) =
      ∫ t in (0 : ℝ)..1, f (a-t/(1-t))/(1-t)^2 := by
  sorry

theorem exp_decay_power {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Real.exp (-s) ≤ (n.factorial : ℝ)/s^n := by
  sorry

/-- Exact power/log moment used for endpoint truncation. -/
theorem power_log_moment {p δ : ℝ} (hp : -1 < p) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (m : ℕ) :
    IntegrableOn (fun t : ℝ => t^p*(1-Real.log t)^m) (Set.Ioc 0 δ) ∧
    (∫ t in (0 : ℝ)..δ, t^p*(1-Real.log t)^m) =
      δ^(p+1) * ∑ j ∈ Finset.range (m+1),
        ((m.factorial : ℝ)/j.factorial/(p+1)^(m-j+1))*(1-Real.log δ)^j := by
  sorry

theorem endpoint_remainder {F : ℝ → ℂ} {p δ C : ℝ} {m : ℕ}
    (hp : -1 < p) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C)
    (hm : Measurable F)
    (hb : ∀ t ∈ Set.Ioo (0 : ℝ) δ, ‖F t‖ ≤ C*t^p*(1-Real.log t)^m) :
    IntegrableOn F (Set.Ioc 0 δ) ∧
    ‖∫ t in (0 : ℝ)..δ, F t‖ ≤ C*δ^(p+1) * ∑ j ∈ Finset.range (m+1),
      ((m.factorial : ℝ)/j.factorial/(p+1)^(m-j+1))*(1-Real.log δ)^j := by
  sorry

theorem finite_power_value {a b p : ℝ} (hab : a ≤ b) (hp : -1 < p) :
    IntervalIntegrable (fun x : ℝ => (x-a)^p) volume a b ∧
      (∫ x in a..b, (x-a)^p) = (b-a)^(p+1)/(p+1) := by
  sorry

theorem finite_log_value {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable Real.log volume 0 b ∧
      (∫ x in (0 : ℝ)..b, Real.log x) = b*(Real.log b-1) := by
  sorry

theorem right_exp_value (a c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (c-x)) (Set.Ioi a) ∧
      (∫ x in Set.Ioi a, Real.exp (c-x)) = Real.exp (c-a) := by
  sorry

theorem finite_power_substitution {f : ℝ → ℝ} (hm : Measurable f) {n : ℕ}
    (hn : 0 < n) :
    IntervalIntegrable f volume 0 1 ↔
      IntervalIntegrable (fun t : ℝ => (n:ℝ)*t^(n-1)*f (t^n)) volume 0 1 := by
  sorry

theorem finite_power_substitution_value {f : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hi : IntervalIntegrable f volume 0 1) :
    (∫ t in (0 : ℝ)..1, f t) = ∫ t in (0 : ℝ)..1, (n:ℝ)*t^(n-1)*f (t^n) := by
  sorry

theorem sqrt_power_factor {t a p : ℝ} (ht : 0 < t) :
    Real.sqrt (t^p*a) = t^(p/2)*Real.sqrt a := by
  sorry

theorem whole_split {f : ℝ → ℝ}
    (hr : IntegrableOn f (Set.Ioi 0)) (hl : IntegrableOn f (Set.Iio 0)) :
    Integrable f ∧ (∫ x, f x) = (∫ x in Set.Ioi (0:ℝ), f x)+(∫ x in Set.Iio (0:ℝ), f x) := by
  sorry

theorem exp_negative_nat (k : ℕ) : Real.exp (-(k:ℝ)) ≤ (2:ℝ)^(-(k:ℤ)) := by
  sorry

theorem whole_split_at {f : ℝ → ℝ} {a : ℝ}
    (hr : IntegrableOn f (Set.Ioi a)) (hl : IntegrableOn f (Set.Iio a)) :
    Integrable f ∧ (∫ x, f x) = (∫ x in Set.Ioi a, f x)+(∫ x in Set.Iio a, f x) := by
  sorry

theorem left_exp_value (a c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (c+x)) (Set.Iio a) ∧
      (∫ x in Set.Iio a, Real.exp (c+x)) = Real.exp (c+a) := by
  sorry

end Intgrl
