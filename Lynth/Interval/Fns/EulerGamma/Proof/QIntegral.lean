import Lynth.Interval.Fns.EulerGamma.Proof.BinomialRemainder

/-!
# The integral `QQ n` and its asymptotic expansion
-/

open Real MeasureTheory Set Finset

namespace BM

/-- the weight `e^{-s} s^{-1/2}` -/
noncomputable def gw (s : ℝ) : ℝ := exp (-s) * s ^ (-(1 / 2 : ℝ))

lemma gw_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ gw s := by
  unfold gw; have := Real.rpow_nonneg hs (-(1 / 2 : ℝ)); positivity

lemma gw_mom_eq (l : ℕ) {s : ℝ} (hs : 0 < s) :
    gw s * s ^ l = exp (-s) * s ^ (((l : ℝ) + 1 / 2) - 1) := by
  unfold gw
  rw [show ((l : ℝ) + 1 / 2) - 1 = -(1 / 2 : ℝ) + l by ring, Real.rpow_add hs,
    Real.rpow_natCast]
  ring

lemma gw_mom_integrable (l : ℕ) : IntegrableOn (fun s => gw s * s ^ l) (Ioi 0) := by
  have := Real.GammaIntegral_convergent (s := (l : ℝ) + 1 / 2) (by positivity)
  refine this.congr_fun (fun s hs => (gw_mom_eq l hs).symm) measurableSet_Ioi

lemma gw_mom_integral (l : ℕ) : ∫ s in Ioi 0, gw s * s ^ l = Real.Gamma (l + 1 / 2) := by
  rw [Real.Gamma_eq_integral (by positivity)]
  exact setIntegral_congr_fun measurableSet_Ioi (fun s hs => gw_mom_eq l hs)

lemma gw_integrable : IntegrableOn gw (Ioi 0) := by
  simpa using gw_mom_integrable 0

lemma gw_integral : ∫ s in Ioi 0, gw s = √π := by
  have := gw_mom_integral 0
  simp only [pow_zero, mul_one, Nat.cast_zero, zero_add] at this
  rw [this, Real.Gamma_one_half_eq]

lemma gw_scaled_integrable (n l : ℕ) :
    IntegrableOn (fun s => gw s * (s / n) ^ l) (Ioi 0) := by
  have := (gw_mom_integrable l).mul_const ((1 / (n : ℝ)) ^ l)
  refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
  rw [div_eq_mul_one_div s, mul_pow]; ring

lemma gw_scaled_integral (n l : ℕ) :
    ∫ s in Ioi 0, gw s * (s / n) ^ l = Real.Gamma (l + 1 / 2) / (n : ℝ) ^ l := by
  have h : ∀ s : ℝ, gw s * (s / n) ^ l = (gw s * s ^ l) * (1 / (n : ℝ)) ^ l := by
    intro s; rw [div_eq_mul_one_div s, mul_pow]; ring
  simp_rw [h]
  rw [integral_mul_const, gw_mom_integral]
  rw [one_div_pow]; ring

lemma QQ_eq (n : ℕ) : QQ n = ∫ s in Ioi 0, gw s * (1 + s / n) ^ (-(1 / 2 : ℝ)) := rfl

lemma QQ_integrand_le (n : ℕ) {s : ℝ} (hs : 0 < s) :
    gw s * (1 + s / n) ^ (-(1 / 2 : ℝ)) ≤ gw s := by
  have h0 : 0 ≤ s / n := by positivity
  have h1 : (1 + s / n) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have := gw_nonneg hs.le
  nlinarith

lemma QQ_integrand_nonneg (n : ℕ) {s : ℝ} (hs : 0 < s) :
    0 ≤ gw s * (1 + s / n) ^ (-(1 / 2 : ℝ)) := by
  have := gw_nonneg hs.le
  have : 0 ≤ (1 + s / n) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  positivity

lemma QQ_integrable (n : ℕ) :
    IntegrableOn (fun s => gw s * (1 + s / n) ^ (-(1 / 2 : ℝ))) (Ioi 0) := by
  refine gw_integrable.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro s hs
    have hs' : 0 < s := hs
    unfold gw
    apply ContinuousAt.continuousWithinAt
    have h1 : 0 < 1 + s / n := by positivity
    apply ContinuousAt.mul
    · apply ContinuousAt.mul (by fun_prop)
      exact Real.continuousAt_rpow_const _ _ (Or.inl hs'.ne')
    · exact ContinuousAt.rpow_const (by fun_prop) (Or.inl h1.ne')
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (QQ_integrand_nonneg n hs)]
    exact QQ_integrand_le n hs

theorem QQ_nonneg (n : ℕ) : 0 ≤ QQ n := by
  rw [QQ_eq]
  exact setIntegral_nonneg measurableSet_Ioi (fun s hs => QQ_integrand_nonneg n hs)

theorem QQ_le (n : ℕ) : QQ n ≤ √π := by
  rw [QQ_eq, ← gw_integral]
  exact setIntegral_mono_on (QQ_integrable n) gw_integrable measurableSet_Ioi
    (fun s hs => QQ_integrand_le n hs)

theorem EQ_bound (n : ℕ) (hn : 1 ≤ n) :
    |QQ n - ∑ l ∈ range n, (-1) ^ l * pp n l| ≤ pp n n := by
  have hsum : ∑ l ∈ range n, (-1) ^ l * pp n l
      = ∫ s in Ioi 0, ∑ l ∈ range n, ((-1) ^ l * bc (1 / 2) l) * (gw s * (s / n) ^ l) := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [integral_const_mul, gw_scaled_integral, bc_half, pp]; ring
    · intro l _; exact (gw_scaled_integrable n l).const_mul _
  have hdiff : QQ n - ∑ l ∈ range n, (-1) ^ l * pp n l
      = ∫ s in Ioi 0, gw s * binRem (1 / 2) n (s / n) := by
    rw [hsum, QQ_eq, ← integral_sub (QQ_integrable n)]
    · refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
      simp only [binRem, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    · exact integrable_finsetSum _ (fun l _ => (gw_scaled_integrable n l).const_mul _)
  rw [hdiff]
  have hb : ∫ s in Ioi 0, cc n * (gw s * (s / n) ^ n) = pp n n := by
    rw [integral_const_mul, gw_scaled_integral, pp]; ring
  rw [← hb, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((gw_scaled_integrable n n).const_mul _) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
  intro s hs
  have hs' : (0 : ℝ) < s := hs
  have hsn : 0 ≤ s / n := by positivity
  have h := abs_binRem_le (1 / 2) (by norm_num) n (s / n) hsn
  rw [bc_half] at h
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gw_nonneg hs'.le)]
  have := gw_nonneg hs'.le
  calc gw s * |binRem (1 / 2) n (s / n)| ≤ gw s * (cc n * (s / n) ^ n) :=
        mul_le_mul_of_nonneg_left h this
    _ = cc n * (gw s * (s / n) ^ n) := by ring

end BM
