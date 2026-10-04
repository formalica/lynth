import Lynth.Interval.Fns.EulerGamma.Proof.Remainder.PointwiseEstimates

/-!
# Integrability and basic integrals for the exponentially small remainder
-/

open Real MeasureTheory Set Filter Topology Finset

namespace BM

lemma integrableOn_of_le {f g : ℝ → ℝ} (hf : Measurable f) (hg : IntegrableOn g (Ioi 0))
    (h : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ f y ∧ f y ≤ g y) : IntegrableOn f (Ioi 0) := by
  refine Integrable.mono' hg hf.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun y hy => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (h y hy).1]; exact (h y hy).2

lemma integrableOn_exp_lin {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun y => exp (-(c * y))) (Ioi 0) := by
  have := exp_neg_integrableOn_Ioi 0 hc
  simpa [neg_mul] using this

lemma integral_exp_lin {c : ℝ} (hc : 0 < c) : ∫ y in Ioi (0:ℝ), exp (-(c * y)) = 1 / c := by
  have := @integral_rpow_mul_exp_neg_mul_Ioi 1 c one_pos hc
  simpa using this

lemma integral_rpow_exp (n : ℕ) (hn : 1 ≤ n) :
    ∫ y in Ioi (0:ℝ), y ^ (-(1 / 2 : ℝ)) * exp (-((n : ℝ) * y)) = √π / √(n : ℝ) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have := @integral_rpow_mul_exp_neg_mul_Ioi (1 / 2) n (by norm_num) hN
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.Gamma_one_half_eq] at this
  rw [this, Real.div_rpow zero_le_one hN.le, Real.one_rpow, ← Real.sqrt_eq_rpow]
  ring

lemma integrableOn_rpow_exp (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (fun y => y ^ (-(1 / 2 : ℝ)) * exp (-((n : ℝ) * y))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_rpow_exp n hn]
  have : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  positivity

lemma gauss_facts (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (fun y => (n : ℝ) * y * exp (-((n : ℝ) * y ^ 2 / 4))) (Ioi 0) ∧
    ∫ y in Ioi (0:ℝ), (n : ℝ) * y * exp (-((n : ℝ) * y ^ 2 / 4)) = 2 := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  set g : ℝ → ℝ := fun y => -2 * exp (-((n : ℝ) * y ^ 2 / 4))
  have hd : ∀ x ∈ Ioi (0:ℝ), HasDerivAt g ((n : ℝ) * x * exp (-((n : ℝ) * x ^ 2 / 4))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -((n : ℝ) * y ^ 2 / 4)) (-((n : ℝ) * (2 * x) / 4)) x := by
      have := ((hasDerivAt_pow 2 x).const_mul (n : ℝ)).div_const 4 |>.neg
      convert this using 2; push_cast; ring
    have := (h1.exp).const_mul (-2)
    convert this using 1; ring
  have hc : ContinuousWithinAt g (Ici 0) 0 := by
    apply Continuous.continuousWithinAt; fun_prop
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => -((n : ℝ) * y ^ 2 / 4)) atTop atBot := by
      apply tendsto_neg_atTop_atBot.comp
      apply Tendsto.atTop_div_const (by norm_num)
      exact (tendsto_pow_atTop (by norm_num)).const_mul_atTop hN
    have := (Real.tendsto_exp_atBot.comp h1).const_mul (-2)
    simpa [g] using this
  have hint := integrableOn_Ioi_deriv_of_nonneg hc hd
    (fun x hx => by have : (0:ℝ) < x := hx; positivity) hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hc hd hint hlim]
  simp [g]

/-! ### integrability of the pieces -/

lemma integrable_a (n j : ℕ) :
    IntegrableOn (fun y => exp (-((n : ℝ) * exp (-y))) * exp (-(((j : ℝ) + 1 / 2) * y)))
      (Ioi 0) := by
  refine integrableOn_of_le (by fun_prop) (integrableOn_exp_lin (c := (j : ℝ) + 1 / 2)
    (by positivity)) (fun y _ => ⟨by positivity, ?_⟩)
  have : exp (-((n : ℝ) * exp (-y))) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := Real.exp_pos (-y); have : (0:ℝ) ≤ n := by positivity
    nlinarith
  have := Real.exp_pos (-(((j : ℝ) + 1 / 2) * y))
  nlinarith

lemma integrable_b (n j : ℕ) (hj : j < n) :
    IntegrableOn (fun y => exp (-((n : ℝ) * exp y)) * exp (((j : ℝ) + 1 / 2) * y)) (Ioi 0) := by
  have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
  refine integrableOn_of_le (by fun_prop)
    ((integrableOn_exp_lin (c := (n : ℝ) - j - 1 / 2) (by linarith)).const_mul (exp (-(n : ℝ))))
    (fun y _ => ⟨by positivity, ?_⟩)
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have := Real.add_one_le_exp y
  have : (0:ℝ) ≤ n := by positivity
  nlinarith

lemma integrable_EmVV (n : ℕ) : IntegrableOn (fun y => Em n y * VV n y) (Ioi 0) := by
  refine integrableOn_of_le (by unfold Em VV; fun_prop)
    ((integrableOn_exp_lin (c := 1 / 2) (by norm_num)).const_mul (n : ℝ))
    (fun y hy => ⟨mul_nonneg (Em_pos n y).le (VV_nonneg n y), ?_⟩)
  have hy : (0:ℝ) ≤ y := le_of_lt hy
  calc Em n y * VV n y ≤ 1 * WW n y :=
        mul_le_mul (Em_le_one n y) (VV_le_WW n y) (VV_nonneg n y) zero_le_one
    _ ≤ _ := by rw [one_mul]; exact WW_le n hy

lemma integrable_EpVV (n : ℕ) : IntegrableOn (fun y => Ep n y * VV n y) (Ioi 0) := by
  refine integrableOn_of_le (by unfold Ep VV; fun_prop)
    ((integrableOn_exp_lin (c := 1 / 2) (by norm_num)).const_mul (n : ℝ))
    (fun y hy => ⟨mul_nonneg (Ep_pos n y).le (VV_nonneg n y), ?_⟩)
  have hy : (0:ℝ) ≤ y := le_of_lt hy
  calc Ep n y * VV n y ≤ 1 * WW n y :=
        mul_le_mul ((Ep_le_Em n hy).trans (Em_le_one n y)) (VV_le_WW n y) (VV_nonneg n y)
          zero_le_one
    _ ≤ _ := by rw [one_mul]; exact WW_le n hy

lemma integrable_EpWW (n : ℕ) : IntegrableOn (fun y => Ep n y * WW n y) (Ioi 0) := by
  refine integrableOn_of_le (by unfold Ep WW; fun_prop)
    ((integrableOn_exp_lin (c := 1 / 2) (by norm_num)).const_mul (n : ℝ))
    (fun y hy => ⟨mul_nonneg (Ep_pos n y).le (WW_nonneg n y), ?_⟩)
  have hy : (0:ℝ) ≤ y := le_of_lt hy
  calc Ep n y * WW n y ≤ 1 * WW n y :=
        mul_le_mul_of_nonneg_right ((Ep_le_Em n hy).trans (Em_le_one n y)) (WW_nonneg n y)
    _ ≤ _ := by rw [one_mul]; exact WW_le n hy

lemma integrable_EmTL (n : ℕ) (hn : 1 ≤ n) : IntegrableOn (fun y => Em n y * TL n y) (Ioi 0) := by
  refine integrableOn_of_le (by unfold Em TL; fun_prop) (integrableOn_rpow_exp n hn)
    (fun y hy => ?_)
  obtain ⟨h1, h2⟩ := TL_bounds n hy
  refine ⟨mul_nonneg (Em_pos n y).le h1, ?_⟩
  calc Em n y * TL n y ≤ 1 * TL n y := mul_le_mul_of_nonneg_right (Em_le_one n y) h1
    _ ≤ _ := by rw [one_mul]; exact h2

end BM
