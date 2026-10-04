import Lynth.Interval.Fns.EulerGamma.Proof.Remainder.IntegralBounds

/-!
# The exponentially small remainder `PP n - Σ_{j<n} pp n j` and the lower bound on `PP n`
-/

open Real MeasureTheory Set Filter Topology Finset

namespace BM

lemma integral_lower (n : ℕ) (hn : 1 ≤ n) :
    ∫ y in Ioi (0:ℝ), exp (-(n * exp (-y))) * exp (-(1 / 2 * y)) * (1 - exp (-y)) ^ (-(1 / 2 : ℝ))
      = ∑ j ∈ range n, cc j * Alow n (j + 1 / 2)
        + exp (-(n : ℝ)) * ((∫ y in Ioi (0:ℝ), Em n y * VV n y)
          + ∫ y in Ioi (0:ℝ), Em n y * TL n y) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => lower_identity n y)]
  have h1 : ∀ j ∈ range n, IntegrableOn (fun y => cc j * (exp (-(n * exp (-y))) *
      exp (-((j + 1 / 2) * y)))) (Ioi 0) := fun j _ => (integrable_a n j).const_mul _
  have h2 : IntegrableOn (fun y => Em n y * VV n y + Em n y * TL n y) (Ioi 0) :=
    (integrable_EmVV n).add (integrable_EmTL n hn)
  rw [integral_add (integrable_finsetSum _ h1)]
  · rw [integral_finsetSum _ h1, MeasureTheory.integral_const_mul]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [MeasureTheory.integral_const_mul, Alow]
    · congr 1
      rw [← integral_add (integrable_EmVV n) (integrable_EmTL n hn)]
      congr 1; ext y; ring
  · exact IntegrableOn.congr_fun (h2.const_mul (exp (-(n : ℝ)))) (fun y _ => by ring)
      measurableSet_Ioi

lemma sum_pp_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ range n, pp n j = √(n : ℝ) * (∑ j ∈ range n, cc j * Alow n (j + 1 / 2)
        + exp (-(n : ℝ)) * ∫ y in Ioi (0:ℝ), Ep n y * WW n y) := by
  have hB : ∑ j ∈ range n, cc j * Bup n (j + 1 / 2)
      = exp (-(n : ℝ)) * ∫ y in Ioi (0:ℝ), Ep n y * WW n y := by
    have h1 : ∀ j ∈ range n, IntegrableOn (fun y => cc j * (exp (-(n * exp y)) *
        exp ((j + 1 / 2) * y))) (Ioi 0) :=
      fun j hj => (integrable_b n j (Finset.mem_range.mp hj)).const_mul _
    have : ∑ j ∈ range n, cc j * Bup n (j + 1 / 2)
        = ∫ y in Ioi (0:ℝ), ∑ j ∈ range n, cc j * (exp (-(n * exp y)) * exp ((j + 1 / 2) * y)) := by
      rw [integral_finsetSum _ h1]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [MeasureTheory.integral_const_mul, Bup]
    rw [this, ← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun y _ => upper_identity n y)
  rw [Finset.sum_congr rfl (fun j _ => pp_split hn j), ← hB, mul_add, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => by ring)

theorem EP_diff (n : ℕ) (hn : 1 ≤ n) :
    PP n - ∑ j ∈ range n, pp n j = √(n : ℝ) * exp (-(n : ℝ)) *
      ((∫ y in Ioi (0:ℝ), (Em n y - Ep n y) * VV n y) + (∫ y in Ioi (0:ℝ), Em n y * TL n y)
        - ∫ y in Ioi (0:ℝ), Ep n y * (WW n y - VV n y)) := by
  rw [PP_eq_y hn, integral_lower n hn, sum_pp_eq n hn]
  have e1 : ∫ y in Ioi (0:ℝ), (Em n y - Ep n y) * VV n y
      = (∫ y in Ioi (0:ℝ), Em n y * VV n y) - ∫ y in Ioi (0:ℝ), Ep n y * VV n y := by
    rw [← integral_sub (integrable_EmVV n) (integrable_EpVV n)]; congr 1; ext y; ring
  have e2 : ∫ y in Ioi (0:ℝ), Ep n y * (WW n y - VV n y)
      = (∫ y in Ioi (0:ℝ), Ep n y * WW n y) - ∫ y in Ioi (0:ℝ), Ep n y * VV n y := by
    rw [← integral_sub (integrable_EpWW n) (integrable_EpVV n)]; congr 1; ext y; ring
  rw [e1, e2]; ring

theorem EP_bound_n (n : ℕ) (hn : 1 ≤ n) :
    |PP n - ∑ j ∈ range n, pp n j| ≤ 10 * exp (-(n : ℝ)) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  rw [EP_diff n hn]
  obtain ⟨a0, a1⟩ := Z1_bounds n hn
  obtain ⟨b0, b1⟩ := Z2_bounds n hn
  obtain ⟨c0, c1⟩ := Z3_bounds n hn
  set A := ∫ y in Ioi (0:ℝ), (Em n y - Ep n y) * VV n y
  set B := ∫ y in Ioi (0:ℝ), Ep n y * (WW n y - VV n y)
  set C := ∫ y in Ioi (0:ℝ), Em n y * TL n y
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hN
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hN.le
  have hE := Real.exp_pos (-(n : ℝ))
  -- `√n · cc n ≤ 0.58`
  have hcn : √(n : ℝ) * cc n ≤ 0.58 := by
    have h := cc_sq_le n
    have hc := cc_pos n
    have : (√(n : ℝ) * cc n) ^ 2 ≤ 0.58 ^ 2 := by
      rw [mul_pow, hsq]
      calc (n : ℝ) * cc n ^ 2 ≤ n * (1 / (3 * n + 1)) := by gcongr
        _ ≤ 0.58 ^ 2 := by rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
    have : 0 ≤ √(n : ℝ) * cc n := by positivity
    nlinarith
  have he1 : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpi : √π < 1.78 := by
    rw [Real.sqrt_lt' (by norm_num)]; have := Real.pi_lt_d2; nlinarith
  have hA : √(n : ℝ) * A ≤ 2.74 := by
    calc √(n : ℝ) * A ≤ √(n : ℝ) * (cc n * (2 + exp 1)) := by gcongr
      _ = (√(n : ℝ) * cc n) * (2 + exp 1) := by ring
      _ ≤ 0.58 * (2 + 2.7182818286) := by gcongr
      _ ≤ 2.74 := by norm_num
  have hB : √(n : ℝ) * B ≤ 4 := by
    calc √(n : ℝ) * B ≤ √(n : ℝ) * (4 / √(n : ℝ)) := by gcongr
      _ = 4 := by field_simp
  have hC : √(n : ℝ) * C ≤ 1.78 := by
    calc √(n : ℝ) * C ≤ √(n : ℝ) * (√π / √(n : ℝ)) := by gcongr
      _ = √π := by field_simp
      _ ≤ 1.78 := hpi.le
  have hA0 : 0 ≤ √(n : ℝ) * A := by positivity
  have hB0 : 0 ≤ √(n : ℝ) * B := by positivity
  have hC0 : 0 ≤ √(n : ℝ) * C := by positivity
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

lemma integral_lower_ge (n : ℕ) (hn : 1 ≤ n) :
    Alow n (1 / 2) ≤ ∫ y in Ioi (0:ℝ),
      exp (-(n * exp (-y))) * exp (-(1 / 2 * y)) * (1 - exp (-y)) ^ (-(1 / 2 : ℝ)) := by
  have hint : IntegrableOn (fun y => exp (-(n * exp (-y))) * exp (-(1 / 2 * y)) *
      (1 - exp (-y)) ^ (-(1 / 2 : ℝ))) (Ioi 0) := by
    have h1 : ∀ j ∈ range n, IntegrableOn (fun y => cc j * (exp (-(n * exp (-y))) *
        exp (-((j + 1 / 2) * y)))) (Ioi 0) := fun j _ => (integrable_a n j).const_mul _
    have h2 := (((integrable_EmVV n).add (integrable_EmTL n hn)).const_mul (exp (-(n : ℝ))))
    refine IntegrableOn.congr_fun ((integrable_finsetSum _ h1).add h2) (fun y _ => ?_)
      measurableSet_Ioi
    rw [lower_identity n y]; simp only [Pi.add_apply]; ring
  rw [Alow]
  refine setIntegral_mono_on (by simpa using integrable_a n 0) hint measurableSet_Ioi
    (fun y hy => ?_)
  have hy : 0 < y := hy
  have hu1 : exp (-y) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hu0 := Real.exp_pos (-y)
  have h1 : 1 ≤ (1 - exp (-y)) ^ (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) (by norm_num)
  have h0 : 0 ≤ exp (-(n * exp (-y))) * exp (-(1 / 2 * y)) := by positivity
  calc exp (-(n * exp (-y))) * exp (-(1 / 2 * y))
      = exp (-(n * exp (-y))) * exp (-(1 / 2 * y)) * 1 := (mul_one _).symm
    _ ≤ _ := by gcongr

theorem PP_ge_n (n : ℕ) (hn : 4 ≤ n) : 1.7 ≤ PP n := by
  have hn1 : 1 ≤ n := by omega
  have hN : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hN0
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hN0.le
  have hG := Gamma_split hN0 (by norm_num : (0:ℝ) < 1 / 2)
  rw [Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow] at hG
  -- the upper part is tiny
  have hBup : Bup n (1 / 2) ≤ exp (-(n : ℝ)) * (1 / ((n : ℝ) - 1 / 2)) := by
    have hI := integral_exp_lin (c := (n : ℝ) - 1 / 2) (by linarith)
    rw [Bup, ← hI, ← MeasureTheory.integral_const_mul]
    refine setIntegral_mono_on (by simpa using integrable_b n 0 (by omega))
      ((integrableOn_exp_lin (by linarith)).const_mul _) measurableSet_Ioi (fun y _ => ?_)
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have := Real.add_one_le_exp y
    nlinarith
  have hpi : 1.77 < √π := by
    rw [Real.lt_sqrt (by norm_num)]; have := Real.pi_gt_d2; nlinarith
  have he4 : exp (-(n : ℝ)) ≤ 0.02 := by
    have h1 : exp (-(n : ℝ)) ≤ exp (-4) := Real.exp_le_exp.mpr (by linarith)
    have h2 : exp (-4 : ℝ) = (exp 1 ^ 4)⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]; norm_num
    have h3 : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
    have h4 : (50 : ℝ) ≤ exp 1 ^ 4 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) h3.le 4)
    rw [h2] at h1
    calc exp (-(n : ℝ)) ≤ (exp 1 ^ 4)⁻¹ := h1
      _ ≤ (50 : ℝ)⁻¹ := by gcongr
      _ ≤ 0.02 := by norm_num
  have hsB : √(n : ℝ) * Bup n (1 / 2) ≤ 0.02 := by
    have hq : √(n : ℝ) * (1 / ((n : ℝ) - 1 / 2)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]; nlinarith
    calc √(n : ℝ) * Bup n (1 / 2) ≤ √(n : ℝ) * (exp (-(n : ℝ)) * (1 / ((n : ℝ) - 1 / 2))) := by
          gcongr
      _ = exp (-(n : ℝ)) * (√(n : ℝ) * (1 / ((n : ℝ) - 1 / 2))) := by ring
      _ ≤ 0.02 * 1 := by
          have : 0 < (n : ℝ) - 1 / 2 := by linarith
          apply mul_le_mul he4 hq (by positivity) (by norm_num)
      _ = 0.02 := by norm_num
  have hL := integral_lower_ge n hn1
  rw [PP_eq_y hn1]
  have : √(n : ℝ) * Alow n (1 / 2) ≤ √(n : ℝ) * ∫ y in Ioi (0:ℝ),
      exp (-(n * exp (-y))) * exp (-(1 / 2 * y)) * (1 - exp (-y)) ^ (-(1 / 2 : ℝ)) := by gcongr
  have hAB : √(n : ℝ) * Alow n (1 / 2) + √(n : ℝ) * Bup n (1 / 2) = √π := by
    rw [hG]; ring
  linarith

end BM
