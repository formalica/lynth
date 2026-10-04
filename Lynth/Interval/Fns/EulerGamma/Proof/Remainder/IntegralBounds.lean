import Lynth.Interval.Fns.EulerGamma.Proof.Remainder.Integrability

/-!
# Bounds on the three remainder integrals
-/

open Real MeasureTheory Set Filter Topology Finset

namespace BM

lemma Z1_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ ∫ y in Ioi (0:ℝ), (Em n y - Ep n y) * VV n y ∧
    ∫ y in Ioi (0:ℝ), (Em n y - Ep n y) * VV n y ≤ cc n * (2 + exp 1) := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hgi, hgv⟩ := gauss_facts n hn
  have hei := integrableOn_exp_lin (c := 1) one_pos
  have hint : IntegrableOn (fun y => (Em n y - Ep n y) * VV n y) (Ioi 0) := by
    have := (integrable_EmVV n).sub (integrable_EpVV n)
    refine IntegrableOn.congr_fun this (fun y _ => by simp only [Pi.sub_apply]; ring)
      measurableSet_Ioi
  have hnn : ∀ y ∈ Ioi (0:ℝ), 0 ≤ (Em n y - Ep n y) * VV n y := fun y hy =>
    mul_nonneg (by have := Ep_le_Em n (le_of_lt (mem_Ioi.mp hy)); linarith) (VV_nonneg n y)
  refine ⟨setIntegral_nonneg measurableSet_Ioi hnn, ?_⟩
  have hmaj : ∀ y ∈ Ioi (0:ℝ), (Em n y - Ep n y) * VV n y
      ≤ cc n * ((n : ℝ) * y * exp (-((n : ℝ) * y ^ 2 / 4)) + exp 1 * exp (-(1 * y))) := by
    intro y hy
    have hy0 : 0 < y := hy
    have hc := cc_pos n
    have hV := VV_le_div n hy0
    have hV0 := VV_nonneg n y
    have hEp := Ep_pos n y
    have hEm := Em_pos n y
    have hg : 0 ≤ (n : ℝ) * y * exp (-((n : ℝ) * y ^ 2 / 4)) := by positivity
    have he : 0 ≤ exp 1 * exp (-(1 * y)) := by positivity
    rcases le_or_gt y 1 with h1 | h1
    · have hd := Em_sub_Ep_le n hy0.le h1
      have hG := Em_le_gauss n hy0.le h1
      have hd0 : 0 ≤ Em n y - Ep n y := by have := Ep_le_Em n hy0.le; linarith
      calc (Em n y - Ep n y) * VV n y ≤ (Em n y * ((n : ℝ) * y ^ 2)) * (cc n / y) :=
            mul_le_mul hd hV hV0 (by positivity)
        _ = cc n * ((n : ℝ) * y * Em n y) := by field_simp
        _ ≤ cc n * ((n : ℝ) * y * exp (-((n : ℝ) * y ^ 2 / 4))) := by gcongr
        _ ≤ _ := by gcongr; linarith
    · have hL := Em_le_exp_lin n y
      have hL2 : exp (-((n : ℝ) * (y - 1))) ≤ exp 1 * exp (-(1 * y)) := by
        rw [← Real.exp_add, Real.exp_le_exp]; nlinarith
      have hV1 : VV n y ≤ cc n := hV.trans (div_le_self hc.le h1.le)
      calc (Em n y - Ep n y) * VV n y ≤ Em n y * cc n :=
            mul_le_mul (by linarith) hV1 hV0 hEm.le
        _ ≤ (exp 1 * exp (-(1 * y))) * cc n := by gcongr; exact hL.trans hL2
        _ ≤ _ := by rw [mul_comm]; gcongr; linarith
  have hmi : IntegrableOn (fun y => cc n * ((n : ℝ) * y * exp (-((n : ℝ) * y ^ 2 / 4))
      + exp 1 * exp (-(1 * y)))) (Ioi 0) := (hgi.add (hei.const_mul _)).const_mul _
  calc ∫ y in Ioi (0:ℝ), (Em n y - Ep n y) * VV n y
      ≤ ∫ y in Ioi (0:ℝ), cc n * ((n : ℝ) * y * exp (-((n : ℝ) * y ^ 2 / 4))
          + exp 1 * exp (-(1 * y))) := setIntegral_mono_on hint hmi measurableSet_Ioi hmaj
    _ = cc n * (2 + exp 1) := by
        rw [MeasureTheory.integral_const_mul, integral_add hgi (hei.const_mul _),
          MeasureTheory.integral_const_mul, hgv, integral_exp_lin one_pos]
        ring

lemma Z2_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ ∫ y in Ioi (0:ℝ), Ep n y * (WW n y - VV n y) ∧
    ∫ y in Ioi (0:ℝ), Ep n y * (WW n y - VV n y) ≤ 4 / √(n : ℝ) := by
  have hint : IntegrableOn (fun y => Ep n y * (WW n y - VV n y)) (Ioi 0) := by
    have := (integrable_EpWW n).sub (integrable_EpVV n)
    refine IntegrableOn.congr_fun this (fun y _ => by simp only [Pi.sub_apply]; ring)
      measurableSet_Ioi
  have hnn : ∀ y ∈ Ioi (0:ℝ), 0 ≤ Ep n y * (WW n y - VV n y) := fun y _ =>
    mul_nonneg (Ep_pos n y).le (by have := VV_le_WW n y; linarith)
  refine ⟨setIntegral_nonneg measurableSet_Ioi hnn, ?_⟩
  have hD : ∀ y, WW n y - VV n y = ∑ i ∈ range n,
      (cc (n - 1 - i) - cc (n + i)) * exp (-(((i : ℝ) + 1 / 2) * y)) := by
    intro y; rw [WW, VV, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have hti : ∀ i ∈ range n, IntegrableOn (fun y => (cc (n - 1 - i) - cc (n + i)) *
      exp (-(((i : ℝ) + 1 / 2) * y))) (Ioi 0) :=
    fun i _ => (integrableOn_exp_lin (by positivity)).const_mul _
  have hsi : IntegrableOn (fun y => WW n y - VV n y) (Ioi 0) := by
    refine IntegrableOn.congr_fun (integrable_finsetSum _ hti) (fun y _ => ?_) measurableSet_Ioi
    rw [hD]
  calc ∫ y in Ioi (0:ℝ), Ep n y * (WW n y - VV n y) ≤ ∫ y in Ioi (0:ℝ), (WW n y - VV n y) := by
        refine setIntegral_mono_on hint hsi measurableSet_Ioi (fun y hy => ?_)
        have h1 := (Ep_le_Em n (le_of_lt (mem_Ioi.mp hy))).trans (Em_le_one n y)
        have h2 : 0 ≤ WW n y - VV n y := by have := VV_le_WW n y; linarith
        nlinarith
    _ = ∑ i ∈ range n, (cc (n - 1 - i) - cc (n + i)) / ((i : ℝ) + 1 / 2) := by
        simp_rw [hD]
        rw [integral_finsetSum _ hti]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [MeasureTheory.integral_const_mul, integral_exp_lin (by positivity)]
        ring
    _ ≤ 4 / √(n : ℝ) := Z2_sum_le n hn

lemma Z3_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ ∫ y in Ioi (0:ℝ), Em n y * TL n y ∧
    ∫ y in Ioi (0:ℝ), Em n y * TL n y ≤ √π / √(n : ℝ) := by
  refine ⟨setIntegral_nonneg measurableSet_Ioi (fun y hy =>
    mul_nonneg (Em_pos n y).le (TL_bounds n hy).1), ?_⟩
  rw [← integral_rpow_exp n hn]
  refine setIntegral_mono_on (integrable_EmTL n hn) (integrableOn_rpow_exp n hn)
    measurableSet_Ioi (fun y hy => ?_)
  obtain ⟨h1, h2⟩ := TL_bounds n hy
  calc Em n y * TL n y ≤ 1 * TL n y := mul_le_mul_of_nonneg_right (Em_le_one n y) h1
    _ ≤ _ := by rw [one_mul]; exact h2

end BM
