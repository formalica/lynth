import Lynth.Interval.Fns.EulerGamma.Proof.Remainder.Identities
import Lynth.Interval.Fns.EulerGamma.Proof.CoefficientSumBound

/-!
# Pointwise estimates for the pieces `Em`, `Ep`, `VV`, `WW`, `TL`
-/

open Real MeasureTheory Set Filter Topology Finset

namespace BM

lemma expm_nonneg (y : ℝ) : 0 ≤ exp (-y) - 1 + y := by
  have := Real.add_one_le_exp (-y); linarith

lemma Em_pos (n : ℕ) (y : ℝ) : 0 < Em n y := Real.exp_pos _
lemma Ep_pos (n : ℕ) (y : ℝ) : 0 < Ep n y := Real.exp_pos _

lemma Em_le_one (n : ℕ) (y : ℝ) : Em n y ≤ 1 := by
  rw [Em, Real.exp_le_one_iff]
  have := expm_nonneg y
  have : (0 : ℝ) ≤ n := by positivity
  nlinarith

lemma Ep_le_Em (n : ℕ) {y : ℝ} (hy : 0 ≤ y) : Ep n y ≤ Em n y := by
  rw [Ep, Em, Real.exp_le_exp]
  have h := Real.self_le_sinh_iff.mpr hy
  rw [Real.sinh_eq] at h
  have : (0 : ℝ) ≤ n := by positivity
  nlinarith

lemma Em_le_exp_lin (n : ℕ) (y : ℝ) : Em n y ≤ exp (-((n : ℝ) * (y - 1))) := by
  rw [Em, Real.exp_le_exp]
  have := Real.exp_pos (-y)
  have : (0 : ℝ) ≤ n := by positivity
  nlinarith

lemma Em_le_gauss (n : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Em n y ≤ exp (-((n : ℝ) * y ^ 2 / 4)) := by
  rw [Em, Real.exp_le_exp]
  have hb := Real.exp_bound (x := -y) (by rw [abs_neg, abs_of_nonneg hy0]; exact hy1)
    (n := 3) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at hb
  rw [abs_of_nonneg hy0] at hb
  have h1 := (abs_le.mp hb).1
  have h3 : y ^ 3 ≤ y ^ 2 := by nlinarith
  have hkey : y ^ 2 / 4 ≤ exp (-y) - 1 + y := by norm_num at h1; nlinarith
  have : (0 : ℝ) ≤ n := by positivity
  nlinarith

lemma Em_sub_Ep_le (n : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Em n y - Ep n y ≤ Em n y * ((n : ℝ) * y ^ 2) := by
  set a := (n : ℝ) * ((exp y - 1 - y) - (exp (-y) - 1 + y))
  have hEp : Ep n y = Em n y * exp (-a) := by
    rw [Ep, Em, ← Real.exp_add]; congr 1; simp only [a]; ring
  have h1 : 1 - exp (-a) ≤ a := by have := Real.add_one_le_exp (-a); linarith
  have h2 := Real.abs_exp_sub_one_sub_id_le (x := y) (by rw [abs_of_nonneg hy0]; exact hy1)
  have h3 := (abs_le.mp h2).2
  have h4 := expm_nonneg y
  have hn : (0 : ℝ) ≤ n := by positivity
  have ha : a ≤ (n : ℝ) * y ^ 2 := by simp only [a]; nlinarith
  rw [hEp]
  have := Em_pos n y
  nlinarith

lemma VV_nonneg (n : ℕ) (y : ℝ) : 0 ≤ VV n y :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (cc_pos _).le (Real.exp_pos _).le)

lemma VV_le_WW (n : ℕ) (y : ℝ) : VV n y ≤ WW n y := by
  refine Finset.sum_le_sum (fun i hi => ?_)
  have := Finset.mem_range.mp hi
  exact mul_le_mul_of_nonneg_right (cc_antitone (by omega)) (Real.exp_pos _).le

lemma exp_half_le {i : ℕ} {y : ℝ} (hy : 0 ≤ y) :
    exp (-(((i : ℝ) + 1 / 2) * y)) ≤ exp (-(1 / 2 * y)) := by
  rw [Real.exp_le_exp]; have : (0 : ℝ) ≤ i := by positivity
  nlinarith

lemma WW_le (n : ℕ) {y : ℝ} (hy : 0 ≤ y) : WW n y ≤ n * exp (-(1 / 2 * y)) := by
  calc WW n y ≤ ∑ i ∈ range n, exp (-(1 / 2 * y)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        calc cc (n - 1 - i) * exp (-((i + 1 / 2) * y)) ≤ 1 * exp (-(1 / 2 * y)) := by
              exact mul_le_mul (cc_le_one _) (exp_half_le hy) (Real.exp_pos _).le zero_le_one
          _ = _ := one_mul _
    _ = n * exp (-(1 / 2 * y)) := by simp

lemma WW_nonneg (n : ℕ) (y : ℝ) : 0 ≤ WW n y := le_trans (VV_nonneg n y) (VV_le_WW n y)

lemma VV_le_div (n : ℕ) {y : ℝ} (hy : 0 < y) : VV n y ≤ cc n / y := by
  set r := exp (-y)
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by simp only [r]; rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hterm : ∀ i ∈ range n, cc (n + i) * exp (-(((i : ℝ) + 1 / 2) * y))
      ≤ cc n * (exp (-(1 / 2 * y)) * r ^ i) := by
    intro i _
    have : exp (-(((i : ℝ) + 1 / 2) * y)) = exp (-(1 / 2 * y)) * r ^ i := by
      simp only [r]; rw [exp_pow_eq, ← Real.exp_add]; congr 1; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (cc_antitone (by omega)) (by positivity)
  have hgeom : (∑ i ∈ range n, r ^ i) * (1 - r) ≤ 1 := by
    have := geom_sum_mul r n
    have : 0 < r ^ n := pow_pos hr0 n
    nlinarith
  have hsinh : y * exp (-(1 / 2 * y)) ≤ 1 - r := by
    have h := Real.self_le_sinh_iff.mpr (by linarith : 0 ≤ y / 2)
    rw [Real.sinh_eq] at h
    have e1 : exp (y / 2) * exp (-(1 / 2 * y)) = 1 := by rw [← Real.exp_add]; ring_nf; simp
    have e2 : exp (-(y / 2)) * exp (-(1 / 2 * y)) = r := by
      simp only [r]; rw [← Real.exp_add]; ring_nf
    have h0 := Real.exp_pos (-(1 / 2 * y))
    nlinarith
  calc VV n y ≤ ∑ i ∈ range n, cc n * (exp (-(1 / 2 * y)) * r ^ i) := Finset.sum_le_sum hterm
    _ = cc n * exp (-(1 / 2 * y)) * ∑ i ∈ range n, r ^ i := by
        rw [Finset.mul_sum]; congr 1; ext i; ring
    _ ≤ cc n / y := by
        rw [le_div_iff₀ hy]
        have hS : 0 ≤ ∑ i ∈ range n, r ^ i := Finset.sum_nonneg (fun i _ => by positivity)
        have hc := (cc_pos n).le
        have h0 := Real.exp_pos (-(1 / 2 * y))
        calc cc n * exp (-(1 / 2 * y)) * (∑ i ∈ range n, r ^ i) * y
            = cc n * (∑ i ∈ range n, r ^ i) * (y * exp (-(1 / 2 * y))) := by ring
          _ ≤ cc n * (∑ i ∈ range n, r ^ i) * (1 - r) := by gcongr
          _ = cc n * ((∑ i ∈ range n, r ^ i) * (1 - r)) := by ring
          _ ≤ cc n * 1 := by gcongr
          _ = cc n := mul_one _

lemma TL_bounds (n : ℕ) {y : ℝ} (hy : 0 < y) :
    0 ≤ TL n y ∧ TL n y ≤ y ^ (-(1 / 2 : ℝ)) * exp (-((n : ℝ) * y)) := by
  have hu0 : 0 ≤ exp (-y) := (Real.exp_pos _).le
  have hu1 : exp (-y) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  obtain ⟨h1, h2⟩ := cc_tail_bounds (2 * n) hu0 hu1
  have hE := Real.exp_pos (((n : ℝ) - 1 / 2) * y)
  refine ⟨mul_nonneg hE.le h1, ?_⟩
  -- `1 - e^{-y} ≥ y e^{-y}`
  have hlow : y * exp (-y) ≤ 1 - exp (-y) := by
    have := Real.add_one_le_exp y
    have e : exp y * exp (-y) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have hpos : 0 < y * exp (-y) := by positivity
  have hrp : (1 - exp (-y)) ^ (-(1 / 2 : ℝ)) ≤ (y * exp (-y)) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hpos hlow (by norm_num)
  have hsplit : (y * exp (-y)) ^ (-(1 / 2 : ℝ)) = y ^ (-(1 / 2 : ℝ)) * exp (1 / 2 * y) := by
    rw [Real.mul_rpow hy.le hu0, ← Real.exp_mul]; congr 2; ring
  have hyr : 0 < y ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hy _
  calc TL n y ≤ exp (((n : ℝ) - 1 / 2) * y) * (exp (-y) ^ (2 * n) * (1 - exp (-y)) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 hE.le
    _ ≤ exp (((n : ℝ) - 1 / 2) * y) * (exp (-y) ^ (2 * n) * (y ^ (-(1 / 2 : ℝ)) * exp (1 / 2 * y))) := by
        rw [← hsplit]; gcongr
    _ = y ^ (-(1 / 2 : ℝ)) * exp (-((n : ℝ) * y)) := by
        rw [exp_pow_eq]
        rw [show exp (((n : ℝ) - 1 / 2) * y) * (exp (-(((2 * n : ℕ) : ℝ) * y)) *
            (y ^ (-(1 / 2 : ℝ)) * exp (1 / 2 * y)))
          = y ^ (-(1 / 2 : ℝ)) * (exp (((n : ℝ) - 1 / 2) * y) * exp (-(((2 * n : ℕ) : ℝ) * y))
            * exp (1 / 2 * y)) by ring]
        simp only [← Real.exp_add]
        congr 2; push_cast; ring

end BM
