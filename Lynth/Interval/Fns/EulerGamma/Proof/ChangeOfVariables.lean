import Lynth.Interval.Fns.EulerGamma.Proof.Notation

/-!
# Changes of variables: `K0` and `bmB` in terms of `QQ` and `PP`
-/

open Real MeasureTheory Set Filter Topology

namespace BM

lemma rpow_neg_half {a : ℝ} (ha : 0 < a) : a ^ (-(1 / 2 : ℝ)) = (√a)⁻¹ := by
  rw [Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]

lemma K0_eq_QQ_real {x : ℝ} (hx : 0 < x) :
    K0 x = exp (-(2 * x)) *
      (∫ s in Ioi 0, exp (-s) * s ^ (-(1 / 2 : ℝ)) * (1 + s / (4 * x)) ^ (-(1 / 2 : ℝ)))
      / (2 * √x) := by
  set f : ℝ → ℝ := fun v => 2 * x * (cosh v - 1)
  have himg : f '' Ioi 0 = Ioi 0 := by
    ext s
    simp only [mem_image, mem_Ioi, f]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have := Real.one_lt_cosh.mpr hv.ne'
      have : 0 < cosh v - 1 := by linarith
      positivity
    · intro hs
      have h0 : 0 < s / (2 * x) := by positivity
      have h1 : 1 < 1 + s / (2 * x) := by linarith
      refine ⟨arcosh (1 + s / (2 * x)), arcosh_pos h1, ?_⟩
      rw [cosh_arcosh h1.le]; field_simp; ring
  have hinj : InjOn f (Ioi 0) := by
    intro a ha b hb h
    simp only [f] at h
    have : cosh a = cosh b := by
      have h2 : 2 * x ≠ 0 := by positivity
      have := mul_left_cancel₀ h2 h; linarith
    exact cosh_injOn (mem_Ici.mpr (le_of_lt ha)) (mem_Ici.mpr (le_of_lt hb)) this
  have hderiv : ∀ v ∈ Ioi (0:ℝ), HasDerivWithinAt f (2 * x * sinh v) (Ioi 0) v := by
    intro v _
    have := ((Real.hasDerivAt_cosh v).sub_const 1).const_mul (2 * x)
    exact this.hasDerivWithinAt
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun s => exp (-s) * s ^ (-(1 / 2 : ℝ)) * (1 + s / (4 * x)) ^ (-(1 / 2 : ℝ)))
  rw [himg] at key
  rw [key]
  have hpt : ∀ v ∈ Ioi (0:ℝ), |2 * x * sinh v| • (exp (-f v) * f v ^ (-(1 / 2 : ℝ)) *
      (1 + f v / (4 * x)) ^ (-(1 / 2 : ℝ))) = (2 * √x * exp (2 * x)) * exp (-(2 * x * cosh v)) := by
    intro v hv
    have hv' : (0:ℝ) < v := hv
    have hS : 0 < sinh v := Real.sinh_pos_iff.mpr hv'
    have hc : 1 < cosh v := Real.one_lt_cosh.mpr hv'.ne'
    have hS2 : sinh v ^ 2 = cosh v ^ 2 - 1 := by have := Real.cosh_sq v; linarith
    have hf : 0 < f v := by
      have h0 : 0 < cosh v - 1 := by linarith
      simp only [f]; positivity
    have hg : 1 + f v / (4 * x) = (cosh v + 1) / 2 := by simp only [f]; field_simp; ring
    rw [smul_eq_mul, abs_of_pos (by positivity), rpow_neg_half hf, hg,
      rpow_neg_half (by linarith)]
    set A := √(f v)
    set B := √((cosh v + 1) / 2)
    have hA : 0 < A := Real.sqrt_pos.mpr hf
    have hB : 0 < B := Real.sqrt_pos.mpr (by linarith)
    have hAB : A * B = √x * sinh v := by
      have h1 : (A * B) ^ 2 = (√x * sinh v) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hf.le, Real.sq_sqrt (by linarith), Real.sq_sqrt hx.le,
          hS2]
        simp only [f]; ring
      have := Real.sqrt_pos.mpr hx
      exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h1
    have hsx : √x ^ 2 = x := Real.sq_sqrt hx.le
    have hexp : exp (-f v) = exp (2 * x) * exp (-(2 * x * cosh v)) := by
      rw [← Real.exp_add]; congr 1; simp only [f]; ring
    rw [hexp]
    have hsq : 0 < √x := Real.sqrt_pos.mpr hx
    field_simp
    linear_combination (-√x) * hAB + (-sinh v) * hsx
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, K0]
  have hsq : 0 < √x := Real.sqrt_pos.mpr hx
  have he : exp (-(2 * x)) * exp (2 * x) = 1 := by rw [← Real.exp_add]; simp
  set J := ∫ v in Ioi 0, exp (-(2 * x * cosh v))
  rw [show exp (-(2 * x)) * (2 * √x * exp (2 * x) * J) / (2 * √x)
    = (exp (-(2 * x)) * exp (2 * x)) * J by field_simp, he, one_mul]

theorem K0_eq_QQ (m : ℕ) (hm : 1 ≤ m) :
    K0 m = exp (-(2 * m)) * QQ (4 * m) / (2 * √(m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [K0_eq_QQ_real hm0, QQ]
  push_cast
  rfl

end BM
