import Lynth.Interval.Fns.EulerGamma.Proof.CoefficientSeries
import Lynth.Interval.Fns.EulerGamma.Proof.ChangeOfVariables

/-!
# Logarithmic changes of variables for `PP` and for the incomplete Gamma integrals
-/

open Real MeasureTheory Set Filter Topology

namespace BM

lemma subst_lower {N : ℝ} (hN : 0 < N) (g : ℝ → ℝ) :
    ∫ t in Ioo 0 N, g t = ∫ y in Ioi 0, N * exp (-y) * g (N * exp (-y)) := by
  have himg : (fun y => N * exp (-y)) '' Ioi 0 = Ioo 0 N := by
    ext t
    simp only [mem_image, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : exp (-y) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      constructor
      · positivity
      · nlinarith [Real.exp_pos (-y)]
    · rintro ⟨h0, h1⟩
      refine ⟨Real.log (N / t), Real.log_pos ((one_lt_div h0).mpr h1), ?_⟩
      rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have hinj : InjOn (fun y => N * exp (-y)) (Ioi 0) := by
    intro a _ b _ h
    simp only at h
    have := mul_left_cancel₀ hN.ne' h
    have := Real.exp_injective this
    linarith
  have hderiv : ∀ y ∈ Ioi (0:ℝ), HasDerivWithinAt (fun y => N * exp (-y)) (-(N * exp (-y)))
      (Ioi 0) y := by
    intro y _
    have := ((hasDerivAt_neg y).exp).const_mul N
    convert this.hasDerivWithinAt using 1; ring
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  simp only [smul_eq_mul]
  rw [abs_neg, abs_of_pos (by positivity)]

lemma subst_upper {N : ℝ} (hN : 0 < N) (g : ℝ → ℝ) :
    ∫ t in Ioi N, g t = ∫ y in Ioi 0, N * exp y * g (N * exp y) := by
  have himg : (fun y => N * exp y) '' Ioi 0 = Ioi N := by
    ext t
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : 1 < exp y := Real.one_lt_exp_iff.mpr hy
      nlinarith
    · intro h1
      have h0 : 0 < t := by linarith
      refine ⟨Real.log (t / N), Real.log_pos ((one_lt_div hN).mpr h1), ?_⟩
      rw [Real.exp_log (by positivity)]; field_simp
  have hinj : InjOn (fun y => N * exp y) (Ioi 0) := by
    intro a _ b _ h
    simp only at h
    exact Real.exp_injective (mul_left_cancel₀ hN.ne' h)
  have hderiv : ∀ y ∈ Ioi (0:ℝ), HasDerivWithinAt (fun y => N * exp y) (N * exp y) (Ioi 0) y :=
    fun y _ => ((Real.hasDerivAt_exp y).const_mul N).hasDerivWithinAt
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  simp only [smul_eq_mul]
  rw [abs_of_pos (by positivity)]

/-- lower incomplete Gamma integral in the variable `y` -/
noncomputable def Alow (N : ℝ) (s : ℝ) : ℝ := ∫ y in Ioi 0, exp (-(N * exp (-y))) * exp (-(s * y))

/-- upper incomplete Gamma integral in the variable `y` -/
noncomputable def Bup (N : ℝ) (s : ℝ) : ℝ := ∫ y in Ioi 0, exp (-(N * exp y)) * exp (s * y)

lemma rpow_mul_exp {N : ℝ} (hN : 0 < N) (y r : ℝ) :
    (N * exp y) ^ r = N ^ r * exp (r * y) := by
  rw [Real.mul_rpow hN.le (Real.exp_pos y).le, ← Real.exp_mul, mul_comm y r]

lemma Gamma_split {N : ℝ} (hN : 0 < N) {s : ℝ} (hs : 0 < s) :
    Real.Gamma s = N ^ s * (Alow N s + Bup N s) := by
  have hint := Real.GammaIntegral_convergent hs
  rw [Real.Gamma_eq_integral hs, ← Ioo_union_Ici_eq_Ioi hN,
    setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => by
        simp only [mem_Ioo, mem_Ici] at hx hx'; linarith) measurableSet_Ici
      (hint.mono_set Ioo_subset_Ioi_self) (hint.mono_set (Ici_subset_Ioi.mpr hN)),
    integral_Ici_eq_integral_Ioi, subst_lower hN, subst_upper hN, Alow, Bup, mul_add,
    ← integral_const_mul, ← integral_const_mul]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    rw [rpow_mul_exp hN]
    rw [show N * exp (-y) * (exp (-(N * exp (-y))) * (N ^ (s - 1) * exp ((s - 1) * -y)))
      = (N * N ^ (s - 1)) * (exp (-(N * exp (-y))) * (exp (-y) * exp ((s - 1) * -y))) by ring,
      ← Real.exp_add, ← Real.rpow_one_add' hN.le (by linarith)]
    rw [show (1 : ℝ) + (s - 1) = s by ring, show -y + (s - 1) * -y = -(s * y) by ring]
  · refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    rw [rpow_mul_exp hN]
    rw [show N * exp y * (exp (-(N * exp y)) * (N ^ (s - 1) * exp ((s - 1) * y)))
      = (N * N ^ (s - 1)) * (exp (-(N * exp y)) * (exp y * exp ((s - 1) * y))) by ring,
      ← Real.exp_add, ← Real.rpow_one_add' hN.le (by linarith)]
    rw [show (1 : ℝ) + (s - 1) = s by ring, show y + (s - 1) * y = s * y by ring]

lemma pp_split {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    pp n j = cc j * √(n : ℝ) * (Alow n (j + 1 / 2) + Bup n (j + 1 / 2)) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  rw [pp, Gamma_split hN (by positivity : (0:ℝ) < j + 1 / 2), Real.rpow_add hN,
    Real.rpow_natCast, Real.sqrt_eq_rpow]
  field_simp

/-- `PP` in the variable `y` (with `t = N e^{-y}`) -/
lemma PP_eq_y {n : ℕ} (hn : 1 ≤ n) :
    PP n = √(n : ℝ) * ∫ y in Ioi 0,
      exp (-(n * exp (-y))) * exp (-(1 / 2 * y)) * (1 - exp (-y)) ^ (-(1 / 2 : ℝ)) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  rw [PP, subst_lower hN, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  rw [rpow_mul_exp hN, show (n : ℝ) * exp (-y) / n = exp (-y) by field_simp]
  rw [show (n : ℝ) ^ (-(1 / 2 : ℝ)) = (√(n:ℝ))⁻¹ by rw [rpow_neg_half hN]]
  rw [show (n : ℝ) * exp (-y) * (exp (-(n * exp (-y))) * ((√(n:ℝ))⁻¹ * exp (-(1 / 2) * -y))
      * (1 - exp (-y)) ^ (-(1 / 2 : ℝ)))
    = ((n : ℝ) * (√(n:ℝ))⁻¹) * (exp (-(n * exp (-y))) * (exp (-y) * exp (-(1 / 2) * -y))
      * (1 - exp (-y)) ^ (-(1 / 2 : ℝ))) by ring, ← Real.exp_add]
  have hs : (n : ℝ) * (√(n:ℝ))⁻¹ = √(n:ℝ) := by
    have := Real.sq_sqrt hN.le
    have h0 : 0 < √(n:ℝ) := Real.sqrt_pos.mpr hN
    field_simp; linarith
  rw [hs, show -y + -(1 / 2) * -y = -(1 / 2 * y) by ring]

end BM
