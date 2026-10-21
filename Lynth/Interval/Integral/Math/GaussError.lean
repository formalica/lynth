import Lynth.Interval.Integral.Math.Legendre

/-!
P0: analytic error bound, real affine specialization, and ellipse geometry.
Send with IntgrlDefs.lean. Legendre.lean is useful proof material, but is
not needed to elaborate the statements.

Target: FLINT src/acb_calc/integrate_gl_auto_deg.c and its acb_calc docs.
The unit rule has n nodes, not n+1. The half-length factor must occur once.
Use the stronger classical bound with (1-rho^(-2))*rho^(2*n) if convenient,
then weaken it to glError.
-/

noncomputable section

open scoped BigOperators

namespace Intgrl

lemma ellipseX_pos {ρ : ℝ} (hρ : 1 < ρ) : 1 < ellipseX ρ := by
  unfold ellipseX
  have h0 : 0 < ρ := by linarith
  have : ρ + ρ⁻¹ - 2 = (ρ - 1) ^ 2 / ρ := by field_simp; ring
  have : 0 < (ρ - 1) ^ 2 / ρ := by apply div_pos; nlinarith; exact h0
  linarith

lemma ellipseY_pos {ρ : ℝ} (hρ : 1 < ρ) : 0 < ellipseY ρ := by
  unfold ellipseY
  have : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
  linarith


theorem ellipse_in_rectangle {ρ : ℝ} (hρ : 1 < ρ) {z : ℂ}
    (hz : z ∈ ellipse ρ) :
    |z.re| ≤ ellipseX ρ ∧ |z.im| ≤ ellipseY ρ := by
  have hX := (zero_lt_one.trans (ellipseX_pos hρ))
  have hY := ellipseY_pos hρ
  simp only [ellipse, Set.mem_setOf_eq] at hz
  have h1 : (z.re / ellipseX ρ) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (z.im / ellipseY ρ)]
  have h2 : (z.im / ellipseY ρ) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (z.re / ellipseX ρ)]
  rw [sq_le_one_iff_abs_le_one, abs_div, abs_of_pos hX, div_le_one hX] at h1
  rw [sq_le_one_iff_abs_le_one, abs_div, abs_of_pos hY, div_le_one hY] at h2
  exact ⟨h1, h2⟩

theorem real_mem_ellipse {ρ t : ℝ} (hρ : 1 < ρ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (t : ℂ) ∈ ellipse ρ := by
  have hX := ellipseX_pos hρ
  simp only [ellipse, Set.mem_setOf_eq, Complex.ofReal_re, Complex.ofReal_im, zero_div]
  have : |t / ellipseX ρ| ≤ 1 := by
    have hX0 : 0 < ellipseX ρ := by linarith
    rw [abs_div, abs_of_pos hX0, div_le_one hX0]
    exact (abs_le.2 ⟨ht.1, ht.2⟩).trans hX.le
  have := (sq_le_one_iff_abs_le_one _).2 this
  nlinarith

open scoped Real
open Complex MeasureTheory


lemma ellipseX_eq_cosh {ρ : ℝ} (hρ : 1 < ρ) : ellipseX ρ = Real.cosh (Real.log ρ) := by
  have h0 : 0 < ρ := by linarith
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_log h0, ellipseX]

lemma ellipseY_eq_sinh {ρ : ℝ} (hρ : 1 < ρ) : ellipseY ρ = Real.sinh (Real.log ρ) := by
  have h0 : 0 < ρ := by linarith
  rw [Real.sinh_eq, Real.exp_neg, Real.exp_log h0, ellipseY]

lemma cos_re_im (w : ℂ) : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im ∧
    (Complex.cos w).im = -(Real.sin w.re * Real.sinh w.im) := by
  conv_lhs => rw [← Complex.re_add_im w]
  conv_rhs => rw [← Complex.re_add_im w]
  rw [Complex.cos_add_mul_I, ← ofReal_cos, ← ofReal_cosh, ← ofReal_sin, ← ofReal_sinh]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, re_add_im]
  constructor <;> ring

/-- The image of the strip `|Im w| ≤ log ρ` under `cos` lies in the Bernstein ellipse. -/
lemma cos_mem_ellipse {ρ : ℝ} (hρ : 1 < ρ) {w : ℂ} (hw : |w.im| ≤ Real.log ρ) :
    Complex.cos w ∈ ellipse ρ := by
  have hX := ellipseX_pos hρ
  have hY := ellipseY_pos hρ
  have hXc := ellipseX_eq_cosh hρ
  have hYs := ellipseY_eq_sinh hρ
  simp only [ellipse, Set.mem_setOf_eq, (cos_re_im w).1, (cos_re_im w).2]
  set a := w.re
  set b := w.im
  have hcosh : Real.cosh b ≤ ellipseX ρ := by
    rw [hXc, Real.cosh_le_cosh, abs_of_nonneg (Real.log_nonneg hρ.le)]; exact hw
  have hsinh : |Real.sinh b| ≤ ellipseY ρ := by
    rw [hYs, Real.abs_sinh]
    exact Real.sinh_le_sinh.2 hw
  have hc0 : 0 ≤ Real.cosh b := (Real.cosh_pos b).le
  have h1 : (Real.cos a * Real.cosh b / ellipseX ρ) ^ 2 ≤ Real.cos a ^ 2 := by
    rw [div_pow, mul_pow, div_le_iff₀ (by positivity)]
    have : Real.cosh b ^ 2 ≤ ellipseX ρ ^ 2 := pow_le_pow_left₀ hc0 hcosh 2
    nlinarith [sq_nonneg (Real.cos a)]
  have h2 : (-(Real.sin a * Real.sinh b) / ellipseY ρ) ^ 2 ≤ Real.sin a ^ 2 := by
    rw [neg_div, neg_sq]
    rw [div_pow, mul_pow, div_le_iff₀ (by positivity)]
    have : Real.sinh b ^ 2 ≤ ellipseY ρ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hsinh 2
    nlinarith [sq_nonneg (Real.sin a)]
  have := Real.cos_sq_add_sin_sq a
  linarith

/-- Fourier (cosine) coefficient of `F ∘ cos`. -/
def chebCoeff (F : ℂ → ℂ) (k : ℤ) : ℂ :=
  (1 / (2 * π : ℝ)) * ∫ θ in (0 : ℝ)..(2 * π), Complex.exp (-(k : ℂ) * θ * I) * F (Complex.cos θ)

lemma chebCoeff_bound_nat {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hF : AnalyticOnNhd ℂ F (ellipse ρ))
    (hbound : ∀ z ∈ ellipse ρ, ‖F z‖ ≤ M) (k : ℕ) :
    ‖chebCoeff F k‖ ≤ M * ρ⁻¹ ^ k := by
  set s := Real.log ρ
  have hs : 0 < s := Real.log_pos hρ
  set h : ℂ → ℂ := fun w => Complex.exp (-(k : ℂ) * w * I) * F (Complex.cos w) with hh
  have hdiff : DifferentiableOn ℂ h (Set.uIcc (0 : ℝ) (2 * π) ×ℂ Set.uIcc (-s) 0) := by
    intro w hw
    have him : |w.im| ≤ s := by
      have := hw.2
      rw [Set.mem_preimage, Set.uIcc_of_le (by linarith)] at this
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    have hFd : DifferentiableAt ℂ F (Complex.cos w) :=
      (hF _ (cos_mem_ellipse hρ him)).differentiableAt
    exact ((by fun_prop : Differentiable ℂ fun w : ℂ => Complex.exp (-(k : ℂ) * w * I)) w).mul
      (hFd.comp w (Complex.differentiable_cos w)) |>.differentiableWithinAt
  have hrect := integral_boundary_rect_eq_zero_of_differentiableOn h (-s * I) (2 * π)
    (by simpa using hdiff)
  have hper : ∀ y : ℝ, h ((2 * π : ℝ) + y * I) = h (0 + y * I) := by
    intro y
    simp only [hh, zero_add]
    congr 1
    · have hE : Complex.exp (-(k : ℂ) * (2 * π * I)) = 1 := by
        have := Complex.exp_int_mul_two_pi_mul_I (-(k : ℤ)); simpa using this
      rw [show -(k : ℂ) * (((2 * π : ℝ) : ℂ) + y * I) * I =
          -(k : ℂ) * (y * I) * I + -(k : ℂ) * (2 * π * I) by push_cast; ring,
        Complex.exp_add, hE, mul_one]
    · rw [add_comm, show ((2 * π : ℝ) : ℂ) = 2 * π by push_cast; ring, Complex.cos_add_two_pi]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, mul_zero, mul_one, zero_mul, sub_zero, neg_zero,
    Complex.mul_im, add_zero, Complex.re_ofNat, Complex.im_ofNat] at hrect
  have hv : (∫ y : ℝ in -s..0, h (((2 * π : ℝ) : ℂ) + y * I)) =
      ∫ y : ℝ in -s..0, h (((0 : ℝ) : ℂ) + y * I) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [hper y, Complex.ofReal_zero]
  rw [hv, add_sub_cancel_right, sub_eq_zero] at hrect
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hbound _ (cos_mem_ellipse hρ (w := 0) (by simp; positivity)))
  have hbd : ∀ x ∈ Set.uIoc (0 : ℝ) (2 * π), ‖h (x + ((-s : ℝ) : ℂ) * I)‖ ≤ M * ρ⁻¹ ^ k := by
    intro x _
    simp only [hh, norm_mul, Complex.norm_exp]
    have hre : (-(k : ℂ) * ((x : ℂ) + ((-s : ℝ) : ℂ) * I) * I).re = -(k * s) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have hexp : Real.exp (-(k * s)) = ρ⁻¹ ^ k := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by linarith), inv_pow]
    rw [hexp, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply hbound
    apply cos_mem_ellipse hρ
    simp [abs_of_pos hs, s]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [hrect] at hnorm
  have hcc : chebCoeff F k = (1 / (2 * π : ℝ)) * ∫ x : ℝ in (0 : ℝ)..(2 * π), h (x + ((0 : ℝ) : ℂ) * I) := by
    unfold chebCoeff
    congr 1
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp [hh]
  rw [hcc, norm_mul]
  have hpi : 0 < 2 * π := by positivity
  rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  rw [sub_zero, abs_of_pos hpi] at hnorm
  calc 1 / (2 * π) * ‖∫ x : ℝ in (0 : ℝ)..(2 * π), h (x + ((0 : ℝ) : ℂ) * I)‖
      ≤ 1 / (2 * π) * (M * ρ⁻¹ ^ k * (2 * π)) := by gcongr
    _ = M * ρ⁻¹ ^ k := by field_simp

lemma chebCoeff_neg (F : ℂ → ℂ) (k : ℤ) : chebCoeff F (-k) = chebCoeff F k := by
  unfold chebCoeff
  congr 1
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => Complex.exp (-(k : ℂ) * θ * I) * F (Complex.cos θ)) (2 * π) (a := 0) (b := 2 * π)
  simp only [sub_zero, sub_self] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  congr 1
  · have hE : Complex.exp ((k : ℂ) * (2 * π * I)) = 1 := Complex.exp_int_mul_two_pi_mul_I k
    rw [show -(((-k : ℤ) : ℂ)) * (θ : ℂ) * I = -(k : ℂ) * (((2 * π - θ : ℝ)) : ℂ) * I +
      (k : ℂ) * (2 * π * I) by push_cast; ring, Complex.exp_add, hE, mul_one]
  · rw [show (((2 * π - θ : ℝ)) : ℂ) = -(θ : ℂ) + 2 * π by push_cast; ring,
      Complex.cos_add_two_pi, Complex.cos_neg]

lemma chebCoeff_bound {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hF : AnalyticOnNhd ℂ F (ellipse ρ))
    (hbound : ∀ z ∈ ellipse ρ, ‖F z‖ ≤ M) (k : ℤ) :
    ‖chebCoeff F k‖ ≤ M * ρ⁻¹ ^ k.natAbs := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa using chebCoeff_bound_nat hρ hF hbound m
  · simpa [chebCoeff_neg] using chebCoeff_bound_nat hρ hF hbound m


lemma cheb_series {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hF : AnalyticOnNhd ℂ F (ellipse ρ))
    (hbound : ∀ z ∈ ellipse ρ, ‖F z‖ ≤ M) (θ : ℝ) :
    HasSum (fun k : ℕ => 2 * chebCoeff F k * (Real.cos (k * θ) : ℂ))
      (F (Real.cos θ) + chebCoeff F 0) := by
  haveI : Fact (0 < 2 * π) := ⟨by positivity⟩
  set g : ℝ → ℂ := fun θ => F (Real.cos θ) with hg
  have hgc : Continuous g := hF.continuousOn.comp_continuous (by fun_prop)
    (fun θ => real_mem_ellipse hρ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
  have hper : Function.Periodic g (2 * π) := fun θ => by simp only [hg]; rw [Real.cos_add_two_pi]
  let f : C(AddCircle (2 * π), ℂ) := ⟨hper.lift, continuous_coinduced_dom.mpr hgc⟩
  have hf : ∀ x : ℝ, f x = g x := fun x => hper.lift_coe x
  have hcoeff : ∀ n : ℤ, fourierCoeff f n = chebCoeff F n := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add, chebCoeff, Complex.real_smul]
    congr 1
    · push_cast; ring
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [smul_eq_mul, hf, hg, fourier_coe_apply, Complex.ofReal_cos]
    congr 2
    push_cast
    field_simp
  have hsum : Summable (fourierCoeff f) := by
    have hr : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
    have hr0 : 0 ≤ ρ⁻¹ := by positivity
    have hgeo : Summable (fun k : ℕ => M * ρ⁻¹ ^ k) :=
      (summable_geometric_of_lt_one hr0 hr).mul_left M
    apply Summable.of_norm
    apply Summable.of_nat_of_neg
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hgeo
      rw [hcoeff]; simpa using chebCoeff_bound hρ hF hbound k
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hgeo
      rw [hcoeff]; simpa using chebCoeff_bound hρ hF hbound (-k)
  have h1 := (has_pointwise_sum_fourier_series_of_summable hsum (θ : AddCircle (2 * π))).nat_add_neg
  rw [hf] at h1
  simp only [hcoeff, fourier_coe_apply, chebCoeff_neg, smul_eq_mul, Int.cast_zero, mul_zero,
    zero_mul, zero_div, Complex.exp_zero, mul_one] at h1
  convert h1 using 1
  funext k
  rw [Complex.ofReal_cos, Complex.cos]
  push_cast
  have e1 : 2 * (π : ℂ) * I * k * θ / (2 * π) = k * θ * I := by field_simp
  have e2 : 2 * (π : ℂ) * I * -(k : ℂ) * θ / (2 * π) = -(k * θ) * I := by field_simp
  rw [e1, e2]
  ring


lemma cheb_eval_cos (k : ℕ) (θ : ℝ) :
    (Polynomial.Chebyshev.T ℝ k).eval (Real.cos θ) = Real.cos (k * θ) := by
  exact_mod_cast Polynomial.Chebyshev.T_real_cos θ (k : ℤ)

lemma cheb_abs_le_one (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ k).eval t| ≤ 1 := by
  rw [← Real.cos_arccos ht.1 ht.2, cheb_eval_cos]
  exact Real.abs_cos_le_one _

lemma integral_cos_mul_sin (k : ℕ) (hk : 2 ≤ k) :
    ∫ θ in (0 : ℝ)..π, Real.cos (k * θ) * Real.sin θ =
      -(1 + (-1) ^ k) / ((k : ℝ) ^ 2 - 1) := by
  have hk1 : (k : ℝ) ^ 2 - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  set G : ℝ → ℝ := fun θ => (Real.cos (k * θ) * Real.cos θ + k * Real.sin (k * θ) * Real.sin θ) /
    ((k : ℝ) ^ 2 - 1) with hG
  have hd : ∀ θ ∈ Set.uIcc (0 : ℝ) π, HasDerivAt G (Real.cos (k * θ) * Real.sin θ) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => (k : ℝ) * θ) k θ := by
      simpa using (hasDerivAt_id θ).const_mul (k : ℝ)
    have := ((((h1.cos).mul (Real.hasDerivAt_cos θ)).add
      (((h1.sin).const_mul (k : ℝ)).mul (Real.hasDerivAt_sin θ))).div_const ((k : ℝ) ^ 2 - 1))
    convert this using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [hG, mul_zero, Real.cos_zero, Real.sin_zero, Real.cos_pi, Real.sin_pi, mul_one]
  have : Real.cos (k * π) = (-1) ^ k := by
    rw [Real.cos_nat_mul_pi]
  rw [this]
  field_simp
  ring

lemma integral_cheb (k : ℕ) (hk : 2 ≤ k) :
    ∫ t in (-1 : ℝ)..1, (Polynomial.Chebyshev.T ℝ k).eval t =
      -(1 + (-1) ^ k) / ((k : ℝ) ^ 2 - 1) := by
  rw [← integral_cos_mul_sin k hk]
  have h := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := π) (f := Real.cos)
    (f' := fun θ => -Real.sin θ) (g := fun t => (Polynomial.Chebyshev.T ℝ k).eval t)
    (fun θ _ => Real.hasDerivAt_cos θ) (by fun_prop) (Polynomial.continuous _)
  simp only [Function.comp_def, cheb_eval_cos, Real.cos_zero, Real.cos_pi, mul_neg,
    intervalIntegral.integral_neg] at h
  rw [intervalIntegral.integral_symm (-1) 1] at h
  linarith

lemma cheb_natDegree (k : ℕ) : (Polynomial.Chebyshev.T ℝ k).natDegree = k := by
  rw [Polynomial.Chebyshev.natDegree_T]; simp

lemma cheb_gauss_err_zero {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ} (hx : IsGaussNodes x)
    {k : ℕ} (hk : k < 2 * n) :
    (∫ t in (-1 : ℝ)..1, (Polynomial.Chebyshev.T ℝ k).eval t) -
      gaussSum x (Polynomial.Chebyshev.T ℝ k).eval = 0 := by
  rw [gauss_exact hn hx _ (by rw [cheb_natDegree]; exact hk), sub_self]

lemma abs_gaussSum_cheb_le {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ} (hx : IsGaussNodes x) (k : ℕ) :
    |gaussSum x (Polynomial.Chebyshev.T ℝ k).eval| ≤ 2 := by
  unfold gaussSum
  calc |∑ i, gaussWeight n (x i) * (Polynomial.Chebyshev.T ℝ k).eval (x i)|
      ≤ ∑ i, |gaussWeight n (x i) * (Polynomial.Chebyshev.T ℝ k).eval (x i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, gaussWeight n (x i) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_pos (gaussWeight_pos hx i)]
        have h1 := (hx.2 i).1
        have := cheb_abs_le_one k ⟨h1.1.le, h1.2.le⟩
        have := gaussWeight_pos hx i
        nlinarith
    _ = 2 := gaussWeight_sum hn hx

lemma cheb_gauss_err_bound {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ} (hx : IsGaussNodes x)
    {k : ℕ} (hk : 2 * n ≤ k) :
    |(∫ t in (-1 : ℝ)..1, (Polynomial.Chebyshev.T ℝ k).eval t) -
      gaussSum x (Polynomial.Chebyshev.T ℝ k).eval| ≤ 32 / 15 := by
  have hQ := abs_gaussSum_cheb_le hn hx k
  rw [integral_cheb k (by omega)]
  rcases (show k = 2 ∨ k = 3 ∨ 4 ≤ k by omega) with rfl | rfl | h4
  · have hn1 : n = 1 := by omega
    subst hn1
    have hx0 : x 0 = 0 := by
      have := (hx.2 0).2
      simpa [legendre] using this
    have hw : gaussWeight 1 0 = 2 := by
      have := gaussWeight_sum hn hx
      simpa [hx0] using this
    have hQ2 : gaussSum x (Polynomial.Chebyshev.T ℝ ((2 : ℕ) : ℤ)).eval = -2 := by
      simp [gaussSum, hw, hx0, Polynomial.Chebyshev.T_two]
    rw [hQ2]
    norm_num [abs_of_pos]
  · norm_num
    exact hQ.trans (by norm_num)
  · have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast h4
    have hpos : (0 : ℝ) < (k : ℝ) ^ 2 - 1 := by nlinarith
    have hI : |-(1 + (-1 : ℝ) ^ k) / ((k : ℝ) ^ 2 - 1)| ≤ 2 / 15 := by
      rw [abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos (by norm_num)]
      have : |-(1 + (-1 : ℝ) ^ k)| ≤ 2 := by
        rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h] <;> norm_num
      nlinarith
    calc _ ≤ |-(1 + (-1 : ℝ) ^ k) / ((k : ℝ) ^ 2 - 1)| +
          |gaussSum x (Polynomial.Chebyshev.T ℝ k).eval| := abs_sub _ _
      _ ≤ 2 / 15 + 2 := add_le_add hI hQ
      _ = 32 / 15 := by norm_num

lemma cheb_series_t {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hF : AnalyticOnNhd ℂ F (ellipse ρ))
    (hbound : ∀ z ∈ ellipse ρ, ‖F z‖ ≤ M) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => 2 * chebCoeff F k * (((Polynomial.Chebyshev.T ℝ k).eval t : ℝ) : ℂ))
      (F t + chebCoeff F 0) := by
  have h := cheb_series hρ hF hbound (Real.arccos t)
  rw [Real.cos_arccos ht.1 ht.2] at h
  convert h using 1
  funext k
  rw [← cheb_eval_cos k, Real.cos_arccos ht.1 ht.2]

lemma glError_eq {n : ℕ} (hn : 0 < n) {ρ M : ℝ} (hρ : 1 < ρ) :
    64 / 15 * M * ρ⁻¹ ^ (2 * n) * (1 - ρ⁻¹)⁻¹ = glError n ρ M := by
  unfold glError
  obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
  rw [hm, show m + 1 - 1 = m by omega]
  have h0 : ρ ≠ 0 := by positivity
  have h1 : ρ - 1 ≠ 0 := by linarith
  have h2 : 1 - ρ⁻¹ = (ρ - 1) / ρ := by field_simp
  rw [h2, inv_pow]
  field_simp
  ring

lemma affine_ofReal (a b t : ℝ) :
    affine a b (t : ℂ) = (((a + b) / 2 + (b - a) / 2 * t : ℝ) : ℂ) := by
  unfold affine; push_cast; ring

theorem gauss_error_complex {n : ℕ} (hn : 0 < n)
    {x : Fin n → ℝ} (hx : IsGaussNodes x)
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ) (hM : 0 ≤ M)
    (hF : AnalyticOnNhd ℂ F (ellipse ρ))
    (hbound : ∀ z ∈ ellipse ρ, ‖F z‖ ≤ M) :
    IntervalIntegrable (fun t : ℝ => F t) MeasureTheory.volume (-1) 1 ∧
      ‖(∫ t in (-1 : ℝ)..1, F t) - gaussSumC x F‖ ≤ glError n ρ M := by
  have hIcc : Set.uIcc (-1 : ℝ) 1 = Set.Icc (-1) 1 := Set.uIcc_of_le (by norm_num)
  have hcont : ContinuousOn (fun t : ℝ => F t) (Set.uIcc (-1) 1) :=
    hF.continuousOn.comp Complex.continuous_ofReal.continuousOn
      (fun t ht => real_mem_ellipse hρ (by rwa [hIcc] at ht))
  have hint : IntervalIntegrable (fun t : ℝ => F t) MeasureTheory.volume (-1) 1 :=
    hcont.intervalIntegrable
  refine ⟨hint, ?_⟩
  set c := chebCoeff F with hc
  set T : ℕ → Polynomial ℝ := fun k => Polynomial.Chebyshev.T ℝ k with hT
  set e : ℕ → ℝ := fun k => (∫ t in (-1 : ℝ)..1, (T k).eval t) - gaussSum x (T k).eval with he
  have hr : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
  have hr0 : 0 ≤ ρ⁻¹ := by positivity
  have hcb : ∀ k : ℕ, ‖c k‖ ≤ M * ρ⁻¹ ^ k := chebCoeff_bound_nat hρ hF hbound
  -- integral of the series
  have hI : HasSum (fun k : ℕ => ∫ t in (-1 : ℝ)..1, 2 * c k * (((T k).eval t : ℝ) : ℂ))
      (∫ t in (-1 : ℝ)..1, (F t + c 0)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k _ => 2 * (M * ρ⁻¹ ^ k)) (fun k => ?_) (fun k => ?_) ?_ ?_ ?_
    · exact (Continuous.continuousOn (by fun_prop)).aestronglyMeasurable measurableSet_uIoc
    · refine Filter.Eventually.of_forall fun t ht => ?_
      have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
        rw [← hIcc]; exact Set.uIoc_subset_uIcc ht
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hTk : |(T k).eval t| ≤ 1 := cheb_abs_le_one k ht'
      have h2n : ‖(2 : ℂ)‖ = 2 := by simp
      have := mul_le_mul (hcb k) hTk (abs_nonneg _) (by positivity)
      rw [h2n]
      linarith
    · exact Filter.Eventually.of_forall fun t _ =>
        ((summable_geometric_of_lt_one hr0 hr).mul_left M).mul_left 2
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun t ht => ?_
      have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
        rw [← hIcc]; exact Set.uIoc_subset_uIcc ht
      exact cheb_series_t hρ hF hbound ht'
  have hS : HasSum (fun k : ℕ => ∑ i, (gaussWeight n (x i) : ℂ) *
      (2 * c k * (((T k).eval (x i) : ℝ) : ℂ))) (∑ i, (gaussWeight n (x i) : ℂ) * (F (x i) + c 0)) :=
    hasSum_sum fun i _ => (cheb_series_t hρ hF hbound
      ⟨(hx.2 i).1.1.le, (hx.2 i).1.2.le⟩).mul_left _
  have hD := hI.sub hS
  have hterm : ∀ k : ℕ, (∫ t in (-1 : ℝ)..1, 2 * c k * (((T k).eval t : ℝ) : ℂ)) -
      ∑ i, (gaussWeight n (x i) : ℂ) * (2 * c k * (((T k).eval (x i) : ℝ) : ℂ)) =
      2 * c k * (e k : ℂ) := by
    intro k
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    simp only [he, gaussSum]
    push_cast
    rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hval : (∫ t in (-1 : ℝ)..1, (F t + c 0)) -
      ∑ i, (gaussWeight n (x i) : ℂ) * (F (x i) + c 0) =
      (∫ t in (-1 : ℝ)..1, F t) - gaussSumC x F := by
    rw [intervalIntegral.integral_add hint intervalIntegrable_const, intervalIntegral.integral_const]
    have hw : ∑ i, (gaussWeight n (x i) : ℂ) = 2 := by
      exact_mod_cast gaussWeight_sum hn hx
    simp only [gaussSumC, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw]
    rw [Complex.real_smul]
    push_cast
    ring
  simp only [hterm, hval] at hD
  -- shift by 2n
  have hD2 := (hasSum_nat_add_iff' (2 * n)).mpr hD
  have hz : ∑ i ∈ Finset.range (2 * n), 2 * c i * (e i : ℂ) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    have : e i = 0 := cheb_gauss_err_zero hn hx hi
    simp [this]
  rw [hz, sub_zero] at hD2
  have hgeo := (hasSum_geometric_of_lt_one hr0 hr).mul_left (64 / 15 * M * ρ⁻¹ ^ (2 * n))
  rw [← glError_eq hn hρ]
  refine hD2.norm_le_of_bounded hgeo fun j => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := hcb (j + 2 * n)
  have h2 : |e (j + 2 * n)| ≤ 32 / 15 := cheb_gauss_err_bound hn hx (by omega)
  have h3 : (0 : ℝ) ≤ M * ρ⁻¹ ^ (j + 2 * n) := by positivity
  calc ‖(2 : ℂ)‖ * ‖c (j + 2 * n)‖ * |e (j + 2 * n)|
      ≤ 2 * (M * ρ⁻¹ ^ (j + 2 * n)) * (32 / 15) := by
        have h2n : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h2n, mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) h3) (by norm_num)
    _ = 64 / 15 * M * ρ⁻¹ ^ (2 * n) * ρ⁻¹ ^ j := by rw [pow_add]; ring

theorem gauss_error_real_affine {n : ℕ} (hn : 0 < n)
    {x : Fin n → ℝ} (hx : IsGaussNodes x)
    {f : ℝ → ℝ} {F : ℂ → ℂ} {a b ρ M : ℝ}
    (hab : a < b) (hρ : 1 < ρ) (hM : 0 ≤ M)
    (hF : AnalyticOnNhd ℂ F ((affine a b) '' ellipse ρ))
    (hbound : ∀ z ∈ ellipse ρ, ‖F (affine a b z)‖ ≤ M)
    (hagrees : ∀ t ∈ Set.Ioo a b, F t = (f t : ℂ)) :
    IntervalIntegrable f MeasureTheory.volume a b ∧
      |(∫ t in a..b, f t) -
        ((b - a) / 2) *
          gaussSum x (fun t => f ((a + b) / 2 + (b - a) / 2 * t))|
        ≤ glError n ρ (((b - a) / 2) * M) := by
  set h := (b - a) / 2 with hh
  set d := (a + b) / 2 with hd
  have hh0 : 0 < h := by rw [hh]; linarith
  have hda : d + h * (-1) = a := by rw [hh, hd]; ring
  have hdb : d + h * 1 = b := by rw [hh, hd]; ring
  have hmemIoo : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, d + h * t ∈ Set.Ioo a b := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  have hφ : ∀ t : ℝ, affine a b t = ((d + h * t : ℝ) : ℂ) := fun t => affine_ofReal a b t
  set G : ℂ → ℂ := fun z => (h : ℂ) * F (affine a b z) with hG
  have hGa : AnalyticOnNhd ℂ G (ellipse ρ) := by
    intro z hz
    have haff : AnalyticAt ℂ (affine a b) z := by
      unfold affine
      exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    exact analyticAt_const.mul ((hF _ ⟨z, hz, rfl⟩).comp haff)
  have hGb : ∀ z ∈ ellipse ρ, ‖G z‖ ≤ h * M := by
    intro z hz
    rw [hG, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh0]
    exact mul_le_mul_of_nonneg_left (hbound z hz) hh0.le
  obtain ⟨-, hGe⟩ := gauss_error_complex hn hx hρ (by positivity) hGa hGb
  have hGt : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, G t = ((h * f (d + h * t) : ℝ) : ℂ) := by
    intro t ht
    show (h : ℂ) * F (affine a b t) = _
    rw [hφ, hagrees _ (hmemIoo t ht)]
    push_cast; rfl
  -- integrability of f
  have hcont : ContinuousOn (fun u : ℝ => (F u).re) (Set.uIcc a b) := by
    intro u hu
    rw [Set.uIcc_of_le hab.le] at hu
    have hmem : (u : ℂ) ∈ affine a b '' ellipse ρ := by
      refine ⟨(((u - d) / h : ℝ) : ℂ), real_mem_ellipse hρ ⟨?_, ?_⟩, ?_⟩
      · rw [le_div_iff₀ hh0]; rw [hh, hd]; linarith [hu.1]
      · rw [div_le_iff₀ hh0]; rw [hh, hd]; linarith [hu.2]
      · rw [hφ]; congr 1; field_simp; ring
    exact (Complex.continuous_re.continuousAt.comp
      ((hF _ hmem).continuousAt.comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  have hfint : IntervalIntegrable f MeasureTheory.volume a b := by
    refine hcont.intervalIntegrable.congr_ae ?_
    rw [Set.uIoc_of_le hab.le, Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine (MeasureTheory.Measure.ae_ne MeasureTheory.volume b).mono fun u hub hu => ?_
    simp [hagrees u ⟨hu.1, lt_of_le_of_ne hu.2 hub⟩]
  refine ⟨hfint, ?_⟩
  -- the integral
  have hI : (∫ t in (-1 : ℝ)..1, G t) = ((∫ t in a..b, f t : ℝ) : ℂ) := by
    have h1 : (∫ t in (-1 : ℝ)..1, G t) = ∫ t in (-1 : ℝ)..1, (((h * f (d + h * t)) : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [Set.uIoc_of_le (by norm_num)]
      exact (MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)).mono
        fun t h1 ht => hGt t ⟨ht.1, lt_of_le_of_ne ht.2 h1⟩
    rw [h1, intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_mul _ hh0.ne', hda, hdb, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hh0.ne', one_mul]
  have hQ : gaussSumC x G = ((h * gaussSum x (fun t => f (d + h * t)) : ℝ) : ℂ) := by
    unfold gaussSumC gaussSum
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hGt _ (hx.2 i).1]
    push_cast; ring
  rw [hI, hQ, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hGe
  exact hGe

end Intgrl
