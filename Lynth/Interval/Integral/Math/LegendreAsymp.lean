import Lynth.Interval.Integral.Math.IntgrlDefs

/-!
Auxiliary analytic facts for the Stieltjes asymptotic expansion of the
Legendre polynomials (used for `Intgrl.legendre_asymptotic`).

For `0 < θ < π` put `A = 2 sin θ (sin θ + i cos θ) = 1 - e^{-2iθ}` and
`I_n = ∫_0^1 (1-σ²)^n (A-σ²)^{-1/2} dσ`.  Then
`P_n(cos θ) = (4/π) Re (e^{inθ} I_n)`, and expanding `(A-σ²)^{-1/2}` in
powers of `σ²/A` with an explicit remainder gives the expansion with error
at most twice the first neglected term.
-/

noncomputable section

open scoped BigOperators
open Complex

namespace Intgrl.Asymp

/-- `A = 1 - e^{-2iθ}`. -/
def A (θ : ℝ) : ℂ := 2 * (Real.sin θ : ℂ) * ((Real.sin θ : ℂ) + (Real.cos θ : ℂ) * I)

/-- Principal square root of `A - r`. -/
def Sq (θ r : ℝ) : ℂ := (A θ - r) ^ (2⁻¹ : ℂ)

/-- `e^{iθ}`. -/
def E (θ : ℝ) : ℂ := (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I

/-- The integrals `I_n`. -/
def In (θ : ℝ) (n : ℕ) : ℂ :=
  ∫ σ in (0 : ℝ)..1, (((1 - σ ^ 2) ^ n : ℝ) : ℂ) * (Sq θ (σ ^ 2))⁻¹

/-- Wallis-type integrals. -/
def W (n k : ℕ) : ℝ := ∫ σ in (0 : ℝ)..1, (1 - σ ^ 2) ^ n * σ ^ (2 * k)

/-- Binomial coefficients of `(1-u)^{-1/2}`. -/
def cc : ℕ → ℝ
  | 0 => 1
  | k + 1 => cc k * (2 * k + 1) / (2 * k + 2)

section basic

variable {θ : ℝ}

lemma A_re : (A θ).re = 2 * Real.sin θ ^ 2 := by
  simp [A, sin_ofReal_re, cos_ofReal_re]; ring

lemma A_im : (A θ).im = 2 * Real.sin θ * Real.cos θ := by
  simp [A, sin_ofReal_re, cos_ofReal_re, sin_ofReal_im, cos_ofReal_im]

lemma sub_mem_slitPlane (hθ0 : 0 < θ) (hθπ : θ < Real.pi) {r : ℝ} (hr : r ≤ 1) :
    A θ - r ∈ slitPlane := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  rw [mem_slitPlane_iff]
  by_cases hc : Real.cos θ = 0
  · left
    have := Real.sin_sq_add_cos_sq θ
    simp only [sub_re, A_re, ofReal_re]
    nlinarith
  · right
    simp only [sub_im, A_im, ofReal_im, sub_zero]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hs.ne') hc

lemma cpow_half_re_pos {z : ℂ} (hz : z ∈ slitPlane) : 0 < (z ^ (2⁻¹ : ℂ)).re := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  rw [cpow_def_of_ne_zero hz0, exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have h1 := neg_pi_lt_arg z
  have h2 : z.arg ≠ Real.pi := (mem_slitPlane_iff_arg.1 hz).1
  have h3 := arg_le_pi z
  have h4 : z.arg < Real.pi := lt_of_le_of_ne h3 h2
  have : (log z * 2⁻¹).im = z.arg / 2 := by
    simp [log_im]; ring
  rw [this]
  constructor <;> linarith

lemma cpow_half_sq (z : ℂ) : (z ^ (2⁻¹ : ℂ)) ^ 2 = z := by
  simp

lemma cpow_half_of_sq {w : ℂ} (hw : 0 < w.re) : (w ^ 2) ^ (2⁻¹ : ℂ) = w := by
  have h := abs_arg_lt_pi_div_two_iff.2 (Or.inl hw)
  rw [abs_lt] at h
  have := pow_cpow_nat_inv (x := w) (n := 2) two_ne_zero (by push_cast; linarith)
    (by push_cast; linarith)
  simpa using this

lemma Sq_sq (θ r : ℝ) : Sq θ r ^ 2 = A θ - r := cpow_half_sq _

lemma Sq_ne_zero (hθ0 : 0 < θ) (hθπ : θ < Real.pi) {r : ℝ} (hr : r ≤ 1) : Sq θ r ≠ 0 := by
  intro h
  have := Sq_sq θ r
  rw [h] at this
  exact slitPlane_ne_zero (sub_mem_slitPlane hθ0 hθπ hr) (by simpa using this.symm)

lemma Sq_re_pos (hθ0 : 0 < θ) (hθπ : θ < Real.pi) {r : ℝ} (hr : r ≤ 1) : 0 < (Sq θ r).re :=
  cpow_half_re_pos (sub_mem_slitPlane hθ0 hθπ hr)

lemma Sq_hasDerivAt (hθ0 : 0 < θ) (hθπ : θ < Real.pi) {r : ℝ} (hr : r ≤ 1) :
    HasDerivAt (fun r : ℝ => Sq θ r) (-(2⁻¹ : ℂ) * (Sq θ r)⁻¹) r := by
  have hsl := sub_mem_slitPlane hθ0 hθπ hr
  have h1 : HasDerivAt (fun r : ℝ => A θ - (r : ℂ)) (-1) r := by
    simpa using ((hasDerivAt_id r).ofReal_comp).const_sub (A θ)
  have h2 : HasDerivAt (fun z : ℂ => z ^ (2⁻¹ : ℂ))
      ((2⁻¹ : ℂ) * (A θ - r) ^ ((2⁻¹ : ℂ) - 1)) (A θ - r) := by
    simpa using (hasStrictDerivAt_cpow_const (c := (2⁻¹ : ℂ)) hsl).hasDerivAt
  have h3 := h2.comp r h1
  have hne : A θ - (r : ℂ) ≠ 0 := slitPlane_ne_zero hsl
  have hsq := Sq_ne_zero hθ0 hθπ hr
  convert h3 using 1
  · funext s
    rfl
  · rw [cpow_sub _ _ hne, cpow_one]
    have hS : A θ - (r : ℂ) = Sq θ r ^ 2 := (Sq_sq θ r).symm
    change -(2⁻¹ : ℂ) * (Sq θ r)⁻¹ = 2⁻¹ * (Sq θ r / (A θ - r)) * (-1)
    rw [hS]
    field_simp

lemma sq_le_one_of_mem {σ : ℝ} (hσ : σ ∈ Set.uIcc (0 : ℝ) 1) : σ ^ 2 ≤ 1 := by
  rw [Set.uIcc_of_le zero_le_one] at hσ
  nlinarith [hσ.1, hσ.2]

lemma Sqσ_hasDerivAt (hθ0 : 0 < θ) (hθπ : θ < Real.pi) {σ : ℝ} (hσ : σ ^ 2 ≤ 1) :
    HasDerivAt (fun σ : ℝ => Sq θ (σ ^ 2)) (-(σ : ℂ) * (Sq θ (σ ^ 2))⁻¹) σ := by
  have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * σ) σ := by simpa using hasDerivAt_pow 2 σ
  have hS : HasDerivAt (fun r : ℝ => Sq θ r) (-(2⁻¹ : ℂ) * (Sq θ (σ ^ 2))⁻¹)
      ((fun x : ℝ => x ^ 2) σ) := Sq_hasDerivAt hθ0 hθπ hσ
  have h1 := HasDerivAt.scomp (h := fun x : ℝ => x ^ 2) σ hS hp
  convert h1 using 1
  · funext x
    rfl
  · simp only [real_smul]
    push_cast
    ring_nf

lemma Sqσ_inv_continuousOn (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    ContinuousOn (fun σ : ℝ => (Sq θ (σ ^ 2))⁻¹) (Set.uIcc 0 1) := by
  intro σ hσ
  have h := sq_le_one_of_mem hσ
  exact ((Sqσ_hasDerivAt hθ0 hθπ h).continuousAt.inv₀
    (Sq_ne_zero hθ0 hθπ h)).continuousWithinAt

lemma integrand_intervalIntegrable (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (j : ℕ) :
    IntervalIntegrable (fun σ : ℝ => (((1 - σ ^ 2) ^ j : ℝ) : ℂ) * (Sq θ (σ ^ 2))⁻¹)
      MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul _ (Sqσ_inv_continuousOn hθ0 hθπ)
  fun_prop

/-- Integration by parts: the three-term recurrence of the `I_n`. -/
lemma In_rec (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (n : ℕ) :
    (2 * n + 4 : ℂ) * In θ (n + 2) - (2 * n + 3) * (2 - A θ) * In θ (n + 1)
      + 2 * (n + 1) * (1 - A θ) * In θ n = 0 := by
  set Ψ : ℝ → ℂ := fun σ => (σ : ℂ) * (((1 - σ ^ 2) ^ (n + 1) : ℝ) : ℂ) * Sq θ (σ ^ 2)
  have hd : ∀ σ ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Ψ
      ((2 * n + 4 : ℂ) * ((((1 - σ ^ 2) ^ (n + 2) : ℝ) : ℂ) * (Sq θ (σ ^ 2))⁻¹)
        - (2 * n + 3) * (2 - A θ) * ((((1 - σ ^ 2) ^ (n + 1) : ℝ) : ℂ) * (Sq θ (σ ^ 2))⁻¹)
        + 2 * (n + 1) * (1 - A θ) * ((((1 - σ ^ 2) ^ n : ℝ) : ℂ) * (Sq θ (σ ^ 2))⁻¹)) σ := by
    intro σ hσ
    have h := sq_le_one_of_mem hσ
    have hS := Sqσ_hasDerivAt hθ0 hθπ h
    have hne := Sq_ne_zero hθ0 hθπ h
    have hsq := Sq_sq θ (σ ^ 2)
    have hg : HasDerivAt (fun σ : ℝ => ((σ * (1 - σ ^ 2) ^ (n + 1) : ℝ) : ℂ))
        (((1 - σ ^ 2) ^ (n + 1) + σ * ((n + 1 : ℝ) * (1 - σ ^ 2) ^ n * (-(2 * σ))) : ℝ) : ℂ)
        σ := by
      apply HasDerivAt.ofReal_comp
      have := (hasDerivAt_id σ).mul (((hasDerivAt_id σ).pow 2).const_sub 1 |>.pow (n + 1))
      convert this using 1
      · funext y
        simp
      · simp
    have := hg.mul hS
    convert this using 1
    · funext x; simp [Ψ]
    · field_simp
      push_cast at hsq ⊢
      linear_combination (-(((1 - σ ^ 2) ^ (n + 1) : ℂ)) +
        2 * (n + 1) * σ ^ 2 * (1 - σ ^ 2) ^ n) * hsq
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    refine ((((integrand_intervalIntegrable hθ0 hθπ (n + 2)).const_mul _).sub
      ((integrand_intervalIntegrable hθ0 hθπ (n + 1)).const_mul _)).add
      ((integrand_intervalIntegrable hθ0 hθπ n).const_mul _)))
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  · simp only [Ψ] at hint
    unfold In
    rw [hint]; simp
  all_goals first
    | exact (integrand_intervalIntegrable hθ0 hθπ _).const_mul _
    | exact (((integrand_intervalIntegrable hθ0 hθπ _).const_mul _).sub
        ((integrand_intervalIntegrable hθ0 hθπ _).const_mul _))

/-- The first step: `2 I_1 = (2 - A) I_0 + √(A - 1)`. -/
lemma In_one (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    2 * In θ 1 - (2 - A θ) * In θ 0 = Sq θ 1 := by
  set Ψ : ℝ → ℂ := fun σ => (σ : ℂ) * Sq θ (σ ^ 2)
  have hd : ∀ σ ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Ψ
      (2 * ((((1 - σ ^ 2) ^ 1 : ℝ) : ℂ) * (Sq θ (σ ^ 2))⁻¹)
        - (2 - A θ) * ((((1 - σ ^ 2) ^ 0 : ℝ) : ℂ) * (Sq θ (σ ^ 2))⁻¹)) σ := by
    intro σ hσ
    have h := sq_le_one_of_mem hσ
    have hS := Sqσ_hasDerivAt hθ0 hθπ h
    have hne := Sq_ne_zero hθ0 hθπ h
    have hsq := Sq_sq θ (σ ^ 2)
    have := ((hasDerivAt_id σ).ofReal_comp).mul hS
    simp only [id] at this
    convert this using 1
    field_simp
    push_cast at hsq ⊢
    linear_combination (-1 : ℂ) * hsq
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    refine (((integrand_intervalIntegrable hθ0 hθπ 1).const_mul _).sub
      ((integrand_intervalIntegrable hθ0 hθπ 0).const_mul _)))
  rw [intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  · simp only [Ψ] at hint
    unfold In
    rw [hint]; simp
  all_goals exact (integrand_intervalIntegrable hθ0 hθπ _).const_mul _

lemma Sq_one (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    Sq θ 1 = (Real.sin θ : ℂ) + (Real.cos θ : ℂ) * I := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have h : A θ - ((1 : ℝ) : ℂ) = ((Real.sin θ : ℂ) + (Real.cos θ : ℂ) * I) ^ 2 := by
    have hcs := Real.sin_sq_add_cos_sq θ
    unfold A
    generalize Real.sin θ = s at *
    generalize Real.cos θ = c at *
    have hcs' : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
    push_cast
    linear_combination hcs' - (c : ℂ) ^ 2 * I_sq
  unfold Sq
  rw [h]
  apply cpow_half_of_sq
  have hre : ((Real.sin θ : ℂ) + (Real.cos θ : ℂ) * I).re = Real.sin θ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
  rw [hre]
  exact hs

/-- The angle `π/4 - θ/2` of `√A`. -/
lemma Sq_zero (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    Sq θ 0 = (Real.sqrt (2 * Real.sin θ) : ℂ) *
      ((Real.cos (Real.pi / 4 - θ / 2) : ℂ) + (Real.sin (Real.pi / 4 - θ / 2) : ℂ) * I) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have h2α : 2 * (Real.pi / 4 - θ / 2) = Real.pi / 2 - θ := by ring
  have hc2 : Real.cos (Real.pi / 4 - θ / 2) ^ 2 - Real.sin (Real.pi / 4 - θ / 2) ^ 2
      = Real.sin θ := by
    have e : Real.sin θ = Real.cos (2 * (Real.pi / 4 - θ / 2)) := by
      rw [h2α, Real.cos_pi_div_two_sub]
    rw [e, Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq (Real.pi / 4 - θ / 2)
    linarith
  have hs2 : 2 * Real.sin (Real.pi / 4 - θ / 2) * Real.cos (Real.pi / 4 - θ / 2)
      = Real.cos θ := by
    have e : Real.cos θ = Real.sin (2 * (Real.pi / 4 - θ / 2)) := by
      rw [h2α, Real.sin_pi_div_two_sub]
    rw [e, Real.sin_two_mul]
  have hcpos : 0 < Real.cos (Real.pi / 4 - θ / 2) := by
    apply Real.cos_pos_of_mem_Ioo; constructor <;> linarith
  have hsq : Real.sqrt (2 * Real.sin θ) ^ 2 = 2 * Real.sin θ := Real.sq_sqrt (by linarith)
  have hsqpos : 0 < Real.sqrt (2 * Real.sin θ) := Real.sqrt_pos.2 (by linarith)
  have h : A θ - ((0 : ℝ) : ℂ) = ((Real.sqrt (2 * Real.sin θ) : ℂ) *
      ((Real.cos (Real.pi / 4 - θ / 2) : ℂ) + (Real.sin (Real.pi / 4 - θ / 2) : ℂ) * I)) ^ 2 := by
    unfold A
    generalize Real.sin θ = s at *
    generalize Real.cos θ = c at *
    generalize Real.cos (Real.pi / 4 - θ / 2) = ca at *
    generalize Real.sin (Real.pi / 4 - θ / 2) = sa at *
    generalize Real.sqrt (2 * s) = r at *
    have e1 : (ca : ℂ) ^ 2 - (sa : ℂ) ^ 2 = s := by exact_mod_cast hc2
    have e2 : 2 * (sa : ℂ) * ca = c := by exact_mod_cast hs2
    have e3 : (r : ℂ) ^ 2 = 2 * s := by exact_mod_cast hsq
    push_cast
    linear_combination (-(r : ℂ) ^ 2) * e1 + (-(r : ℂ) ^ 2 * I) * e2 + (-(s : ℂ) -
      (c : ℂ) * I) * e3 + (-(r : ℂ) ^ 2 * (sa : ℂ) ^ 2) * I_sq
  unfold Sq
  rw [h]
  apply cpow_half_of_sq
  simp only [mul_re, ofReal_re, ofReal_im, add_re, I_re, I_im]
  simp
  positivity

/-- Algebraic identities for `E = e^{iθ}`. -/
lemma E_mul_two_sub_A : E θ * (2 - A θ) = 2 * Real.cos θ := by
  have hcs := Real.sin_sq_add_cos_sq θ
  unfold E A
  generalize Real.sin θ = s at *
  generalize Real.cos θ = c at *
  have hcs' : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  linear_combination (-2 * (s : ℂ) * I) * hcs' + (-2 * (s : ℂ) ^ 2 * (c : ℂ)) * I_sq

lemma E_sq_mul_one_sub_A : E θ ^ 2 * (1 - A θ) = 1 := by
  have hcs := Real.sin_sq_add_cos_sq θ
  unfold E A
  generalize Real.sin θ = s at *
  generalize Real.cos θ = c at *
  have hcs' : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  linear_combination ((1 - 2 * (s : ℂ) ^ 2) * s ^ 2 - 4 * (s : ℂ) ^ 2 * c ^ 2
    - 2 * (s : ℂ) ^ 3 * c * I) * I_sq + ((1 + 2 * (s : ℂ) ^ 2) - 2 * (c : ℂ) * s * I) * hcs'

lemma E_mul_Sq_one (hθ0 : 0 < θ) (hθπ : θ < Real.pi) : E θ * Sq θ 1 = I := by
  rw [Sq_one hθ0 hθπ]
  have hcs := Real.sin_sq_add_cos_sq θ
  unfold E
  generalize Real.sin θ = s at *
  generalize Real.cos θ = c at *
  have hcs' : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  linear_combination I * hcs' + ((s : ℂ) * c) * I_sq

lemma arg_polar {r x : ℝ} (hr : 0 < r) (hx1 : -Real.pi < x) (hx2 : x ≤ Real.pi) :
    ((r : ℂ) * ((Real.cos x : ℂ) + (Real.sin x : ℂ) * I)).arg = x := by
  rw [arg_real_mul _ hr, ofReal_cos, ofReal_sin]
  exact arg_cos_add_sin_mul_I ⟨hx1, hx2⟩

lemma In_zero_re (hθ0 : 0 < θ) (hθπ : θ < Real.pi) : (In θ 0).re = Real.pi / 4 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  set F : ℝ → ℂ := fun σ => -I * log (Sq θ (σ ^ 2) + I * σ)
  have hd : ∀ σ ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F
      ((((1 - σ ^ 2) ^ 0 : ℝ) : ℂ) * (Sq θ (σ ^ 2))⁻¹) σ := by
    intro σ hσ
    have h := sq_le_one_of_mem hσ
    have hS := Sqσ_hasDerivAt hθ0 hθπ h
    have hne := Sq_ne_zero hθ0 hθπ h
    have hre := Sq_re_pos hθ0 hθπ h
    have hg : HasDerivAt (fun σ : ℝ => Sq θ (σ ^ 2) + I * σ) (-(σ : ℂ) * (Sq θ (σ ^ 2))⁻¹ + I)
        σ := by
      have := hS.add (((hasDerivAt_id σ).ofReal_comp).const_mul I)
      convert this using 1
      · funext y
        rfl
      · simp
    have hmem : Sq θ (σ ^ 2) + I * σ ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left; simpa using hre
    have hne2 : Sq θ (σ ^ 2) + I * σ ≠ 0 := slitPlane_ne_zero hmem
    have := (hg.clog_real hmem).const_mul (-I)
    convert this using 1
    simp only [pow_zero, ofReal_one, one_mul]
    field_simp
    linear_combination (Sq θ (σ ^ 2)) * I_sq
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (integrand_intervalIntegrable hθ0 hθπ 0)
  unfold In
  rw [hint]
  simp only [F, sub_re, neg_mul, neg_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, log_im,
    log_re, neg_neg]
  simp only [ofReal_one, one_pow, mul_one, ofReal_zero, mul_zero, add_zero]
  have h1 : Sq θ 1 + I = ((2 * Real.cos (θ / 2) : ℝ) : ℂ) *
      ((Real.cos (Real.pi / 2 - θ / 2) : ℂ) + (Real.sin (Real.pi / 2 - θ / 2) : ℂ) * I) := by
    rw [Sq_one hθ0 hθπ, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    have e1 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      rw [← Real.sin_two_mul]; ring_nf
    have e2 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
      rw [← Real.cos_two_mul]; ring_nf
    rw [e1, e2]
    push_cast
    ring
  have hc2 : 0 < Real.cos (θ / 2) := by
    apply Real.cos_pos_of_mem_Ioo; constructor <;> linarith
  have hsq : 0 < Real.sqrt (2 * Real.sin θ) := Real.sqrt_pos.2 (by linarith)
  rw [h1, show ((0 : ℝ) ^ 2) = 0 by norm_num, Sq_zero hθ0 hθπ,
    arg_polar (by positivity) (by linarith) (by linarith),
    arg_polar hsq (by linarith) (by linarith)]
  ring

lemma legendre_eq_In (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (n : ℕ) :
    (legendre n).eval (Real.cos θ) = 4 / Real.pi * (E θ ^ n * In θ n).re := by
  have hpi := Real.pi_pos
  have h0 : (legendre 0).eval (Real.cos θ) = 4 / Real.pi * (E θ ^ 0 * In θ 0).re := by
    simp [legendre, In_zero_re hθ0 hθπ]
  have h1 : (legendre 1).eval (Real.cos θ) = 4 / Real.pi * (E θ ^ 1 * In θ 1).re := by
    have h := In_one hθ0 hθπ
    have hE := E_mul_two_sub_A (θ := θ)
    have hS := E_mul_Sq_one hθ0 hθπ
    have : E θ * In θ 1 = Real.cos θ * In θ 0 + I / 2 := by
      linear_combination (E θ / 2) * h + (In θ 0 / 2) * hE + hS / 2
    rw [pow_one, this]
    simp [legendre, In_zero_re hθ0 hθπ, cos_ofReal_re]
    field_simp
  have key : ∀ m, (legendre m).eval (Real.cos θ) = 4 / Real.pi * (E θ ^ m * In θ m).re ∧
      (legendre (m + 1)).eval (Real.cos θ) = 4 / Real.pi * (E θ ^ (m + 1) * In θ (m + 1)).re := by
    intro m
    induction m with
    | zero => exact ⟨h0, h1⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have hrec := In_rec hθ0 hθπ m
      have hE1 := E_mul_two_sub_A (θ := θ)
      have hE2 := E_sq_mul_one_sub_A (θ := θ)
      have G : (((2 * m + 4 : ℝ)) : ℂ) * (E θ ^ (m + 2) * In θ (m + 2))
          - (((2 * m + 3) * (2 * Real.cos θ) : ℝ) : ℂ) * (E θ ^ (m + 1) * In θ (m + 1))
          + ((2 * (m + 1) : ℝ) : ℂ) * (E θ ^ m * In θ m) = 0 := by
        simp only [ofReal_mul, ofReal_add, ofReal_natCast, ofReal_ofNat, ofReal_one]
        linear_combination E θ ^ (m + 2) * hrec
          + (2 * m + 3) * E θ ^ (m + 1) * In θ (m + 1) * hE1
          - 2 * (m + 1) * E θ ^ m * In θ m * hE2
      have Gre := congrArg Complex.re G
      simp only [add_re, sub_re, re_ofReal_mul, zero_re] at Gre
      have e2 : (legendre (m + 2)).eval (Real.cos θ) =
          (2 * m + 3) / (m + 2) * Real.cos θ * (legendre (m + 1)).eval (Real.cos θ)
            - (m + 1) / (m + 2) * (legendre m).eval (Real.cos θ) := by
        simp [legendre]
      show (legendre (m + 2)).eval (Real.cos θ) = 4 / Real.pi * (E θ ^ (m + 2) * In θ (m + 2)).re
      rw [e2, ih.1, ih.2]
      field_simp
      linear_combination (-1 / 2 : ℝ) * Gre
  exact (key n).1

end basic

section wallis

lemma W_ibp (n k : ℕ) :
    (2 * k + 1 : ℝ) * W n k - (2 * k + 2 * n + 3) * W n (k + 1) = 0 := by
  have hd : ∀ σ ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
      (fun σ : ℝ => (1 - σ ^ 2) ^ (n + 1) * σ ^ (2 * k + 1))
      ((2 * k + 1 : ℝ) * ((1 - σ ^ 2) ^ n * σ ^ (2 * k))
        - (2 * k + 2 * n + 3) * ((1 - σ ^ 2) ^ n * σ ^ (2 * (k + 1)))) σ := by
    intro σ _
    have h1 : HasDerivAt (fun σ : ℝ => (1 - σ ^ 2) ^ (n + 1))
        (((n + 1 : ℕ) : ℝ) * (1 - σ ^ 2) ^ n * (-(2 * σ))) σ := by
      have := ((hasDerivAt_pow 2 σ).const_sub 1).pow (n + 1)
      convert this using 1
      simp
    have h2 : HasDerivAt (fun σ : ℝ => σ ^ (2 * k + 1)) (((2 * k + 1 : ℕ) : ℝ) * σ ^ (2 * k)) σ := by
      simpa using hasDerivAt_pow (2 * k + 1) σ
    convert h1.mul h2 using 1
    rw [pow_succ (1 - σ ^ 2) n, pow_succ σ (2 * k), show 2 * (k + 1) = 2 * k + 2 by ring,
      pow_add σ (2 * k) 2]
    push_cast
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    apply Continuous.intervalIntegrable; fun_prop)
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  · unfold W; rw [hint]; simp
  all_goals apply Continuous.intervalIntegrable; fun_prop

lemma W_succ_right (n k : ℕ) :
    W n (k + 1) = (2 * k + 1) / (2 * n + 2 * k + 3) * W n k := by
  have := W_ibp n k
  field_simp
  linarith

lemma W_succ_left (n k : ℕ) : W (n + 1) k = W n k - W n (k + 1) := by
  unfold W
  rw [← intervalIntegral.integral_sub]
  · congr 1; funext σ; ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

lemma W_zero_zero : W 0 0 = 1 := by simp [W]

lemma W_zero (n : ℕ) : W n 0 = 4 ^ n / ((2 * n + 1) * (Nat.centralBinom n : ℝ)) := by
  induction n with
  | zero => simp [W_zero_zero]
  | succ n ih =>
    rw [W_succ_left, W_succ_right, ih]
    have h := Nat.succ_mul_centralBinom_succ n
    have h' : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
        2 * (2 * n + 1) * (Nat.centralBinom n : ℝ) := by exact_mod_cast h
    have hpos : (0 : ℝ) < Nat.centralBinom n := by exact_mod_cast Nat.centralBinom_pos n
    have hC : (Nat.centralBinom (n + 1) : ℝ) = 2 * (2 * n + 1) * (Nat.centralBinom n : ℝ) /
        ((n : ℝ) + 1) := by
      field_simp; linarith
    rw [hC]
    push_cast
    field_simp
    ring

lemma W_nonneg (n k : ℕ) : 0 ≤ W n k := by
  unfold W
  apply intervalIntegral.integral_nonneg zero_le_one
  intro σ hσ
  have : 0 ≤ 1 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
  exact mul_nonneg (pow_nonneg this n) (pow_nonneg hσ.1 _)

lemma cc_succ (k : ℕ) : ((k : ℝ) + 1) * cc (k + 1) = ((k : ℝ) + 1 / 2) * cc k := by
  simp only [cc]; field_simp

lemma cc_nonneg (k : ℕ) : 0 ≤ cc k := by
  induction k with
  | zero => simp [cc]
  | succ k ih => simp only [cc]; positivity

end wallis

section remainder

/-- Partial sums of the binomial series of `(1-u)^{-1/2}` and their derivatives. -/
def Tsum (K : ℕ) (u : ℂ) : ℂ := ∑ k ∈ Finset.range K, (cc k : ℂ) * u ^ k

def Tder (K : ℕ) (u : ℂ) : ℂ := ∑ k ∈ Finset.range K, (cc k : ℂ) * (k : ℂ) * u ^ (k - 1)

lemma Tsum_hasDerivAt (K : ℕ) (u : ℂ) : HasDerivAt (Tsum K) (Tder K u) u := by
  unfold Tsum Tder
  have := HasDerivAt.sum (u := Finset.range K) (A := fun k (z : ℂ) => (cc k : ℂ) * z ^ k)
    (A' := fun k => (cc k : ℂ) * ((k : ℂ) * u ^ (k - 1))) (x := u)
    (fun k _ => (hasDerivAt_pow k u).const_mul _)
  convert this using 1
  · funext z; simp
  · simp [mul_assoc]

lemma Tsum_zero (m : ℕ) : Tsum (m + 1) 0 = 1 := by
  simp [Tsum, Finset.sum_range_succ', cc]

lemma Tsum_ode (m : ℕ) (u : ℂ) :
    Tsum (m + 1) u / 2 - (1 - u) * Tder (m + 1) u =
      ((((m : ℝ) + 1 / 2) * cc m : ℝ) : ℂ) * u ^ m := by
  induction m with
  | zero => simp [Tsum, Tder, cc]
  | succ m ih =>
    have hcc : ((m : ℂ) + 1) * cc (m + 1) = ((m : ℂ) + 1 / 2) * cc m := by
      have h := congrArg (fun x : ℝ => (x : ℂ)) (cc_succ m)
      push_cast at h
      linear_combination h
    unfold Tsum Tder at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k => (cc k : ℂ) * (k : ℂ) * u ^ (k - 1))]
    push_cast at ih ⊢
    linear_combination ih - u ^ m * hcc

variable {θ : ℝ}

/-- The truncated expansion of `(A - r)^{-1/2}`. -/
def Tθ (θ : ℝ) (K : ℕ) (r : ℝ) : ℂ := (Sq θ 0)⁻¹ * Tsum K (r / A θ)

lemma norm_A (hθ0 : 0 < θ) (hθπ : θ < Real.pi) : ‖A θ‖ = 2 * Real.sin θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  unfold A
  rw [norm_mul, norm_mul]
  have h1 : ‖(Real.sin θ : ℂ) + (Real.cos θ : ℂ) * I‖ = 1 := by
    have hcs := Real.sin_sq_add_cos_sq θ
    have : ‖(Real.sin θ : ℂ) + (Real.cos θ : ℂ) * I‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, normSq_apply]
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, add_im, mul_im]
      linear_combination hcs
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  norm_num

lemma norm_A_sub_ge (hθ0 : 0 < θ) (hθπ : θ < Real.pi) {r : ℝ} (hr1 : r ≤ 1) :
    Real.sin θ ≤ ‖A θ - r‖ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hcs := Real.sin_sq_add_cos_sq θ
  have h2 : ‖A θ - r‖ ^ 2 = (2 * Real.sin θ ^ 2 - r) ^ 2 + (2 * Real.sin θ * Real.cos θ) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]
    simp only [sub_re, sub_im, A_re, A_im, ofReal_re, ofReal_im, sub_zero]
    ring
  have h3 : Real.sin θ ^ 2 ≤ ‖A θ - r‖ ^ 2 := by
    rw [h2]
    have h4 : 0 ≤ Real.sin θ ^ 2 * ((1 - r) * (3 - r)) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))
    have h5 : (2 * Real.sin θ ^ 2 - r) ^ 2 + (2 * Real.sin θ * Real.cos θ) ^ 2 - Real.sin θ ^ 2
        = Real.sin θ ^ 2 * ((1 - r) * (3 - r)) + (r * Real.cos θ) ^ 2 := by
      linear_combination (4 * Real.sin θ ^ 2 - r ^ 2) * hcs
    nlinarith [sq_nonneg (r * Real.cos θ)]
  exact (pow_le_pow_iff_left₀ hs.le (norm_nonneg _) two_ne_zero).1 h3

lemma norm_Sq_sq (θ r : ℝ) : ‖Sq θ r‖ ^ 2 = ‖A θ - r‖ := by
  rw [← norm_pow, Sq_sq]

lemma sqrt_sin_le_norm_Sq (hθ0 : 0 < θ) (hθπ : θ < Real.pi) {r : ℝ} (hr1 : r ≤ 1) : Real.sqrt (Real.sin θ) ≤ ‖Sq θ r‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (Sq θ r)), norm_Sq_sq]
  exact Real.sqrt_le_sqrt (norm_A_sub_ge hθ0 hθπ hr1)

lemma norm_Sq_zero (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    ‖Sq θ 0‖ = Real.sqrt (2 * Real.sin θ) := by
  rw [← Real.sqrt_sq (norm_nonneg (Sq θ 0)), norm_Sq_sq]
  simp [norm_A hθ0 hθπ]

/-- The remainder of the binomial expansion is at most twice the first omitted term. -/
lemma rem_bound (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) :
    ‖(Sq θ r)⁻¹ - Tθ θ (m + 1) r‖ ≤
      2 * cc (m + 1) * r ^ (m + 1) / ((2 * Real.sin θ) ^ (m + 1) * Real.sqrt (2 * Real.sin θ)) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hA : A θ ≠ 0 := by
    intro h; have := norm_A hθ0 hθπ; rw [h, norm_zero] at this; linarith
  have hS0 : Sq θ 0 ≠ 0 := Sq_ne_zero hθ0 hθπ (by norm_num)
  set Q : ℝ → ℂ := fun x => 1 - Sq θ x * Tθ θ (m + 1) x with hQ
  set Q' : ℝ → ℂ := fun x => (Sq θ x)⁻¹ * (Sq θ 0)⁻¹ *
    (((((m : ℝ) + 1 / 2) * cc m : ℝ) : ℂ) * ((x : ℂ) / A θ) ^ m) with hQ'
  have hQd : ∀ x : ℝ, x ≤ 1 → HasDerivAt Q (Q' x) x := by
    intro x hx
    have hS := Sq_hasDerivAt hθ0 hθπ hx
    have hSne := Sq_ne_zero hθ0 hθπ hx
    have hsq := Sq_sq θ x
    have hg : HasDerivAt (fun z : ℂ => Tsum (m + 1) (z / A θ))
        (Tder (m + 1) ((x : ℂ) / A θ) * (1 / A θ)) (x : ℂ) := by
      have := (Tsum_hasDerivAt (m + 1) ((x : ℂ) / A θ)).comp (x : ℂ)
        ((hasDerivAt_id (x : ℂ)).div_const (A θ))
      convert this using 1
      · funext z
        rfl
    have hT : HasDerivAt (fun y : ℝ => Tθ θ (m + 1) y)
        ((Sq θ 0)⁻¹ * (Tder (m + 1) ((x : ℂ) / A θ) * (1 / A θ))) x :=
      (hg.comp_ofReal).const_mul _
    have := (hS.mul hT).const_sub 1
    convert this using 1
    have hode := Tsum_ode m ((x : ℂ) / A θ)
    simp only [hQ']
    rw [← hode]
    unfold Tθ
    have h1 : (1 : ℂ) - (x : ℂ) / A θ = Sq θ x ^ 2 / A θ := by
      rw [hsq]; field_simp
    rw [h1]
    field_simp
    ring
  set Cst : ℝ := cc (m + 1) /
    ((2 * Real.sin θ) ^ m * Real.sqrt (Real.sin θ) * Real.sqrt (2 * Real.sin θ)) with hCst
  have hB : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Cst * x ^ (m + 1))
      (Cst * ((m + 1 : ℕ) * x ^ m)) x := by
    intro x
    have := (hasDerivAt_pow (m + 1) x).const_mul Cst
    simpa using this
  have hsqs : 0 < Real.sqrt (Real.sin θ) := Real.sqrt_pos.2 hs
  have hsq2s : 0 < Real.sqrt (2 * Real.sin θ) := Real.sqrt_pos.2 (by linarith)
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) 1, ‖Q' x‖ ≤ Cst * ((m + 1 : ℕ) * x ^ m) := by
    intro x hx
    have hnS := sqrt_sin_le_norm_Sq hθ0 hθπ hx.2.le
    simp only [hQ', norm_mul, norm_inv, norm_pow, norm_div, Complex.norm_real,
      Real.norm_eq_abs, norm_A hθ0 hθπ, norm_Sq_zero hθ0 hθπ, abs_of_nonneg hx.1]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1 / 2), abs_of_nonneg (cc_nonneg m)]
    have hcc := cc_succ m
    calc ‖Sq θ x‖⁻¹ * (Real.sqrt (2 * Real.sin θ))⁻¹ *
          ((m + 1 / 2) * cc m * (x / (2 * Real.sin θ)) ^ m)
        ≤ (Real.sqrt (Real.sin θ))⁻¹ * (Real.sqrt (2 * Real.sin θ))⁻¹ *
          (((m : ℝ) + 1 / 2) * cc m * (x / (2 * Real.sin θ)) ^ m) := by
          have := cc_nonneg m
          have := hx.1
          gcongr
      _ = Cst * ((m + 1 : ℕ) * x ^ m) := by
          rw [hCst]
          push_cast
          rw [div_pow]
          field_simp
          linear_combination (-2 * x ^ m) * hcc
  have hQ0 : ‖Q 0‖ ≤ Cst * 0 ^ (m + 1) := by
    simp only [hQ, Tθ, ofReal_zero, zero_div, Tsum_zero]
    rw [mul_inv_cancel_left₀ hS0]
    simp
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := Q)
    (f' := Q') (fun x hx => (hQd x hx.2).continuousAt.continuousWithinAt)
    (fun x hx => (hQd x hx.2.le).hasDerivWithinAt) hQ0 hB hbound ⟨hr0, hr1⟩
  have hSr := Sq_ne_zero hθ0 hθπ hr1
  have hnS := sqrt_sin_le_norm_Sq hθ0 hθπ hr1
  have heq : (Sq θ r)⁻¹ - Tθ θ (m + 1) r = Q r / Sq θ r := by
    simp only [hQ]; field_simp
  rw [heq, norm_div]
  calc ‖Q r‖ / ‖Sq θ r‖ ≤ Cst * r ^ (m + 1) / Real.sqrt (Real.sin θ) := by
        apply div_le_div₀ (by have := cc_nonneg (m + 1); positivity) key hsqs hnS
    _ = _ := by
        rw [hCst]
        have h2 : Real.sqrt (2 * Real.sin θ) ^ 2 = 2 * Real.sin θ := Real.sq_sqrt (by linarith)
        have h3 : Real.sqrt (Real.sin θ) ^ 2 = Real.sin θ := Real.sq_sqrt hs.le
        field_simp
        rw [pow_succ, h3]
        ring

end remainder

section assembly

variable {θ : ℝ}

lemma In_sub_sum (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (n K : ℕ) :
    In θ n - ∑ k ∈ Finset.range K, ((cc k * W n k : ℝ) : ℂ) * ((Sq θ 0)⁻¹ * (A θ)⁻¹ ^ k) =
      ∫ σ in (0 : ℝ)..1, (((1 - σ ^ 2) ^ n : ℝ) : ℂ) *
        ((Sq θ (σ ^ 2))⁻¹ - Tθ θ K (σ ^ 2)) := by
  have hT : ∀ σ : ℝ, (((1 - σ ^ 2) ^ n : ℝ) : ℂ) * Tθ θ K (σ ^ 2) =
      ∑ k ∈ Finset.range K, ((cc k : ℂ) * ((Sq θ 0)⁻¹ * (A θ)⁻¹ ^ k)) *
        (((1 - σ ^ 2) ^ n * σ ^ (2 * k) : ℝ) : ℂ) := by
    intro σ
    unfold Tθ Tsum
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    rw [div_pow, pow_mul, div_eq_mul_inv, inv_pow]
    ring
  have hcont : ∀ k : ℕ, IntervalIntegrable (fun σ : ℝ => ((cc k : ℂ) *
      ((Sq θ 0)⁻¹ * (A θ)⁻¹ ^ k)) * (((1 - σ ^ 2) ^ n * σ ^ (2 * k) : ℝ) : ℂ))
      MeasureTheory.volume 0 1 := by
    intro k
    apply Continuous.intervalIntegrable
    fun_prop
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub (integrand_intervalIntegrable hθ0 hθπ n)]
  · simp_rw [hT]
    rw [intervalIntegral.integral_finset_sum (fun k _ => hcont k)]
    unfold In
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    unfold W
    push_cast
    ring
  · simp_rw [hT]
    exact (continuous_finset_sum _ fun k _ => by fun_prop).intervalIntegrable _ _

lemma In_expansion (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (n m : ℕ) :
    ‖In θ n - ∑ k ∈ Finset.range (m + 1), ((cc k * W n k : ℝ) : ℂ) *
        ((Sq θ 0)⁻¹ * (A θ)⁻¹ ^ k)‖ ≤
      2 * cc (m + 1) * W n (m + 1) /
        ((2 * Real.sin θ) ^ (m + 1) * Real.sqrt (2 * Real.sin θ)) := by
  rw [In_sub_sum hθ0 hθπ]
  set D := (2 * Real.sin θ) ^ (m + 1) * Real.sqrt (2 * Real.sin θ)
  have hle := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := 1)
    (μ := MeasureTheory.volume)
    (f := fun σ : ℝ => (((1 - σ ^ 2) ^ n : ℝ) : ℂ) * ((Sq θ (σ ^ 2))⁻¹ - Tθ θ (m + 1) (σ ^ 2)))
    (g := fun σ : ℝ => (2 * cc (m + 1) / D) * ((1 - σ ^ 2) ^ n * σ ^ (2 * (m + 1))))
    zero_le_one (by
      filter_upwards with σ hσ
      have h0 : 0 ≤ σ ^ 2 := sq_nonneg σ
      have h1 : σ ^ 2 ≤ 1 := by nlinarith [hσ.1, hσ.2]
      have hb := rem_bound hθ0 hθπ m h0 h1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
        (pow_nonneg (by linarith) n)]
      calc (1 - σ ^ 2) ^ n * ‖(Sq θ (σ ^ 2))⁻¹ - Tθ θ (m + 1) (σ ^ 2)‖
          ≤ (1 - σ ^ 2) ^ n * (2 * cc (m + 1) * (σ ^ 2) ^ (m + 1) / D) := by
            gcongr
        _ = _ := by rw [← pow_mul]; ring)
    (by apply Continuous.intervalIntegrable; fun_prop)
  refine hle.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul]
  unfold W
  ring

lemma norm_E (θ : ℝ) : ‖E θ‖ = 1 := by
  have hcs := Real.sin_sq_add_cos_sq θ
  have : ‖E θ‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, normSq_apply]
    simp only [E, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, add_im, mul_im]
    linear_combination hcs
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this

lemma re_term (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (n k : ℕ) :
    (E θ ^ n * ((Sq θ 0)⁻¹ * (A θ)⁻¹ ^ k)).re =
      Real.cos (((n : ℝ) + k + 1 / 2) * θ - ((k : ℝ) + 1 / 2) * Real.pi / 2) /
        ((2 * Real.sin θ) ^ k * Real.sqrt (2 * Real.sin θ)) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hE : E θ = exp ((θ : ℂ) * I) := by
    rw [E, ofReal_cos, ofReal_sin, ← exp_mul_I]
  have hA : A θ = ((2 * Real.sin θ : ℝ) : ℂ) * exp (((Real.pi / 2 - θ : ℝ) : ℂ) * I) := by
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    unfold A
    simp only [ofReal_mul, ofReal_ofNat]
  have hS : Sq θ 0 = ((Real.sqrt (2 * Real.sin θ) : ℝ) : ℂ) *
      exp (((Real.pi / 4 - θ / 2 : ℝ) : ℂ) * I) := by
    rw [Sq_zero hθ0 hθπ, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  set a := Real.pi / 4 - θ / 2
  set b := Real.pi / 2 - θ
  have key : E θ ^ n * ((Sq θ 0)⁻¹ * (A θ)⁻¹ ^ k) =
      (((Real.sqrt (2 * Real.sin θ))⁻¹ * ((2 * Real.sin θ)⁻¹) ^ k : ℝ) : ℂ) *
        exp (((n * θ - a - k * b : ℝ) : ℂ) * I) := by
    rw [hE, hA, hS]
    have e1 : exp ((θ : ℂ) * I) ^ n = exp ((n : ℂ) * ((θ : ℂ) * I)) := (exp_nat_mul _ n).symm
    have e2 : (exp ((a : ℂ) * I))⁻¹ = exp (-((a : ℂ) * I)) := (exp_neg _).symm
    have e3 : ((exp ((b : ℂ) * I))⁻¹) ^ k = exp ((k : ℂ) * (-((b : ℂ) * I))) := by
      rw [exp_nat_mul, exp_neg]
    calc _
        = (((Real.sqrt (2 * Real.sin θ))⁻¹ * ((2 * Real.sin θ)⁻¹) ^ k : ℝ) : ℂ) *
          (exp ((θ : ℂ) * I) ^ n * (exp ((a : ℂ) * I))⁻¹ * ((exp ((b : ℂ) * I))⁻¹) ^ k) := by
          push_cast; ring
      _ = _ := by
          rw [e1, e2, e3, ← exp_add, ← exp_add]
          congr 2
          push_cast
          ring
  rw [key, re_ofReal_mul, exp_ofReal_mul_I_re]
  have hang : (n : ℝ) * θ - a - k * b =
      ((n : ℝ) + k + 1 / 2) * θ - ((k : ℝ) + 1 / 2) * Real.pi / 2 := by
    simp only [a, b]; ring
  rw [hang]
  have hsq : 0 < Real.sqrt (2 * Real.sin θ) := Real.sqrt_pos.2 (by linarith)
  have h2s : (2 * Real.sin θ) ^ k ≠ 0 := pow_ne_zero _ (by linarith)
  rw [inv_pow]
  field_simp

/-- Stieltjes-type expansion of `P_n(cos θ)` with explicit coefficients `cc k * W n k` and
an error at most twice the first omitted term. -/
theorem legendre_expansion {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (n m : ℕ) :
    |(legendre n).eval (Real.cos θ) - ∑ k ∈ Finset.range (m + 1),
        4 / Real.pi * (cc k * W n k) *
          (Real.cos (((n : ℝ) + k + 1 / 2) * θ - ((k : ℝ) + 1 / 2) * Real.pi / 2) /
            ((2 * Real.sin θ) ^ k * Real.sqrt (2 * Real.sin θ)))| ≤
      4 / Real.pi * (2 * cc (m + 1) * W n (m + 1) /
        ((2 * Real.sin θ) ^ (m + 1) * Real.sqrt (2 * Real.sin θ))) := by
  have hpi := Real.pi_pos
  set S : ℂ := ∑ k ∈ Finset.range (m + 1), ((cc k * W n k : ℝ) : ℂ) * ((Sq θ 0)⁻¹ * (A θ)⁻¹ ^ k)
  have hsum : (E θ ^ n * S).re = ∑ k ∈ Finset.range (m + 1), (cc k * W n k) *
      (Real.cos (((n : ℝ) + k + 1 / 2) * θ - ((k : ℝ) + 1 / 2) * Real.pi / 2) /
        ((2 * Real.sin θ) ^ k * Real.sqrt (2 * Real.sin θ))) := by
    simp only [S, Finset.mul_sum, re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, re_ofReal_mul, re_term hθ0 hθπ]
  rw [legendre_eq_In hθ0 hθπ n]
  have : ∑ k ∈ Finset.range (m + 1), 4 / Real.pi * (cc k * W n k) *
      (Real.cos (((n : ℝ) + k + 1 / 2) * θ - ((k : ℝ) + 1 / 2) * Real.pi / 2) /
        ((2 * Real.sin θ) ^ k * Real.sqrt (2 * Real.sin θ))) = 4 / Real.pi * (E θ ^ n * S).re := by
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [this, ← mul_sub, ← sub_re, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  gcongr
  calc |(E θ ^ n * (In θ n - S)).re| ≤ ‖E θ ^ n * (In θ n - S)‖ := abs_re_le_norm _
    _ = ‖In θ n - S‖ := by rw [norm_mul, norm_pow, norm_E, one_pow, one_mul]
    _ ≤ _ := In_expansion hθ0 hθπ n m

end assembly

end Intgrl.Asymp
