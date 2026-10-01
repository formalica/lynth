import Mathlib
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Lynth.HGIdentities.Common
import Lynth.Hypergeometric

/-!
# The closed form of `₃F̃₂(-1/2, 1, 1; 2, 2; z)`

This file proves
`₃F̃₂(-1/2, 1, 1; 2, 2; z) = (4/9 - 16/(9z)) √(1-z) + 4 log((√(1-z)+1)/2)/(3z) + 16/(9z)`
for `0 < ‖z‖ ≤ 1`.

Since `Γ(2) = 1`, the regularized function coincides here with the classical `₃F₂`.

The proof goes as follows.

* The coefficients of the series are `cₙ = (-1/2)ₙ / ((n+1)² n!)`.
* The antiderivative-type function
  `A z = (4z/9 - 16/9) √(1-z) + 4 log((√(1-z)+1)/2)/3 + 16/9`
  satisfies `A 0 = 0` and `A' z = 2(s² + s + 1)/(3(s+1))` with `s = √(1-z)`, which is exactly the
  sum of the termwise derivatives of `∑ₙ cₙ z^(n+1)` (a shifted binomial series).
* Hence `∑ₙ cₙ z^(n+1) = A z` on the unit disc, and dividing by `z` gives the identity.
* Abel's limit theorem extends the identity to the boundary `‖z‖ = 1`.
-/

open scoped Nat
open Metric

namespace Complex

/-- The coefficients of `₃F̃₂(-1/2, 1, 1; 2, 2; ·)`, namely `(-1/2)ₙ / ((n+1)² n!)`. -/
private noncomputable def coeff3F2 (n : ℕ) : ℂ :=
  (ascPochhammer ℂ n).eval (-1 / 2) / (((n : ℂ) + 1) ^ 2 * (n ! : ℂ))

/-- The closed form of `₃F̃₂(-1/2, 1, 1; 2, 2; z)`. -/
private noncomputable def hyper3F2Closed (z : ℂ) : ℂ :=
  (4 / 9 - 16 / (9 * z)) * Complex.sqrt (1 - z)
    + 4 * Complex.log ((Complex.sqrt (1 - z) + 1) / 2) / (3 * z) + 16 / (9 * z)

/-- `z * hyper3F2Closed z`, the function whose power series is `∑ₙ cₙ z^(n+1)`. -/
private noncomputable def hyper3F2Antideriv (z : ℂ) : ℂ :=
  (4 * z / 9 - 16 / 9) * Complex.sqrt (1 - z)
    + 4 * Complex.log ((Complex.sqrt (1 - z) + 1) / 2) / 3 + 16 / 9

section Coefficients

/-- The coefficients of the regularized `₃F̃₂` with parameters `(-1/2, 1, 1; 2, 2)`. -/
private theorem regularizedHGFunCoeff_3F2 (n : ℕ) :
    regularizedHGFunCoeff {-1 / 2, 1, 1} {2, 2} n = coeff3F2 n := by
  have hG : Gamma (2 + (n : ℂ)) = ((n + 1)! : ℕ) := by
    rw [show (2 + (n : ℂ)) = ((n + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
  have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    have h : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    simpa using h
  rw [coeff3F2]
  simp [regularizedHGFunCoeff, ascPochhammer_eval_one, hG, Nat.factorial_succ]
  field_simp

/-- The binomial coefficients of `√(1-z)` are bounded by `1`. -/
private theorem norm_pochhammer_half_div_factorial_le (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval (-1 / 2) / (n ! : ℂ)‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by
      have h : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      simpa using h
    have hstep : (ascPochhammer ℂ (n + 1)).eval (-1 / 2) / ((n + 1)! : ℂ)
        = ((ascPochhammer ℂ n).eval (-1 / 2) / (n ! : ℂ))
          * ((-1 / 2 + (n : ℂ)) / ((n : ℂ) + 1)) := by
      rw [ascPochhammer_succ_right]
      simp only [Nat.factorial_succ, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp
    rw [hstep, norm_mul]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : ‖(-1 / 2 + (n : ℂ)) / ((n : ℂ) + 1)‖ ≤ 1 := by
      rw [show (-1 / 2 + (n : ℂ)) = ((-1 / 2 + n : ℝ) : ℂ) by push_cast; ring,
        show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_div,
        div_le_one (by positivity), abs_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity), abs_le]
      constructor <;> linarith
    calc ‖(ascPochhammer ℂ n).eval (-1 / 2) / (n ! : ℂ)‖ * ‖(-1 / 2 + (n : ℂ)) / ((n : ℂ) + 1)‖
        ≤ 1 * 1 := mul_le_mul ih h2 (norm_nonneg _) zero_le_one
      _ = 1 := by ring

private theorem norm_coeff3F2_le (n : ℕ) : ‖coeff3F2 n‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    have h : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    simpa using h
  have he : coeff3F2 n = ((ascPochhammer ℂ n).eval (-1 / 2) / (n ! : ℂ)) / ((n : ℂ) + 1) ^ 2 := by
    rw [coeff3F2]; field_simp
  have hnorm : ‖((n : ℂ) + 1) ^ 2‖ = ((n : ℝ) + 1) ^ 2 := by
    rw [norm_pow, show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [he, norm_div, hnorm, div_le_div_iff_of_pos_right (by positivity)]
  exact norm_pochhammer_half_div_factorial_le n

private theorem summable_norm_coeff3F2 : Summable fun n : ℕ => ‖coeff3F2 n‖ := by
  have hbase : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    have h : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    exact ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr h).congr
      fun n => by push_cast; ring
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) norm_coeff3F2_le hbase

end Coefficients

section Series

variable {z : ℂ}

/-- The binomial series for `√(1-z)`. -/
private theorem hasSum_sqrt_one_sub (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (ascPochhammer ℂ n).eval (-1 / 2) / (n ! : ℂ) * z ^ n)
      (Complex.sqrt (1 - z)) := by
  have h := hasSum_regularized1F0 (a := -1 / 2) hz
  rwa [show (-(-1 / 2 : ℂ)) = 2⁻¹ by norm_num] at h

/-- The binomial series for `(1-z)^(3/2) = (1-z) √(1-z)`. -/
private theorem hasSum_one_sub_pow_three_halves (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (ascPochhammer ℂ n).eval (-3 / 2) / (n ! : ℂ) * z ^ n)
      ((1 - z) * Complex.sqrt (1 - z)) := by
  have h := hasSum_regularized1F0 (a := -3 / 2) hz
  have hne : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero' hz
  rwa [show (-(-3 / 2 : ℂ)) = 1 + 2⁻¹ by norm_num, Complex.cpow_add _ _ hne,
    Complex.cpow_one] at h

/-- The termwise integrated binomial series. -/
private theorem hasSum_shifted (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (ascPochhammer ℂ n).eval (-1 / 2) / ((n + 1)! : ℂ) * z ^ (n + 1))
      (2 / 3 * (1 - (1 - z) * Complex.sqrt (1 - z))) := by
  have h := hasSum_one_sub_pow_three_halves hz
  have hshift : HasSum
      (fun n : ℕ => (ascPochhammer ℂ (n + 1)).eval (-3 / 2) / ((n + 1)! : ℂ) * z ^ (n + 1))
      ((1 - z) * Complex.sqrt (1 - z) - 1) := by
    refine (hasSum_nat_add_iff (f := fun n : ℕ => (ascPochhammer ℂ n).eval (-3 / 2) / (n ! : ℂ)
      * z ^ n) 1).mpr ?_
    simpa using h
  have h2 := hshift.mul_left (-2 / 3 : ℂ)
  rw [show (-2 / 3 : ℂ) * ((1 - z) * Complex.sqrt (1 - z) - 1)
      = 2 / 3 * (1 - (1 - z) * Complex.sqrt (1 - z)) by ring] at h2
  refine h2.congr_fun fun n => ?_
  have hp : (ascPochhammer ℂ (n + 1)).eval (-3 / 2)
      = (-3 / 2) * (ascPochhammer ℂ n).eval (-1 / 2) := by
    rw [ascPochhammer_succ_left]; simp; norm_num
  rw [hp]
  ring

/-- The sum of the termwise derivatives of `∑ₙ cₙ z^(n+1)`. -/
private theorem hasSum_deriv_series (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (ascPochhammer ℂ n).eval (-1 / 2) / ((n + 1)! : ℂ) * z ^ n)
      (2 * (Complex.sqrt (1 - z) ^ 2 + Complex.sqrt (1 - z) + 1) /
        (3 * (Complex.sqrt (1 - z) + 1))) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · have hval : 2 * (Complex.sqrt (1 - (0 : ℂ)) ^ 2 + Complex.sqrt (1 - 0) + 1) /
        (3 * (Complex.sqrt (1 - (0 : ℂ)) + 1)) = 1 := by norm_num
    have hfun : (fun n : ℕ => (ascPochhammer ℂ n).eval (-1 / 2) / ((n + 1)! : ℂ) * (0 : ℂ) ^ n)
        = fun n : ℕ => if n = 0 then (1 : ℂ) else 0 := by
      funext n
      cases n <;> simp
    rw [hval, hfun]
    simpa using hasSum_ite_eq (0 : ℕ) (1 : ℂ)
  · have h := (hasSum_shifted hz).mul_left z⁻¹
    have hsq : Complex.sqrt (1 - z) ^ 2 = 1 - z := sqrt_sq_eq _
    have hs1 : Complex.sqrt (1 - z) + 1 ≠ 0 := sqrt_add_one_ne_zero hz
    have hval : z⁻¹ * (2 / 3 * (1 - (1 - z) * Complex.sqrt (1 - z)))
        = 2 * (Complex.sqrt (1 - z) ^ 2 + Complex.sqrt (1 - z) + 1) /
          (3 * (Complex.sqrt (1 - z) + 1)) := by
      set s := Complex.sqrt (1 - z) with hsdef
      clear_value s
      have hzs : z = 1 - s ^ 2 := by rw [hsq]; ring
      subst hzs
      have h1 : (1 : ℂ) - s ≠ 0 := by
        intro h
        exact hz0 (by rw [show (1 : ℂ) - s ^ 2 = (1 - s) * (1 + s) by ring, h, zero_mul])
      field_simp
      ring
    rw [hval] at h
    refine h.congr_fun fun n => ?_
    field_simp
    ring

end Series

section Derivative

variable {z : ℂ}

private theorem hyper3F2Antideriv_zero : hyper3F2Antideriv 0 = 0 := by
  simp [hyper3F2Antideriv]

/-- The derivative of the closed form. -/
private theorem hasDerivAt_hyper3F2Antideriv (hz : ‖z‖ < 1) :
    HasDerivAt hyper3F2Antideriv
      (2 * (Complex.sqrt (1 - z) ^ 2 + Complex.sqrt (1 - z) + 1) /
        (3 * (Complex.sqrt (1 - z) + 1))) z := by
  have hds := hasDerivAt_sqrt_one_sub hz
  have hs : Complex.sqrt (1 - z) ≠ 0 := sqrt_ne_zero' hz
  have hs1 : Complex.sqrt (1 - z) + 1 ≠ 0 := sqrt_add_one_ne_zero hz
  have hre := re_sqrt_pos hz
  have h1 : HasDerivAt (fun w : ℂ => 4 * w / 9 - 16 / 9) (4 / 9) z := by
    simpa using (((hasDerivAt_id z).const_mul (4 : ℂ)).div_const 9).sub_const (16 / 9)
  have hu : HasDerivAt (fun w : ℂ => (Complex.sqrt (1 - w) + 1) / 2)
      ((-(1 / (2 * Complex.sqrt (1 - z)))) / 2) z := (hds.add_const 1).div_const 2
  have hmem : ((Complex.sqrt (1 - z) + 1) / 2) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have hre2 : ((Complex.sqrt (1 - z) + 1) / 2).re = ((Complex.sqrt (1 - z)).re + 1) / 2 := by
      simp
    rw [hre2]
    linarith
  have hlog := hu.clog hmem
  refine (((h1.mul hds).add ((hlog.const_mul (4 : ℂ)).div_const 3)).add_const
    (16 / 9 : ℂ)).congr_deriv ?_
  have hsq : Complex.sqrt (1 - z) ^ 2 = 1 - z := sqrt_sq_eq _
  set s := Complex.sqrt (1 - z) with hsdef
  clear_value s
  have hzs : z = 1 - s ^ 2 := by rw [hsq]; ring
  subst hzs
  field_simp
  ring

/-- The derivative of the power series `∑ₙ cₙ z^(n+1)`. -/
private theorem hasDerivAt_tsum_coeff3F2 (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : ℂ => ∑' n : ℕ, coeff3F2 n * w ^ (n + 1))
      (∑' n : ℕ, coeff3F2 n * ((n : ℂ) + 1) * z ^ n) z := by
  set r : ℝ := (‖z‖ + 1) / 2 with hr
  have hr0 : 0 < r := by simp [hr]; positivity
  have hr1 : r < 1 := by simp [hr]; linarith
  have hzr : z ∈ ball (0 : ℂ) r := by rw [mem_ball_zero_iff, hr]; linarith
  refine hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => r ^ n)
    (g := fun n w => coeff3F2 n * w ^ (n + 1))
    (g' := fun n w => coeff3F2 n * ((n : ℂ) + 1) * w ^ n)
    (summable_geometric_of_lt_one hr0.le hr1) isOpen_ball (convex_ball _ _).isPreconnected
    ?_ ?_ (mem_ball_self hr0) ?_ hzr
  · intro n w _
    have h := (hasDerivAt_pow (n + 1) w).const_mul (coeff3F2 n)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  · intro n w hw
    have hwr : ‖w‖ < r := mem_ball_zero_iff.mp hw
    have h1 : ‖coeff3F2 n * ((n : ℂ) + 1) * w ^ n‖ = ‖coeff3F2 n‖ * ((n : ℝ) + 1) * ‖w‖ ^ n := by
      rw [norm_mul, norm_mul, norm_pow,
        show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h1]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hb : ‖coeff3F2 n‖ * ((n : ℝ) + 1) ^ 2 ≤ 1 := by
      have h := norm_coeff3F2_le n
      rwa [le_div_iff₀ (by positivity)] at h
    have h2 : ‖coeff3F2 n‖ * ((n : ℝ) + 1) ≤ 1 := by
      nlinarith [norm_nonneg (coeff3F2 n)]
    calc ‖coeff3F2 n‖ * ((n : ℝ) + 1) * ‖w‖ ^ n ≤ 1 * r ^ n :=
          mul_le_mul h2 (pow_le_pow_left₀ (norm_nonneg _) hwr.le n) (by positivity) zero_le_one
      _ = r ^ n := one_mul _
  · simp

/-- The power series `∑ₙ cₙ z^(n+1)` equals the antiderivative closed form. -/
private theorem tsum_coeff3F2_succ (hz : ‖z‖ < 1) :
    ∑' n : ℕ, coeff3F2 n * z ^ (n + 1) = hyper3F2Antideriv z := by
  set r : ℝ := (‖z‖ + 1) / 2 with hr
  have hr0 : 0 < r := by simp [hr]; positivity
  have hr1 : r < 1 := by simp [hr]; linarith
  have hzr : z ∈ ball (0 : ℂ) r := by rw [mem_ball_zero_iff, hr]; linarith
  set F : ℂ → ℂ := fun w => (∑' n : ℕ, coeff3F2 n * w ^ (n + 1)) - hyper3F2Antideriv w with hF
  have hmem : ∀ w ∈ ball (0 : ℂ) r, ‖w‖ < 1 := fun w hw =>
    lt_trans (mem_ball_zero_iff.mp hw) hr1
  have hderiv : ∀ w ∈ ball (0 : ℂ) r, HasDerivAt F 0 w := by
    intro w hw
    have hw' := hmem w hw
    have h1 := hasDerivAt_tsum_coeff3F2 hw'
    have h2 := hasDerivAt_hyper3F2Antideriv hw'
    have heq : ∑' n : ℕ, coeff3F2 n * ((n : ℂ) + 1) * w ^ n
        = 2 * (Complex.sqrt (1 - w) ^ 2 + Complex.sqrt (1 - w) + 1) /
          (3 * (Complex.sqrt (1 - w) + 1)) := by
      rw [← (hasSum_deriv_series hw').tsum_eq]
      refine tsum_congr fun n => ?_
      have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hn1 : ((n : ℂ) + 1) ≠ 0 := by
        have h : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
        simpa using h
      rw [coeff3F2, Nat.factorial_succ]
      push_cast
      field_simp
    rw [heq] at h1
    exact (h1.sub h2).congr_deriv (sub_self _)
  have hdiff : DifferentiableOn ℂ F (ball (0 : ℂ) r) := fun w hw =>
    ((hderiv w hw).differentiableAt).differentiableWithinAt
  have hd0 : Set.EqOn (deriv F) 0 (ball (0 : ℂ) r) := fun w hw => by
    simp [(hderiv w hw).deriv]
  have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
    hdiff hd0 hzr (mem_ball_self hr0)
  have hF0 : F 0 = 0 := by simp [hF, hyper3F2Antideriv_zero]
  rw [hF0] at hconst
  have hz' : (∑' n : ℕ, coeff3F2 n * z ^ (n + 1)) - hyper3F2Antideriv z = 0 := hconst
  linear_combination hz'

end Derivative

section Main

variable {z : ℂ}

/-- Absolute convergence of the coefficient series on the closed unit disc. -/
private theorem summable_coeff3F2_mul_pow (hz : ‖z‖ ≤ 1) (k : ℕ) :
    Summable fun n : ℕ => coeff3F2 n * z ^ (n + k) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    summable_norm_coeff3F2)
  rw [norm_mul, norm_pow]
  calc ‖coeff3F2 n‖ * ‖z‖ ^ (n + k) ≤ ‖coeff3F2 n‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hz) (norm_nonneg _)
    _ = ‖coeff3F2 n‖ := mul_one _

private theorem hasSum_coeff3F2_of_norm_lt_one (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasSum (fun n : ℕ => coeff3F2 n * z ^ n) (hyper3F2Closed z) := by
  have h := (summable_coeff3F2_mul_pow hz.le 1).hasSum
  rw [tsum_coeff3F2_succ hz] at h
  have h2 := h.mul_left z⁻¹
  have hval : z⁻¹ * hyper3F2Antideriv z = hyper3F2Closed z := by
    rw [hyper3F2Antideriv, hyper3F2Closed]
    field_simp
  rw [hval] at h2
  refine h2.congr_fun fun n => ?_
  field_simp
  ring

/-- The closed form is continuous on the punctured closed unit disc. -/
private theorem continuousAt_hyper3F2Closed (hz : ‖z‖ ≤ 1) (hz0 : z ≠ 0) :
    ContinuousAt hyper3F2Closed z := by
  have hre : 0 ≤ (1 - z).re := by
    have h := abs_le.mp (Complex.abs_re_le_norm z)
    simp only [Complex.sub_re, Complex.one_re]
    linarith [h.2]
  have hsqrt : ContinuousAt (fun w : ℂ => Complex.sqrt (1 - w)) z :=
    (continuousAt_cpow_const_of_re_pos (Or.inl hre) (by norm_num)).comp (by fun_prop)
  have hre2 : 0 ≤ (Complex.sqrt (1 - z)).re := by
    rw [Complex.sqrt, Complex.cpow_inv_two_re]
    positivity
  have hmem : ((Complex.sqrt (1 - z) + 1) / 2) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have h : ((Complex.sqrt (1 - z) + 1) / 2).re = ((Complex.sqrt (1 - z)).re + 1) / 2 := by simp
    rw [h]
    linarith
  have hlog : ContinuousAt (fun w : ℂ => Complex.log ((Complex.sqrt (1 - w) + 1) / 2)) z :=
    ((hsqrt.add continuousAt_const).div_const 2).clog hmem
  have h9 : ContinuousAt (fun w : ℂ => 9 * w) z := continuousAt_id.const_mul 9
  have h3 : ContinuousAt (fun w : ℂ => 3 * w) z := continuousAt_id.const_mul 3
  have h9ne : (9 : ℂ) * z ≠ 0 := by simp [hz0]
  have h3ne : (3 : ℂ) * z ≠ 0 := by simp [hz0]
  unfold hyper3F2Closed
  exact (((continuousAt_const.sub (continuousAt_const.div h9 h9ne)).mul hsqrt).add
    ((continuousAt_const.mul hlog).div h3 h3ne)).add (continuousAt_const.div h9 h9ne)

private theorem hasSum_coeff3F2_of_norm_le_one (hz : ‖z‖ ≤ 1) (hz0 : z ≠ 0) :
    HasSum (fun n : ℕ => coeff3F2 n * z ^ n) (hyper3F2Closed z) := by
  rcases lt_or_eq_of_le hz with hlt | hz1
  · exact hasSum_coeff3F2_of_norm_lt_one hlt hz0
  have habs : Summable fun n : ℕ => coeff3F2 n * z ^ n := by
    simpa using summable_coeff3F2_mul_pow hz 0
  have hS : HasSum (fun n : ℕ => coeff3F2 n * z ^ n) (∑' n, coeff3F2 n * z ^ n) := habs.hasSum
  suffices h : (∑' n : ℕ, coeff3F2 n * z ^ n) = hyper3F2Closed z by rw [← h]; exact hS
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzSet (M := 2)
    (f := fun n : ℕ => coeff3F2 n * z ^ n) hS.tendsto_sum_nat
  have hpath : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 1 (Set.Iio 1))
      (nhdsWithin 1 (Complex.stolzSet 2)) :=
    Complex.nhdsWithin_lt_le_nhdsWithin_stolzSet (by norm_num)
  have h1 : Filter.Tendsto (fun t : ℝ => ∑' n : ℕ, (coeff3F2 n * z ^ n) * (t : ℂ) ^ n)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (∑' n : ℕ, coeff3F2 n * z ^ n)) := habel.comp hpath
  have h2 : (fun t : ℝ => ∑' n : ℕ, (coeff3F2 n * z ^ n) * (t : ℂ) ^ n)
      =ᶠ[nhdsWithin 1 (Set.Iio 1)] fun t : ℝ => hyper3F2Closed ((t : ℂ) * z) := by
    filter_upwards [Ioo_mem_nhdsLT (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num)] with t ht
    have hnorm : ‖(t : ℂ) * z‖ < 1 := by
      rw [norm_mul, hz1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      exact ht.2
    have hne : (t : ℂ) * z ≠ 0 := mul_ne_zero (by simp [ne_of_gt ht.1]) hz0
    rw [← (hasSum_coeff3F2_of_norm_lt_one hnorm hne).tsum_eq]
    exact tsum_congr fun n => by rw [mul_pow]; ring
  have h3 : Filter.Tendsto (fun t : ℝ => hyper3F2Closed ((t : ℂ) * z))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (hyper3F2Closed z)) := by
    have hcont : ContinuousAt hyper3F2Closed z := continuousAt_hyper3F2Closed hz hz0
    have hmap : Filter.Tendsto (fun t : ℝ => (t : ℂ) * z) (nhdsWithin 1 (Set.Iio 1)) (nhds z) := by
      have hct : ContinuousAt (fun t : ℝ => (t : ℂ) * z) 1 := by fun_prop
      simpa using hct.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    exact Filter.Tendsto.comp (g := hyper3F2Closed) (f := fun t : ℝ => (t : ℂ) * z)
      hcont.tendsto hmap
  exact tendsto_nhds_unique (h1.congr' h2) h3

/-- **The requested identity.** -/
theorem hypergeometric3F2_0 (hz : ‖z‖ ≤ 1) (hz0 : z ≠ 0) :
    regularizedHGFun {-1 / 2, 1, 1} {2, 2} z =
      (4 / 9 - 16 / (9 * z)) * Complex.sqrt (1 - z) +
        4 * Complex.log ((Complex.sqrt (1 - z) + 1) / 2) / (3 * z) +
        16 / (9 * z) := by
  have h2 : ∑' n : ℕ, regularizedHGFunCoeff {-1 / 2, 1, 1} {2, 2} n * z ^ n
      = ∑' n : ℕ, coeff3F2 n * z ^ n :=
    tsum_congr fun n => by rw [regularizedHGFunCoeff_3F2]
  rw [regularizedHGFun_eq_tsum, h2, (hasSum_coeff3F2_of_norm_le_one hz hz0).tsum_eq,
    hyper3F2Closed]

/-- The Gamma factor relating `₃F₂(·; 2, 2; ·)` and `₃F̃₂(·; 2, 2; ·)` is `Γ(2)·Γ(2) = 1`. -/
private theorem prod_map_Gamma_two_two : ((({2, 2} : Multiset ℂ)).map Gamma).prod = 1 := by
  rw [show ({2, 2} : Multiset ℂ) = (2 : ℂ) ::ₘ {2} from rfl]
  simp

/-- **The requested identity** for the non-regularized function.  Since `Γ(2) = 1`, the
right-hand side is the same as in `Complex.hypergeometric3F2_0`. -/
theorem HGFun3F2_0 (hz : ‖z‖ ≤ 1) (hz0 : z ≠ 0) :
    HGFun {-1 / 2, 1, 1} {2, 2} z =
      (4 / 9 - 16 / (9 * z)) * Complex.sqrt (1 - z) +
        4 * Complex.log ((Complex.sqrt (1 - z) + 1) / 2) / (3 * z) +
        16 / (9 * z) := by
  rw [HGFun_eq_regularizedHGFun_of_prod_eq_one prod_map_Gamma_two_two]
  exact hypergeometric3F2_0 hz hz0

/-- The hypothesis `z ≠ 0` cannot be dropped: at `z = 0` the left-hand side is `1` while the
right-hand side evaluates to `4/9` (in Lean, division by zero returns zero). -/
theorem not_hypergeometric3F2_0_at_zero :
    ¬ ∀ z : ℂ, ‖z‖ ≤ 1 → regularizedHGFun {-1 / 2, 1, 1} {2, 2} z =
      (4 / 9 - 16 / (9 * z)) * Complex.sqrt (1 - z) +
        4 * Complex.log ((Complex.sqrt (1 - z) + 1) / 2) / (3 * z) +
        16 / (9 * z) := by
  intro h
  have h0 := h 0 (by simp)
  have hL : regularizedHGFun {-1 / 2, 1, 1} {2, 2} (0 : ℂ) = 1 := by
    rw [regularizedHGFun_eq_tsum]
    have hfun : (fun n : ℕ => regularizedHGFunCoeff {-1 / 2, 1, 1} {2, 2} n * (0 : ℂ) ^ n)
        = fun n : ℕ => if n = 0 then (1 : ℂ) else 0 := by
      funext n
      cases n with
      | zero => rw [regularizedHGFunCoeff_3F2, coeff3F2]; norm_num
      | succ m => simp
    rw [hfun, tsum_ite_eq]
  rw [hL] at h0
  norm_num at h0

/-- The hypothesis `z ≠ 0` cannot be dropped for the non-regularized function either. -/
theorem not_HGFun3F2_0_at_zero :
    ¬ ∀ z : ℂ, ‖z‖ ≤ 1 → HGFun {-1 / 2, 1, 1} {2, 2} z =
      (4 / 9 - 16 / (9 * z)) * Complex.sqrt (1 - z) +
        4 * Complex.log ((Complex.sqrt (1 - z) + 1) / 2) / (3 * z) +
        16 / (9 * z) := by
  intro h
  refine not_hypergeometric3F2_0_at_zero fun z hz => ?_
  rw [← HGFun_eq_regularizedHGFun_of_prod_eq_one (a := {-1 / 2, 1, 1}) prod_map_Gamma_two_two]
  exact h z hz

end Main

end Complex

/-
The statement as originally requested,

theorem Complex.hypergeometric3F2_0 {z : ℂ} (hz : ‖z‖ <= 1) :
    regularizedHGFun {-1/2, 1, 1} {2, 2} z =
      (4/9 - 16 / (9 * z)) * Complex.sqrt (1 - z) +
      4 * Complex.log ((Complex.sqrt (1 - z) + 1) / 2) / (3 * z) +
      16 / (9 * z) := by
  sorry

is not provable exactly as written, because it also covers `z = 0`, where the left-hand side is
`1` while the right-hand side evaluates to `4/9` (Lean's convention makes the terms with `9 * z`
and `3 * z` in the denominator vanish).  This is proved in
`Complex.not_hypergeometric3F2_0_at_zero`.  The corrected statement, with the extra hypothesis
`z ≠ 0`, is `Complex.hypergeometric3F2_0` above; it covers the whole punctured closed unit disc,
which is the full region of convergence of the series apart from the removable point `z = 0`.
The same identity for the non-regularized function `Complex.HGFun` is `Complex.HGFun3F2_0`
(the two functions agree here, since `Γ(2) = 1`).
-/
