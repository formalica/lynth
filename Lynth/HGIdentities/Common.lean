import Mathlib
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Common auxiliary results

This file collects the lemmas that are used in more than one of the hypergeometric identity
files of this project:

* elementary facts about `1 - z` and the principal square root `√(1 - z)` on the unit disc
  (`Complex.re_one_sub_pos`, `Complex.sqrt_sq_eq`, `Complex.norm_sqrt_lt_one`,
  `Complex.sqrt_ne_zero_of_ne_zero`, `Complex.re_sqrt_pos`, `Complex.sqrt_ne_zero'`,
  `Complex.sqrt_add_one_ne_zero`, `Complex.one_sub_ne_zero'`,
  `Complex.hasDerivAt_sqrt_one_sub`);
* the binomial series `∑ₙ ((a)ₙ / n!) zⁿ = (1 - z)^(-a)` (`Complex.hasSum_regularized1F0`)
  together with the identification of its coefficients with `Ring.choose`
  (`Complex.ringChoose_add_sub_one`);
* elementary facts about the Pochhammer symbols at `1/2` and `3/2` and about `2n+1`
  (`Complex.ascPochhammer_half_ne_zero`, `Complex.norm_ascPochhammer_half_div_factorial_le`,
  `Complex.two_mul_add_one_ne_zero`, `Complex.ascPochhammer_three_half`,
  `Complex.ascPochhammer_three_half_ne_zero`, `Complex.three_half_not_nonpos_int`);
* the duplication formula for factorials and the values of `Γ` at half-integers
  (`Complex.factorial_two_mul_cast`, `Complex.Gamma_half_add_nat`,
  `Complex.Gamma_one_half_ne_zero`);
* the description of `Complex.regularizedHGFun` as an ordinary power series
  (`Complex.regularizedHGFun_eq_tsum`).
-/

open scoped Nat

namespace Complex

section Disc

variable {z : ℂ}

theorem re_one_sub_pos (hz : ‖z‖ < 1) : 0 < (1 - z).re := by
  have h := abs_le.mp (Complex.abs_re_le_norm z)
  simp only [Complex.sub_re, Complex.one_re]
  linarith [h.1, h.2]

theorem sqrt_sq_eq (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  simp [Complex.sqrt]

/-- `‖√z‖ < 1` when `‖z‖ < 1`. -/
theorem norm_sqrt_lt_one (hz : ‖z‖ < 1) : ‖Complex.sqrt z‖ < 1 := by
  nlinarith [norm_nonneg (Complex.sqrt z),
    show ‖Complex.sqrt z‖ ^ 2 = ‖z‖ by rw [← norm_pow, sqrt_sq_eq]]

/-- `√z ≠ 0` when `z ≠ 0`. -/
theorem sqrt_ne_zero_of_ne_zero (hz : z ≠ 0) : Complex.sqrt z ≠ 0 := by
  intro h
  exact hz (by rw [← sqrt_sq_eq z, h]; ring)

theorem re_sqrt_pos (hz : ‖z‖ < 1) : 0 < (Complex.sqrt (1 - z)).re := by
  have h : 0 < (1 - z).re := re_one_sub_pos hz
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  refine Real.sqrt_pos.mpr ?_
  have h2 := abs_le.mp (Complex.abs_re_le_norm (1 - z))
  linarith [h2.1]

theorem sqrt_ne_zero' (hz : ‖z‖ < 1) : Complex.sqrt (1 - z) ≠ 0 := by
  intro h
  have := re_sqrt_pos hz
  rw [h] at this
  simp at this

theorem sqrt_add_one_ne_zero (hz : ‖z‖ < 1) : Complex.sqrt (1 - z) + 1 ≠ 0 := by
  intro h
  have h1 := re_sqrt_pos hz
  have h2 : (Complex.sqrt (1 - z) + 1).re = 0 := by rw [h]; simp
  simp only [Complex.add_re, Complex.one_re] at h2
  linarith

theorem one_sub_ne_zero' (hz : ‖z‖ < 1) : (1 : ℂ) - z ≠ 0 := by
  intro h
  have := re_one_sub_pos hz
  rw [h] at this
  simp at this

/-- The derivative of `z ↦ √(1-z)` on the unit disc. -/
theorem hasDerivAt_sqrt_one_sub (hz : ‖z‖ < 1) :
    HasDerivAt (fun w => Complex.sqrt (1 - w)) (-(1 / (2 * Complex.sqrt (1 - z)))) z := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub 1
  have hmem : (1 - z) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (re_one_sub_pos hz))
  have key := h1.cpow_const hmem (c := 2⁻¹)
  simp only [Complex.sqrt]
  convert key using 1
  have hne : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero' hz
  have h2 : Complex.sqrt (1 - z) ^ 2 = 1 - z := sqrt_sq_eq _
  rw [Complex.cpow_sub _ _ hne, Complex.cpow_one,
    show (1 - z) ^ (2⁻¹ : ℂ) = Complex.sqrt (1 - z) from rfl]
  set s := Complex.sqrt (1 - z) with hsdef
  clear_value s
  rw [← h2]
  field_simp

end Disc

section BinomialSeries

/-- The binomial coefficient `Ring.choose (a + n - 1) n` is `(a)ₙ / n!`. -/
theorem ringChoose_add_sub_one (a : ℂ) (n : ℕ) :
    Ring.choose (a + n - 1) n = (ascPochhammer ℂ n).eval a / (Nat.factorial n : ℂ) := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (a + (n : ℂ) - 1) n
  rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    show a + (n : ℂ) - 1 - n + 1 = a by ring, Polynomial.ascPochhammer_smeval_cast,
    Polynomial.ascPochhammer_smeval_eq_eval, nsmul_eq_mul] at h
  rw [h, mul_comm, mul_div_assoc, div_self (by exact_mod_cast Nat.factorial_ne_zero n), mul_one]

/-- The binomial series: for `‖z‖ < 1` the series `∑ₙ ((a)ₙ / n!) zⁿ` sums to `(1 - z)^(-a)`. -/
theorem hasSum_regularized1F0 {a z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => ((ascPochhammer ℂ n).eval a / (Nat.factorial n : ℂ)) * z ^ n)
      ((1 - z) ^ (-a)) := by
  have hb := (one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a).hasSum
    (y := z) (by rw [← ENNReal.ofReal_one, Metric.eball_ofReal]; simpa using hz)
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, smul_eq_mul] at hb
  rw [cpow_neg, ← one_div]
  exact hb.congr_fun fun n => by rw [ringChoose_add_sub_one]

/-- `(1/2)ₖ ≠ 0`. -/
theorem ascPochhammer_half_ne_zero (k : ℕ) : (ascPochhammer ℂ k).eval (1 / 2) ≠ 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [ascPochhammer_succ_eval]
      refine mul_ne_zero ih ?_
      intro h
      have h2 := congrArg Complex.re h
      simp at h2
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith

theorem two_mul_add_one_ne_zero (n : ℕ) : (2 * (n : ℂ) + 1) ≠ 0 := by
  intro h
  have hre : (2 * (n : ℂ) + 1).re = 0 := by rw [h]; simp
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.natCast_re, Complex.natCast_im, Complex.one_re] at hre
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- `(3/2)ₙ = (2n+1) (1/2)ₙ`. -/
theorem ascPochhammer_three_half (n : ℕ) :
    (ascPochhammer ℂ n).eval (3 / 2) = (2 * (n : ℂ) + 1) * (ascPochhammer ℂ n).eval (1 / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_natCast, ih]
      push_cast
      ring

theorem three_half_not_nonpos_int : ∀ j ∈ ({3 / 2} : Multiset ℂ), ∀ m : ℕ, j ≠ -(m : ℂ) := by
  intro j hj m
  rw [Multiset.mem_singleton] at hj
  subst hj
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.div_re, Complex.neg_re, Complex.natCast_re] at hre
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  norm_num at hre
  linarith

/-- `(3/2)ₙ ≠ 0`. -/
theorem ascPochhammer_three_half_ne_zero (n : ℕ) : (ascPochhammer ℂ n).eval (3 / 2) ≠ 0 := by
  rw [ascPochhammer_three_half]
  exact mul_ne_zero (two_mul_add_one_ne_zero n) (ascPochhammer_half_ne_zero n)

/-- `‖(1/2)ₙ / n!‖ ≤ 1`. -/
theorem norm_ascPochhammer_half_div_factorial_le (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval (1 / 2) / (n ! : ℂ)‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hn1 : ((n : ℂ) + 1) ≠ 0 := by
        have h : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
        simpa using h
      have hstep : (ascPochhammer ℂ (n + 1)).eval (1 / 2) / ((n + 1)! : ℂ)
          = ((ascPochhammer ℂ n).eval (1 / 2) / (n ! : ℂ)) * ((1 / 2 + (n : ℂ)) / ((n : ℂ) + 1)) := by
        rw [ascPochhammer_succ_right]
        simp only [Nat.factorial_succ, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        field_simp
      rw [hstep, norm_mul]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h2 : ‖(1 / 2 + (n : ℂ)) / ((n : ℂ) + 1)‖ ≤ 1 := by
        rw [show (1 / 2 + (n : ℂ)) = ((1 / 2 + n : ℝ) : ℂ) by push_cast; ring,
          show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_div,
          div_le_one (by positivity), abs_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity), abs_le]
        constructor <;> [linarith; linarith]
      calc ‖(ascPochhammer ℂ n).eval (1 / 2) / (n ! : ℂ)‖ * ‖(1 / 2 + (n : ℂ)) / ((n : ℂ) + 1)‖
          ≤ 1 * 1 := by
            exact mul_le_mul ih h2 (norm_nonneg _) zero_le_one
        _ = 1 := by ring

end BinomialSeries

/-- The duplication formula for factorials: `(2k)! = 4^k k! (1/2)_k`. -/
theorem factorial_two_mul_cast (k : ℕ) :
    (((2 * k)! : ℕ) : ℂ) = 4 ^ k * (k ! : ℂ) * (ascPochhammer ℂ k).eval (1 / 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h2 : 2 * (k + 1) = (2 * k) + 1 + 1 := by ring
      rw [h2, Nat.factorial_succ, Nat.factorial_succ, ascPochhammer_succ_eval,
        Nat.factorial_succ]
      push_cast
      rw [ih]
      ring

/-- `Γ(1/2 + k) = (1/2)_k Γ(1/2)`. -/
theorem Gamma_half_add_nat (k : ℕ) :
    Gamma (1 / 2 + k) = (ascPochhammer ℂ k).eval (1 / 2) * Gamma (1 / 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hne : ((1 : ℂ) / 2 + k) ≠ 0 := by
        intro h
        have h2 := congrArg Complex.re h
        simp at h2
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have : (1 : ℂ) / 2 + (k + 1 : ℕ) = (1 / 2 + k) + 1 := by push_cast; ring
      rw [this, Complex.Gamma_add_one _ hne, ih, ascPochhammer_succ_eval]
      ring

/-- `Γ(1/2) ≠ 0`. -/
theorem Gamma_one_half_ne_zero : Gamma ((1 : ℂ) / 2) ≠ 0 := by
  refine Gamma_ne_zero fun m h => ?_
  have hre := congrArg Complex.re h
  simp only [Complex.div_re, Complex.one_re, Complex.one_im, Complex.neg_re,
    Complex.natCast_re] at hre
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  norm_num at hre
  linarith

/-- The regularized hypergeometric function is the sum of its power series. -/
theorem regularizedHGFun_eq_tsum (as bs : Multiset ℂ) (w : ℂ) :
    regularizedHGFun as bs w = ∑' n : ℕ, regularizedHGFunCoeff as bs n * w ^ n := by
  rw [regularizedHGFun, FormalMultilinearSeries.sum]
  exact tsum_congr fun n => by
    rw [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

end Complex
