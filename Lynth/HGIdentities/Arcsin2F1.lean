import Mathlib
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Lynth.HGIdentities.Common
import Lynth.Hypergeometric
import Lynth.ComplexFuncs
import Lynth.SeriesTools

/-!
# The two arcsine identities

This file proves

* `₂F₁(1/2, 1/2; 3/2; z) = asin(√z)/√z` (`Complex.HGFun2F1_arcsin`), and
* `₂F₁(1, 1; 3/2; z) = asin(√z)/(√z √(1-z))` (`Complex.HGFun2F1_arcsin_div_sqrt`),

both on the punctured open unit disc.

The coefficients are, respectively, `(1/2)ₙ / (n! (2n+1))` and `n!/(3/2)ₙ`; writing
`Y(z) = ∑ₙ cₙ zⁿ`, the two statements amount to

* `v · Y(v²) = asin v`, proved by checking that both sides vanish at `0` and have derivative
  `(1-v²)^(-1/2)` (the binomial series);
* `√(1-v²) · v · Y(v²) = asin v`, proved the same way; here the required series identity
  `(1-z) ∑ₙ (2n+1) dₙ zⁿ - z ∑ₙ dₙ zⁿ = 1` is a telescoping consequence of the recursion
  `(2n+3) dₙ₊₁ = (2n+2) dₙ`.
-/

open scoped Nat
open Metric

namespace Complex

/-! ### `₂F₁(1/2, 1/2; 3/2; z) = asin(√z)/√z` -/

/-- The coefficients `(1/2)ₙ / (n! (2n+1))` of `₂F₁(1/2, 1/2; 3/2; ·)`. -/
private noncomputable def arcsinCoeff (n : ℕ) : ℂ :=
  (ascPochhammer ℂ n).eval (1 / 2) / ((n ! : ℂ) * (2 * (n : ℂ) + 1))

private theorem HGFunCoeff_arcsin (n : ℕ) : HGFunCoeff {1 / 2, 1 / 2} {3 / 2} n = arcsinCoeff n := by
  rw [HGFunCoeff_eq_ascPochhammer _ three_half_not_nonpos_int n, arcsinCoeff,
    show ({1 / 2, 1 / 2} : Multiset ℂ) = (1 / 2 : ℂ) ::ₘ {1 / 2} from rfl]
  simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, ascPochhammer_three_half]
  have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hhalf := ascPochhammer_half_ne_zero n
  have h2n := two_mul_add_one_ne_zero n
  field_simp

private theorem seriesOnDisc_arcsinCoeff : SeriesOnDisc arcsinCoeff := by
  refine seriesOnDisc_of_bdd (B := 1) fun n => ?_
  have h2n := two_mul_add_one_ne_zero n
  have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hsplit : arcsinCoeff n
      = ((ascPochhammer ℂ n).eval (1 / 2) / (n ! : ℂ)) * (1 / (2 * (n : ℂ) + 1)) := by
    rw [arcsinCoeff]
    field_simp
  rw [hsplit, norm_mul]
  have h1 := norm_ascPochhammer_half_div_factorial_le n
  have h2 : ‖1 / (2 * (n : ℂ) + 1)‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (norm_pos_iff.mpr h2n),
      show (2 * (n : ℂ) + 1) = (((2 * (n : ℝ) + 1 : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  calc ‖(ascPochhammer ℂ n).eval (1 / 2) / (n ! : ℂ)‖ * ‖1 / (2 * (n : ℂ) + 1)‖ ≤ 1 * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := by ring

/-- The derivative combination of the coefficient series is the binomial series for
`(1-z)^(-1/2)`. -/
private theorem tsum_arcsin_deriv {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' n : ℕ, arcsinCoeff n * z ^ n)
      + 2 * z * ∑' n : ℕ, ((n : ℂ) + 1) * arcsinCoeff (n + 1) * z ^ n
      = (1 - z) ^ (-(1 / 2) : ℂ) := by
  have h1 := seriesOnDisc_arcsinCoeff.hasSum_deriv_combo hz
  have h2 : HasSum (fun n : ℕ => (2 * (n : ℂ) + 1) * arcsinCoeff n * z ^ n)
      ((1 - z) ^ (-(1 / 2) : ℂ)) := by
    refine (hasSum_regularized1F0 (a := 1 / 2) hz).congr_fun fun n => ?_
    have h2n := two_mul_add_one_ne_zero n
    have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    rw [arcsinCoeff]
    field_simp
  exact h1.unique h2

/-- `(1 - z)^(-1/2) = 1/√(1-z)`. -/
private theorem cpow_neg_half (z : ℂ) : (1 - z) ^ (-(1 / 2) : ℂ) = 1 / Complex.sqrt (1 - z) := by
  rw [Complex.cpow_neg, one_div, Complex.sqrt]
  norm_num

/-- The key series identity: `v ∑ₙ cₙ (v²)ⁿ = asin v` on the unit disc. -/
private theorem tsum_arcsinCoeff_eq {v : ℂ} (hv : ‖v‖ < 1) :
    v * ∑' n : ℕ, arcsinCoeff n * (v ^ 2) ^ n = arcsin v := by
  refine eq_of_hasDerivAt_ball (F := fun w : ℂ => w * ∑' n : ℕ, arcsinCoeff n * (w ^ 2) ^ n)
    (G := arcsin) (D := fun w => 1 / Complex.sqrt (1 - w ^ 2)) one_pos ?_ ?_ ?_
    (mem_ball_zero_iff.mpr hv)
  · intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hw2 : ‖w ^ 2‖ < 1 := norm_sq_lt_one hw1
    have h := seriesOnDisc_arcsinCoeff.hasDerivAt_odd_series hw1
    rw [tsum_arcsin_deriv hw2, cpow_neg_half] at h
    exact h
  · intro w hw
    exact hasDerivAt_arcsin (mem_ball_zero_iff.mp hw)
  · simp

/-- **The identity** `₂F₁(1/2, 1/2; 3/2; z) = asin(√z)/√z`, on the punctured unit disc. -/
theorem HGFun2F1_arcsin {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HGFun {1 / 2, 1 / 2} {3 / 2} z = arcsin (Complex.sqrt z) / Complex.sqrt z := by
  have hw : ‖Complex.sqrt z‖ < 1 := norm_sqrt_lt_one hz
  have hw0 : Complex.sqrt z ≠ 0 := sqrt_ne_zero_of_ne_zero hz0
  have hsq : Complex.sqrt z ^ 2 = z := sqrt_sq_eq z
  have key := tsum_arcsinCoeff_eq hw
  rw [hsq] at key
  rw [HGFun_eq_tsum,
    show (∑' n : ℕ, HGFunCoeff {1 / 2, 1 / 2} {3 / 2} n * z ^ n)
      = ∑' n : ℕ, arcsinCoeff n * z ^ n from tsum_congr fun n => by rw [HGFunCoeff_arcsin],
    ← key]
  field_simp

/-- The regularized form of the identity, with the extra factor `1/Γ(3/2)`. -/
theorem regularized2F1_arcsin {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    regularizedHGFun {1 / 2, 1 / 2} {3 / 2} z =
      arcsin (Complex.sqrt z) / Complex.sqrt z / Gamma (3 / 2) := by
  have hGne : ((({3 / 2} : Multiset ℂ)).map Gamma).prod ≠ 0 :=
    prod_map_Gamma_ne_zero three_half_not_nonpos_int
  rw [regularizedHGFun_eq_HGFun_div hGne, HGFun2F1_arcsin hz hz0]
  simp

/-- The hypothesis `z ≠ 0` is necessary: at `z = 0` the left-hand side is `1` while the
right-hand side is `0/0 = 0`. -/
theorem not_HGFun2F1_arcsin_at_zero :
    ¬ ∀ z : ℂ, HGFun {1 / 2, 1 / 2} {3 / 2} z = arcsin (Complex.sqrt z) / Complex.sqrt z := by
  intro h
  have h0 := h 0
  rw [HGFun_eq_tsum] at h0
  have hzero : (∑' n : ℕ, HGFunCoeff {1 / 2, 1 / 2} {3 / 2} n * (0 : ℂ) ^ n) = 1 := by
    rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn]), HGFunCoeff_arcsin]
    simp [arcsinCoeff]
  rw [hzero] at h0
  simp [Complex.sqrt] at h0

/-! ### `₂F₁(1, 1; 3/2; z) = asin(√z)/(√z √(1-z))` -/

/-- The coefficients `n!/(3/2)ₙ` of `₂F₁(1, 1; 3/2; ·)`. -/
private noncomputable def arcsinDivCoeff (n : ℕ) : ℂ := (n ! : ℂ) / (ascPochhammer ℂ n).eval (3 / 2)

private theorem HGFunCoeff_arcsin_div (n : ℕ) : HGFunCoeff {1, 1} {3 / 2} n = arcsinDivCoeff n := by
  rw [HGFunCoeff_eq_ascPochhammer _ three_half_not_nonpos_int n, arcsinDivCoeff,
    show ({1, 1} : Multiset ℂ) = (1 : ℂ) ::ₘ {1} from rfl]
  simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, ascPochhammer_eval_one]
  have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h32 := ascPochhammer_three_half_ne_zero n
  field_simp

private theorem two_mul_add_three_ne_zero (n : ℕ) : (2 * (n : ℂ) + 3) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.natCast_re, Complex.natCast_im, Complex.zero_re] at hre
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  norm_num at hre
  linarith

/-- The recursion `(2n+3) dₙ₊₁ = (2n+2) dₙ`. -/
private theorem arcsinDivCoeff_succ (n : ℕ) :
    (2 * (n : ℂ) + 3) * arcsinDivCoeff (n + 1) = (2 * (n : ℂ) + 2) * arcsinDivCoeff n := by
  have h3 := two_mul_add_three_ne_zero n
  have h3' : (3 + (n : ℂ) * 2) ≠ 0 := by intro h; exact h3 (by linear_combination h)
  have h32 := ascPochhammer_three_half_ne_zero n
  have h32' := ascPochhammer_three_half_ne_zero (n + 1)
  rw [arcsinDivCoeff, arcsinDivCoeff, ascPochhammer_succ_right]
  simp only [Nat.factorial_succ, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [ascPochhammer_succ_right] at h32'
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_natCast] at h32'
  field_simp
  linear_combination (n ! : ℂ) * mul_inv_cancel₀ h3'

private theorem norm_arcsinDivCoeff_le (n : ℕ) : ‖arcsinDivCoeff n‖ ≤ 1 := by
  induction n with
  | zero => simp [arcsinDivCoeff]
  | succ n ih =>
      have h3 := two_mul_add_three_ne_zero n
      have hstep : arcsinDivCoeff (n + 1)
          = arcsinDivCoeff n * ((2 * (n : ℂ) + 2) / (2 * (n : ℂ) + 3)) := by
        field_simp
        linear_combination arcsinDivCoeff_succ n
      rw [hstep, norm_mul]
      have h2 : ‖(2 * (n : ℂ) + 2) / (2 * (n : ℂ) + 3)‖ ≤ 1 := by
        rw [show (2 * (n : ℂ) + 2) = (((2 * (n : ℝ) + 2 : ℝ)) : ℂ) by push_cast; ring,
          show (2 * (n : ℂ) + 3) = (((2 * (n : ℝ) + 3 : ℝ)) : ℂ) by push_cast; ring,
          ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_div,
          div_le_one (by positivity), abs_of_pos (by positivity), abs_of_pos (by positivity)]
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      calc ‖arcsinDivCoeff n‖ * ‖(2 * (n : ℂ) + 2) / (2 * (n : ℂ) + 3)‖ ≤ 1 * 1 :=
            mul_le_mul ih h2 (norm_nonneg _) zero_le_one
        _ = 1 := by ring

private theorem seriesOnDisc_arcsinDivCoeff : SeriesOnDisc arcsinDivCoeff :=
  seriesOnDisc_of_bdd norm_arcsinDivCoeff_le

/-- The telescoping identity `(1-z) ∑ₙ (2n+1) dₙ zⁿ - z ∑ₙ dₙ zⁿ = 1`. -/
private theorem tsum_arcsin_div_deriv {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z) * ((∑' n : ℕ, arcsinDivCoeff n * z ^ n)
        + 2 * z * ∑' n : ℕ, ((n : ℂ) + 1) * arcsinDivCoeff (n + 1) * z ^ n)
      - z * ∑' n : ℕ, arcsinDivCoeff n * z ^ n = 1 := by
  set A : ℂ := ∑' n : ℕ, arcsinDivCoeff n * z ^ n with hA
  set S : ℂ := A + 2 * z * ∑' n : ℕ, ((n : ℂ) + 1) * arcsinDivCoeff (n + 1) * z ^ n with hSdef
  have hA' : HasSum (fun n : ℕ => arcsinDivCoeff n * z ^ n) A := seriesOnDisc_arcsinDivCoeff.hasSum hz
  have hS : HasSum (fun n : ℕ => (2 * (n : ℂ) + 1) * arcsinDivCoeff n * z ^ n) S :=
    seriesOnDisc_arcsinDivCoeff.hasSum_deriv_combo hz
  -- the shifted series
  have hshift : HasSum
      (fun n : ℕ => (2 * ((n + 1 : ℕ) : ℂ) + 1) * arcsinDivCoeff (n + 1) * z ^ (n + 1)) (S - 1) := by
    rw [hasSum_nat_add_iff (f := fun n : ℕ => (2 * (n : ℂ) + 1) * arcsinDivCoeff n * z ^ n) 1]
    simpa [arcsinDivCoeff] using hS
  -- `z (S + A)` is the shifted series
  have hzSA : HasSum (fun n : ℕ => (2 * ((n : ℂ) + 1) + 1) * arcsinDivCoeff (n + 1) * z ^ (n + 1))
      (z * (S + A)) := by
    refine ((hS.add hA').mul_left z).congr_fun fun n => ?_
    have hrec := arcsinDivCoeff_succ n
    linear_combination (z ^ (n + 1)) * hrec
  have hzSA' : z * (S + A) = S - 1 := by
    refine hzSA.unique ?_
    refine hshift.congr_fun fun n => ?_
    push_cast
    ring
  linear_combination -hzSA'

/-- The key series identity: `√(1-v²) · v ∑ₙ dₙ (v²)ⁿ = asin v` on the unit disc. -/
private theorem tsum_arcsinDivCoeff_eq {v : ℂ} (hv : ‖v‖ < 1) :
    Complex.sqrt (1 - v ^ 2) * (v * ∑' n : ℕ, arcsinDivCoeff n * (v ^ 2) ^ n) = arcsin v := by
  refine eq_of_hasDerivAt_ball
    (F := fun w : ℂ => Complex.sqrt (1 - w ^ 2) * (w * ∑' n : ℕ, arcsinDivCoeff n * (w ^ 2) ^ n))
    (G := arcsin) (D := fun w => 1 / Complex.sqrt (1 - w ^ 2)) one_pos ?_ ?_ ?_
    (mem_ball_zero_iff.mpr hv)
  · intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hw2 : ‖w ^ 2‖ < 1 := norm_sq_lt_one hw1
    have hs : Complex.sqrt (1 - w ^ 2) ≠ 0 := sqrt_one_sub_sq_ne_zero hw1
    have hsq : Complex.sqrt (1 - w ^ 2) ^ 2 = 1 - w ^ 2 := sq_sqrt_one_sub_sq w
    have h1 := hasDerivAt_sqrt_one_sub_sq hw1
    have h2 := seriesOnDisc_arcsinDivCoeff.hasDerivAt_odd_series hw1
    have h := h1.mul h2
    refine h.congr_deriv ?_
    -- reduce to the telescoping identity
    have hkey := tsum_arcsin_div_deriv hw2
    set s : ℂ := Complex.sqrt (1 - w ^ 2) with hsdef
    set A : ℂ := ∑' n : ℕ, arcsinDivCoeff n * (w ^ 2) ^ n with hA
    set B : ℂ := ∑' n : ℕ, ((n : ℂ) + 1) * arcsinDivCoeff (n + 1) * (w ^ 2) ^ n with hB
    rw [eq_div_iff hs]
    have hexpand : (-(w / s) * (w * A) + s * (A + 2 * w ^ 2 * B)) * s
        = -w ^ 2 * A + s ^ 2 * (A + 2 * w ^ 2 * B) := by
      field_simp
    rw [hexpand]
    linear_combination hkey + (A + 2 * w ^ 2 * B) * hsq
  · intro w hw
    exact hasDerivAt_arcsin (mem_ball_zero_iff.mp hw)
  · simp

/-- **The identity** `₂F₁(1, 1; 3/2; z) = asin(√z)/(√z √(1-z))`, on the punctured unit disc. -/
theorem HGFun2F1_arcsin_div_sqrt {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HGFun {1, 1} {3 / 2} z =
      arcsin (Complex.sqrt z) / (Complex.sqrt z * Complex.sqrt (1 - z)) := by
  have hw : ‖Complex.sqrt z‖ < 1 := norm_sqrt_lt_one hz
  have hw0 : Complex.sqrt z ≠ 0 := sqrt_ne_zero_of_ne_zero hz0
  have hsq : Complex.sqrt z ^ 2 = z := sqrt_sq_eq z
  have hs : Complex.sqrt (1 - z) ≠ 0 := sqrt_ne_zero' hz
  have key := tsum_arcsinDivCoeff_eq hw
  rw [hsq] at key
  rw [HGFun_eq_tsum,
    show (∑' n : ℕ, HGFunCoeff {1, 1} {3 / 2} n * z ^ n)
      = ∑' n : ℕ, arcsinDivCoeff n * z ^ n from tsum_congr fun n => by rw [HGFunCoeff_arcsin_div],
    ← key]
  field_simp

/-- The regularized form of the identity, with the extra factor `1/Γ(3/2)`. -/
theorem regularized2F1_arcsin_div_sqrt {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    regularizedHGFun {1, 1} {3 / 2} z =
      arcsin (Complex.sqrt z) / (Complex.sqrt z * Complex.sqrt (1 - z)) / Gamma (3 / 2) := by
  have hGne : ((({3 / 2} : Multiset ℂ)).map Gamma).prod ≠ 0 :=
    prod_map_Gamma_ne_zero three_half_not_nonpos_int
  rw [regularizedHGFun_eq_HGFun_div hGne, HGFun2F1_arcsin_div_sqrt hz hz0]
  simp

/-- The hypothesis `z ≠ 0` is necessary: at `z = 0` the left-hand side is `1` while the
right-hand side is `0/0 = 0`. -/
theorem not_HGFun2F1_arcsin_div_sqrt_at_zero :
    ¬ ∀ z : ℂ, HGFun {1, 1} {3 / 2} z =
      arcsin (Complex.sqrt z) / (Complex.sqrt z * Complex.sqrt (1 - z)) := by
  intro h
  have h0 := h 0
  rw [HGFun_eq_tsum] at h0
  have hzero : (∑' n : ℕ, HGFunCoeff {1, 1} {3 / 2} n * (0 : ℂ) ^ n) = 1 := by
    rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn]), HGFunCoeff_arcsin_div]
    simp [arcsinDivCoeff]
  rw [hzero] at h0
  simp [Complex.sqrt] at h0

end Complex
