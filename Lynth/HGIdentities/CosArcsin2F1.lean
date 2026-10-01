import Mathlib
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Lynth.HGIdentities.Common
import Lynth.Hypergeometric
import Lynth.ComplexFuncs
import Lynth.SeriesTools

/-!
# `₂F₁(a, -a; 1/2; z) = cos(2a asin √z)`

The coefficients of the series are `cₙ = (a)ₙ (-a)ₙ / (n! (1/2)ₙ)`, and the identity to be proved
is `∑ₙ cₙ (v²)ⁿ = cos(2a asin v)` for `‖v‖ < 1`.

Both sides solve the second-order linear differential equation
`(1 - v²) y'' - v y' + 4a² y = 0` with `y(0) = 1`, `y'(0) = 0`; for the series this is exactly the
two-term recursion `2(n+1)(2n+1) cₙ₊₁ = 4(n² - a²) cₙ`.  Uniqueness is obtained without any
appeal to general ODE theory: with `u v = exp(2ia asin v)`, a nonvanishing solution of the same
equation, the Wronskian `W = φ' u - φ u'` of the difference `φ` of the two solutions satisfies
`(1-v²) W' = v W`, so `W √(1-v²)` has vanishing derivative and hence is `0`; then `(φ/u)' = 0`
gives `φ ≡ 0`.

## Main results

* `Complex.HGFun2F1_cos_arcsin` : `₂F₁(a, -a; 1/2; z) = cos(2a asin(√z))` for `‖z‖ < 1`;
* `Complex.regularized2F1_cos_arcsin` : the regularized version, with the factor `1/Γ(1/2)`.
-/

open scoped Nat
open Metric

namespace Complex

variable {a : ℂ}

/-! ### The coefficients -/

/-- The coefficients `(a)ₙ (-a)ₙ / (n! (1/2)ₙ)` of `₂F₁(a, -a; 1/2; ·)`. -/
private noncomputable def cosArcsinCoeff (a : ℂ) (n : ℕ) : ℂ :=
  (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval (-a) /
    ((n ! : ℂ) * (ascPochhammer ℂ n).eval (1 / 2))

private theorem half_not_nonpos_int : ∀ j ∈ ({1 / 2} : Multiset ℂ), ∀ m : ℕ, j ≠ -(m : ℂ) := by
  intro j hj m
  rw [Multiset.mem_singleton] at hj
  subst hj
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.div_re, Complex.neg_re, Complex.natCast_re] at hre
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  norm_num at hre
  linarith

private theorem HGFunCoeff_cos_arcsin (a : ℂ) (n : ℕ) :
    HGFunCoeff {a, -a} {1 / 2} n = cosArcsinCoeff a n := by
  rw [HGFunCoeff_eq_ascPochhammer _ half_not_nonpos_int n, cosArcsinCoeff,
    show ({a, -a} : Multiset ℂ) = a ::ₘ {-a} from rfl]
  simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton]

@[simp] theorem cosArcsinCoeff_zero (a : ℂ) : cosArcsinCoeff a 0 = 1 := by
  simp [cosArcsinCoeff]

private theorem cosArcsinCoeff_one (a : ℂ) : cosArcsinCoeff a 1 = -2 * a ^ 2 := by
  simp [cosArcsinCoeff, ascPochhammer_one]
  ring

private theorem one_add_two_mul_ne_zero (n : ℕ) : (1 + (n : ℂ) * 2) ≠ 0 :=
  fun h => two_mul_add_one_ne_zero n (by linear_combination h)

private theorem natCast_add_one_ne_zero (n : ℕ) : ((n : ℂ) + 1) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at hre
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

private theorem natCast_add_half_ne_zero (n : ℕ) : ((n : ℂ) + 1 / 2) ≠ 0 :=
  fun h => one_add_two_mul_ne_zero n (by linear_combination 2 * h)

/-- The two-term recursion `2(n+1)(2n+1) cₙ₊₁ = 4(n² - a²) cₙ`. -/
private theorem cosArcsinCoeff_succ (a : ℂ) (n : ℕ) :
    2 * ((n : ℂ) + 1) * (2 * (n : ℂ) + 1) * cosArcsinCoeff a (n + 1)
      = (4 * (n : ℂ) ^ 2 - 4 * a ^ 2) * cosArcsinCoeff a n := by
  have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hH := ascPochhammer_half_ne_zero n
  have h1 := one_add_two_mul_ne_zero n
  have hhalf : ((1 : ℂ) / 2 + (n : ℂ)) ≠ 0 := fun h => h1 (by linear_combination 2 * h)
  rw [cosArcsinCoeff, cosArcsinCoeff, ascPochhammer_succ_right]
  simp only [Nat.factorial_succ, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  linear_combination (4 * (Polynomial.eval a (ascPochhammer ℂ n)) *
    (Polynomial.eval (-a) (ascPochhammer ℂ n)) * ((n : ℂ) ^ 2 - a ^ 2)) * mul_inv_cancel₀ h1

/-- The recursion in multiplicative form. -/
private theorem cosArcsinCoeff_step (a : ℂ) (n : ℕ) :
    cosArcsinCoeff a (n + 1)
      = cosArcsinCoeff a n * (((n : ℂ) ^ 2 - a ^ 2) / (((n : ℂ) + 1) * ((n : ℂ) + 1 / 2))) := by
  have h3 := one_add_two_mul_ne_zero n
  have h1 := natCast_add_one_ne_zero n
  have h2 := natCast_add_half_ne_zero n
  have hne : (2 * ((n : ℂ) + 1) * (2 * (n : ℂ) + 1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero h1) (two_mul_add_one_ne_zero n)
  refine mul_left_cancel₀ hne ?_
  rw [cosArcsinCoeff_succ a n]
  field_simp
  linear_combination (-4 * cosArcsinCoeff a n * ((n : ℂ) ^ 2 - a ^ 2)) * mul_inv_cancel₀ h3

/-- The coefficients define a series converging on the open unit disc. -/
private theorem seriesOnDisc_cosArcsinCoeff (a : ℂ) : SeriesOnDisc (cosArcsinCoeff a) := by
  refine seriesOnDisc_of_ratio_bound (K := ‖a‖ ^ 2) 1 fun n hn => ?_
  have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [cosArcsinCoeff_step, norm_mul, norm_div, norm_mul]
  have hnorm1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hnorm2 : ‖((n : ℂ) + 1 / 2)‖ = (n : ℝ) + 1 / 2 := by
    rw [show ((n : ℂ) + 1 / 2) = (((n : ℝ) + 1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hnum : ‖(n : ℂ) ^ 2 - a ^ 2‖ ≤ (n : ℝ) ^ 2 + ‖a‖ ^ 2 := by
    calc ‖(n : ℂ) ^ 2 - a ^ 2‖ ≤ ‖(n : ℂ) ^ 2‖ + ‖a ^ 2‖ := norm_sub_le _ _
      _ = (n : ℝ) ^ 2 + ‖a‖ ^ 2 := by rw [norm_pow, norm_pow, Complex.norm_natCast]
  rw [hnorm1, hnorm2]
  have hfrac : ‖(n : ℂ) ^ 2 - a ^ 2‖ / (((n : ℝ) + 1) * ((n : ℝ) + 1 / 2))
      ≤ 1 + ‖a‖ ^ 2 / ((n : ℝ) + 1) := by
    rw [div_le_iff₀ (by positivity)]
    have hexp : (1 + ‖a‖ ^ 2 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * ((n : ℝ) + 1 / 2))
        = ((n : ℝ) + 1 + ‖a‖ ^ 2) * ((n : ℝ) + 1 / 2) := by
      field_simp
    rw [hexp]
    nlinarith [norm_nonneg a, sq_nonneg ‖a‖]
  calc ‖cosArcsinCoeff a n‖ * (‖(n : ℂ) ^ 2 - a ^ 2‖ / (((n : ℝ) + 1) * ((n : ℝ) + 1 / 2)))
      ≤ ‖cosArcsinCoeff a n‖ * (1 + ‖a‖ ^ 2 / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hfrac (norm_nonneg _)
    _ = (1 + ‖a‖ ^ 2 / ((n : ℝ) + 1)) * ‖cosArcsinCoeff a n‖ := by ring

/-! ### The series and its derivatives -/

/-- The series `∑ₙ cₙ (v²)ⁿ`. -/
private noncomputable def cosSeries (a v : ℂ) : ℂ := ∑' n : ℕ, cosArcsinCoeff a n * (v ^ 2) ^ n

/-- Its first derivative. -/
private noncomputable def cosSeries' (a v : ℂ) : ℂ :=
  2 * v * ∑' n : ℕ, ((n : ℂ) + 1) * cosArcsinCoeff a (n + 1) * (v ^ 2) ^ n

/-- Its second derivative. -/
private noncomputable def cosSeries'' (a v : ℂ) : ℂ :=
  2 * ∑' n : ℕ, ((n : ℂ) + 1) * cosArcsinCoeff a (n + 1) * (v ^ 2) ^ n
    + 4 * v ^ 2 * ∑' n : ℕ, ((n : ℂ) + 1) *
        (((n : ℂ) + 1 + 1) * cosArcsinCoeff a (n + 1 + 1)) * (v ^ 2) ^ n

@[simp] theorem cosSeries_zero (a : ℂ) : cosSeries a 0 = 1 := by
  rw [cosSeries, tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

@[simp] theorem cosSeries'_zero (a : ℂ) : cosSeries' a 0 = 0 := by
  simp [cosSeries']

private theorem hasDerivAt_cosSeries {v : ℂ} (hv : ‖v‖ < 1) :
    HasDerivAt (cosSeries a) (cosSeries' a v) v :=
  (seriesOnDisc_cosArcsinCoeff a).hasDerivAt_even_series hv

private theorem hasDerivAt_cosSeries' {v : ℂ} (hv : ‖v‖ < 1) :
    HasDerivAt (cosSeries' a) (cosSeries'' a v) v := by
  have h := ((seriesOnDisc_cosArcsinCoeff a).shift.hasDerivAt_odd_series hv).const_mul 2
  have heq : (cosSeries' a) =ᶠ[nhds v]
      fun w : ℂ => 2 * (w * ∑' n : ℕ, ((n : ℂ) + 1) * cosArcsinCoeff a (n + 1) * (w ^ 2) ^ n) :=
    Filter.Eventually.of_forall fun w => by rw [cosSeries']; ring
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [cosSeries'']
  push_cast
  ring

/-- The differential equation satisfied by the series. -/
private theorem cosSeries_ode {v : ℂ} (hv : ‖v‖ < 1) :
    (1 - v ^ 2) * cosSeries'' a v - v * cosSeries' a v + 4 * a ^ 2 * cosSeries a v = 0 := by
  have hc := seriesOnDisc_cosArcsinCoeff a
  have hz : ‖v ^ 2‖ < 1 := norm_sq_lt_one hv
  rw [cosSeries'', cosSeries', cosSeries]
  set z : ℂ := v ^ 2 with hzdef
  set A : ℂ := ∑' n : ℕ, cosArcsinCoeff a n * z ^ n with hA
  set B : ℂ := ∑' n : ℕ, ((n : ℂ) + 1) * cosArcsinCoeff a (n + 1) * z ^ n with hB
  set C : ℂ := ∑' n : ℕ, ((n : ℂ) + 1) * (((n : ℂ) + 1 + 1) * cosArcsinCoeff a (n + 1 + 1)) * z ^ n
    with hC
  have hA' : HasSum (fun n : ℕ => cosArcsinCoeff a n * z ^ n) A := hc.hasSum hz
  have hB' : HasSum (fun n : ℕ => ((n : ℂ) + 1) * cosArcsinCoeff a (n + 1) * z ^ n) B :=
    hc.shift.hasSum hz
  have hcombo : HasSum
      (fun n : ℕ => (2 * (n : ℂ) + 1) * (((n : ℂ) + 1) * cosArcsinCoeff a (n + 1)) * z ^ n)
      (B + 2 * z * C) := hc.hasSum_deriv_combo_shift hz
  set F : ℂ := 2 * (B + 2 * z * C) + 4 * a ^ 2 * A with hF
  have hFsum : HasSum (fun n : ℕ =>
      (2 * ((2 * (n : ℂ) + 1) * (((n : ℂ) + 1) * cosArcsinCoeff a (n + 1)))
        + 4 * a ^ 2 * cosArcsinCoeff a n) * z ^ n) F := by
    refine ((hcombo.mul_left 2).add (hA'.mul_left (4 * a ^ 2))).congr_fun fun n => ?_
    ring
  have hf0 : 2 * cosArcsinCoeff a 1 + 4 * a ^ 2 = 0 := by
    rw [cosArcsinCoeff_one]; ring
  have hshift : HasSum (fun n : ℕ =>
      (2 * ((2 * ((n + 1 : ℕ) : ℂ) + 1) * ((((n + 1 : ℕ)) : ℂ) + 1) * cosArcsinCoeff a (n + 1 + 1))
        + 4 * a ^ 2 * cosArcsinCoeff a (n + 1)) * z ^ (n + 1)) F := by
    have hrw := (hasSum_nat_add_iff (g := F) (f := fun n : ℕ =>
      (2 * ((2 * (n : ℂ) + 1) * (((n : ℂ) + 1) * cosArcsinCoeff a (n + 1)))
        + 4 * a ^ 2 * cosArcsinCoeff a n) * z ^ n) 1)
    refine (hrw.mpr ?_).congr_fun fun n => by ring
    simpa [hf0] using hFsum
  have hG : HasSum (fun n : ℕ =>
      (2 * ((2 * (n : ℂ) + 1) * (((n : ℂ) + 1) * cosArcsinCoeff a (n + 1)))
        + 2 * (((n : ℂ) + 1) * cosArcsinCoeff a (n + 1))) * z ^ (n + 1))
      (z * (2 * (B + 2 * z * C) + 2 * B)) := by
    refine (((hcombo.mul_left 2).add (hB'.mul_left 2)).mul_left z).congr_fun fun n => ?_
    ring
  have hEq : F = z * (2 * (B + 2 * z * C) + 2 * B) := by
    refine hshift.unique (hG.congr_fun fun n => ?_)
    have hrec := cosArcsinCoeff_succ a (n + 1)
    push_cast at hrec ⊢
    linear_combination (z ^ (n + 1)) * hrec
  linear_combination hEq + 2 * B * hzdef

/-! ### The closed form and the auxiliary exponential solution -/

/-- The closed form `cos (2a asin v)`. -/
private noncomputable def cosArcsinFun (a v : ℂ) : ℂ := Complex.cos (2 * a * arcsin v)

/-- Its first derivative. -/
private noncomputable def cosArcsinFun' (a v : ℂ) : ℂ :=
  -2 * a * Complex.sin (2 * a * arcsin v) / Complex.sqrt (1 - v ^ 2)

/-- Its second derivative. -/
private noncomputable def cosArcsinFun'' (a v : ℂ) : ℂ :=
  -4 * a ^ 2 * Complex.cos (2 * a * arcsin v) / (1 - v ^ 2)
    - 2 * a * v * Complex.sin (2 * a * arcsin v) / (Complex.sqrt (1 - v ^ 2) * (1 - v ^ 2))

/-- The nonvanishing solution `exp (2ia asin v)`. -/
private noncomputable def expArcsinFun (a v : ℂ) : ℂ := Complex.exp (2 * a * I * arcsin v)

/-- Its first derivative. -/
private noncomputable def expArcsinFun' (a v : ℂ) : ℂ :=
  2 * a * I * expArcsinFun a v / Complex.sqrt (1 - v ^ 2)

/-- Its second derivative. -/
private noncomputable def expArcsinFun'' (a v : ℂ) : ℂ :=
  -4 * a ^ 2 * expArcsinFun a v / (1 - v ^ 2)
    + 2 * a * I * v * expArcsinFun a v / (Complex.sqrt (1 - v ^ 2) * (1 - v ^ 2))

private theorem expArcsinFun_ne_zero (a v : ℂ) : expArcsinFun a v ≠ 0 := Complex.exp_ne_zero _

@[simp] theorem cosArcsinFun_zero (a : ℂ) : cosArcsinFun a 0 = 1 := by simp [cosArcsinFun]

@[simp] theorem cosArcsinFun'_zero (a : ℂ) : cosArcsinFun' a 0 = 0 := by
  simp [cosArcsinFun']

private theorem hasDerivAt_cosArcsinFun {v : ℂ} (hv : ‖v‖ < 1) :
    HasDerivAt (cosArcsinFun a) (cosArcsinFun' a v) v := by
  have hs : Complex.sqrt (1 - v ^ 2) ≠ 0 := sqrt_one_sub_sq_ne_zero hv
  have h1 : HasDerivAt (fun w : ℂ => 2 * a * arcsin w) (2 * a * (1 / Complex.sqrt (1 - v ^ 2))) v :=
    (hasDerivAt_arcsin hv).const_mul (2 * a)
  refine ((Complex.hasDerivAt_cos (2 * a * arcsin v)).comp v h1).congr_deriv ?_
  rw [cosArcsinFun']
  field_simp

private theorem hasDerivAt_cosArcsinFun' {v : ℂ} (hv : ‖v‖ < 1) :
    HasDerivAt (cosArcsinFun' a) (cosArcsinFun'' a v) v := by
  have hs : Complex.sqrt (1 - v ^ 2) ≠ 0 := sqrt_one_sub_sq_ne_zero hv
  have hsq : Complex.sqrt (1 - v ^ 2) ^ 2 = 1 - v ^ 2 := sq_sqrt_one_sub_sq v
  have harg : HasDerivAt (fun w : ℂ => 2 * a * arcsin w)
      (2 * a * (1 / Complex.sqrt (1 - v ^ 2))) v := (hasDerivAt_arcsin hv).const_mul (2 * a)
  have hnum : HasDerivAt (fun w : ℂ => -2 * a * Complex.sin (2 * a * arcsin w))
      (-2 * a * (Complex.cos (2 * a * arcsin v) * (2 * a * (1 / Complex.sqrt (1 - v ^ 2))))) v :=
    ((Complex.hasDerivAt_sin (2 * a * arcsin v)).comp v harg).const_mul (-2 * a)
  refine (hnum.div (hasDerivAt_sqrt_one_sub_sq hv) hs).congr_deriv ?_
  rw [cosArcsinFun'']
  generalize hgen : Complex.sqrt (1 - v ^ 2) = s at hs hsq ⊢
  rw [← hsq]
  field_simp
  ring

private theorem hasDerivAt_expArcsinFun {v : ℂ} (hv : ‖v‖ < 1) :
    HasDerivAt (expArcsinFun a) (expArcsinFun' a v) v := by
  have hs : Complex.sqrt (1 - v ^ 2) ≠ 0 := sqrt_one_sub_sq_ne_zero hv
  have h1 : HasDerivAt (fun w : ℂ => 2 * a * I * arcsin w)
      (2 * a * I * (1 / Complex.sqrt (1 - v ^ 2))) v := (hasDerivAt_arcsin hv).const_mul (2 * a * I)
  refine h1.cexp.congr_deriv ?_
  rw [expArcsinFun', expArcsinFun]
  field_simp

private theorem hasDerivAt_expArcsinFun' {v : ℂ} (hv : ‖v‖ < 1) :
    HasDerivAt (expArcsinFun' a) (expArcsinFun'' a v) v := by
  have hs : Complex.sqrt (1 - v ^ 2) ≠ 0 := sqrt_one_sub_sq_ne_zero hv
  have hsq : Complex.sqrt (1 - v ^ 2) ^ 2 = 1 - v ^ 2 := sq_sqrt_one_sub_sq v
  have hnum : HasDerivAt (fun w : ℂ => 2 * a * I * expArcsinFun a w)
      (2 * a * I * expArcsinFun' a v) v := (hasDerivAt_expArcsinFun hv).const_mul (2 * a * I)
  refine (hnum.div (hasDerivAt_sqrt_one_sub_sq hv) hs).congr_deriv ?_
  rw [expArcsinFun'', expArcsinFun']
  generalize hgen : Complex.sqrt (1 - v ^ 2) = s at hs hsq ⊢
  rw [← hsq]
  set E := expArcsinFun a v
  field_simp
  linear_combination (4 * a ^ 2 * E * s) * Complex.I_sq

/-- The closed form satisfies the same differential equation. -/
private theorem cosArcsinFun_ode {v : ℂ} (hv : ‖v‖ < 1) :
    (1 - v ^ 2) * cosArcsinFun'' a v - v * cosArcsinFun' a v + 4 * a ^ 2 * cosArcsinFun a v = 0 := by
  have hs : Complex.sqrt (1 - v ^ 2) ≠ 0 := sqrt_one_sub_sq_ne_zero hv
  have hne : (1 : ℂ) - v ^ 2 ≠ 0 := one_sub_ne_zero' (norm_sq_lt_one hv)
  rw [cosArcsinFun'', cosArcsinFun', cosArcsinFun]
  field_simp
  ring

/-- The exponential solution satisfies the same differential equation. -/
private theorem expArcsinFun_ode {v : ℂ} (hv : ‖v‖ < 1) :
    (1 - v ^ 2) * expArcsinFun'' a v - v * expArcsinFun' a v + 4 * a ^ 2 * expArcsinFun a v = 0 := by
  have hs : Complex.sqrt (1 - v ^ 2) ≠ 0 := sqrt_one_sub_sq_ne_zero hv
  have hne : (1 : ℂ) - v ^ 2 ≠ 0 := one_sub_ne_zero' (norm_sq_lt_one hv)
  rw [expArcsinFun'', expArcsinFun']
  field_simp
  ring

/-! ### Uniqueness via the Wronskian -/

/-- The Wronskian of the difference of the two solutions with the exponential solution. -/
private noncomputable def wronsk (a v : ℂ) : ℂ :=
  (cosSeries' a v - cosArcsinFun' a v) * expArcsinFun a v
    - (cosSeries a v - cosArcsinFun a v) * expArcsinFun' a v

private noncomputable def wronsk' (a v : ℂ) : ℂ :=
  (cosSeries'' a v - cosArcsinFun'' a v) * expArcsinFun a v
    - (cosSeries a v - cosArcsinFun a v) * expArcsinFun'' a v

@[simp] theorem wronsk_zero (a : ℂ) : wronsk a 0 = 0 := by
  simp [wronsk]

private theorem hasDerivAt_wronsk {v : ℂ} (hv : ‖v‖ < 1) :
    HasDerivAt (wronsk a) (wronsk' a v) v := by
  have h1 := ((hasDerivAt_cosSeries (a := a) hv).sub (hasDerivAt_cosArcsinFun (a := a) hv)).mul
    (hasDerivAt_expArcsinFun' (a := a) hv)
  have h2 := ((hasDerivAt_cosSeries' (a := a) hv).sub (hasDerivAt_cosArcsinFun' (a := a) hv)).mul
    (hasDerivAt_expArcsinFun (a := a) hv)
  refine (h2.sub h1).congr_deriv ?_
  rw [wronsk']
  simp only [Pi.sub_apply]
  ring

/-- The Wronskian satisfies the first-order equation `(1-v²) W' = v W`. -/
private theorem wronsk_ode {v : ℂ} (hv : ‖v‖ < 1) :
    (1 - v ^ 2) * wronsk' a v = v * wronsk a v := by
  rw [wronsk, wronsk']
  linear_combination (expArcsinFun a v) * cosSeries_ode (a := a) hv
    - (expArcsinFun a v) * cosArcsinFun_ode (a := a) hv
    - (cosSeries a v - cosArcsinFun a v) * expArcsinFun_ode (a := a) hv

/-- Consequently the Wronskian vanishes identically on the disc. -/
private theorem wronsk_eq_zero {v : ℂ} (hv : ‖v‖ < 1) : wronsk a v = 0 := by
  have hs : Complex.sqrt (1 - v ^ 2) ≠ 0 := sqrt_one_sub_sq_ne_zero hv
  have key : (fun w : ℂ => wronsk a w * Complex.sqrt (1 - w ^ 2)) v = (fun _ : ℂ => (0 : ℂ)) v := by
    refine eq_of_hasDerivAt_ball (F := fun w : ℂ => wronsk a w * Complex.sqrt (1 - w ^ 2))
      (G := fun _ : ℂ => (0 : ℂ)) (D := fun _ => 0) one_pos ?_ (fun w _ => hasDerivAt_const w 0) ?_
      (mem_ball_zero_iff.mpr hv)
    · intro w hw
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
      have hsw : Complex.sqrt (1 - w ^ 2) ≠ 0 := sqrt_one_sub_sq_ne_zero hw1
      have hsqw : Complex.sqrt (1 - w ^ 2) ^ 2 = 1 - w ^ 2 := sq_sqrt_one_sub_sq w
      have hode := wronsk_ode (a := a) hw1
      refine ((hasDerivAt_wronsk (a := a) hw1).mul (hasDerivAt_sqrt_one_sub_sq hw1)).congr_deriv ?_
      generalize hgen : Complex.sqrt (1 - w ^ 2) = s at hsw hsqw ⊢
      show wronsk' a w * s + wronsk a w * -(w / s) = 0
      field_simp
      linear_combination hode + (wronsk' a w) * hsqw
    · simp
  simpa [hs] using key

/-- The key identity: the series is the closed form. -/
private theorem cosSeries_eq {v : ℂ} (hv : ‖v‖ < 1) : cosSeries a v = cosArcsinFun a v := by
  have hU : expArcsinFun a v ≠ 0 := expArcsinFun_ne_zero a v
  have key : (fun w : ℂ => (cosSeries a w - cosArcsinFun a w) / expArcsinFun a w) v
      = (fun _ : ℂ => (0 : ℂ)) v := by
    refine eq_of_hasDerivAt_ball
      (F := fun w : ℂ => (cosSeries a w - cosArcsinFun a w) / expArcsinFun a w)
      (G := fun _ : ℂ => (0 : ℂ)) (D := fun _ => 0) one_pos ?_ (fun w _ => hasDerivAt_const w 0) ?_
      (mem_ball_zero_iff.mpr hv)
    · intro w hw
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
      have hUw : expArcsinFun a w ≠ 0 := expArcsinFun_ne_zero a w
      have h := ((hasDerivAt_cosSeries (a := a) hw1).sub
        (hasDerivAt_cosArcsinFun (a := a) hw1)).div (hasDerivAt_expArcsinFun (a := a) hw1) hUw
      refine h.congr_deriv ?_
      have hW := wronsk_eq_zero (a := a) hw1
      rw [wronsk] at hW
      show ((cosSeries' a w - cosArcsinFun' a w) * expArcsinFun a w
        - (cosSeries a w - cosArcsinFun a w) * expArcsinFun' a w) / expArcsinFun a w ^ 2 = 0
      rw [hW, zero_div]
    · simp
  simp only at key
  rw [div_eq_zero_iff] at key
  rcases key with h | h
  · linear_combination h
  · exact absurd h hU

/-! ### The hypergeometric identity -/

/-- **The identity** `₂F₁(a, -a; 1/2; z) = cos(2a asin(√z))` on the unit disc. -/
theorem HGFun2F1_cos_arcsin {a z : ℂ} (hz : ‖z‖ < 1) :
    HGFun {a, -a} {1 / 2} z = Complex.cos (2 * a * arcsin (Complex.sqrt z)) := by
  have hw : ‖Complex.sqrt z‖ < 1 := norm_sqrt_lt_one hz
  have hsq : Complex.sqrt z ^ 2 = z := sqrt_sq_eq z
  have key := cosSeries_eq (a := a) hw
  rw [cosSeries, cosArcsinFun, hsq] at key
  rw [HGFun_eq_tsum,
    show (∑' n : ℕ, HGFunCoeff {a, -a} {1 / 2} n * z ^ n)
      = ∑' n : ℕ, cosArcsinCoeff a n * z ^ n from
      tsum_congr fun n => by rw [HGFunCoeff_cos_arcsin]]
  exact key

/-- The regularized form of the identity, with the extra factor `1/Γ(1/2)`. -/
theorem regularized2F1_cos_arcsin {a z : ℂ} (hz : ‖z‖ < 1) :
    regularizedHGFun {a, -a} {1 / 2} z =
      Complex.cos (2 * a * arcsin (Complex.sqrt z)) / Gamma (1 / 2) := by
  have hGne : ((({1 / 2} : Multiset ℂ)).map Gamma).prod ≠ 0 :=
    prod_map_Gamma_ne_zero half_not_nonpos_int
  rw [regularizedHGFun_eq_HGFun_div hGne, HGFun2F1_cos_arcsin hz]
  simp

end Complex
