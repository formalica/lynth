import Mathlib
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Lynth.HGIdentities.Common
import Lynth.Hypergeometric

/-!
# The complete elliptic integrals `K` and `E` as hypergeometric functions

Mathlib does not (yet) contain the complete elliptic integrals, so they are defined here by
their classical integral representations, in the *parameter* convention `m = k²` used by
`sympy`/`mpmath`:
$$ K(m) = \int_0^{\pi/2} \frac{dt}{\sqrt{1 - m \sin^2 t}}, \qquad
   E(m) = \int_0^{\pi/2} \sqrt{1 - m \sin^2 t}\, dt . $$

The two identities proved here are

* `Complex.HGFun2F1_ellipticK` : `₂F₁(1/2, 1/2; 1; m) = 2 K(m) / π`;
* `Complex.HGFun2F1_ellipticE` : `₂F₁(-1/2, 1/2; 1; m) = 2 E(m) / π`,

both for `‖m‖ < 1` (the hypergeometric series diverges outside the unit disc, where Lean's
convention makes the left-hand side `0`).

The proof is the classical one: expand the integrand by the binomial series
`(1 - u)^(-a) = ∑ₙ (a)ₙ uⁿ / n!` at `u = m sin²t`, integrate term by term (dominated
convergence, with the summable bound `‖m‖ⁿ`), and use Wallis' integral
`∫₀^{π/2} sin²ⁿ t dt = (π/2) (1/2)ₙ / n!`.
-/

open scoped Nat
open MeasureTheory

namespace Complex

/-- The Wallis coefficient `(1/2)ₙ / n! = (2n)! / (4ⁿ (n!)²)`, which is `2/π` times the
Wallis integral `∫₀^{π/2} sin²ⁿ t dt`. -/
private noncomputable def wallisCoeff (n : ℕ) : ℂ := (ascPochhammer ℂ n).eval (1 / 2) / (n ! : ℂ)

/-- The complete elliptic integral of the first kind, in the parameter convention `m = k²`. -/
noncomputable def ellipticK (m : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), (1 - m * (Real.sin t : ℂ) ^ 2) ^ (-(1 / 2) : ℂ)

/-- The complete elliptic integral of the second kind, in the parameter convention `m = k²`. -/
noncomputable def ellipticE (m : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), (1 - m * (Real.sin t : ℂ) ^ 2) ^ ((1 / 2) : ℂ)

section Wallis

/-- **Wallis' integral**: `∫₀^{π/2} sin²ⁿ t dt = (π/2) ∏_{i<n} (2i+1)/(2i+2)`. -/
private theorem integral_sin_pow_two_mul (n : ℕ) :
    (∫ t in (0 : ℝ)..(Real.pi / 2), Real.sin t ^ (2 * n))
      = Real.pi / 2 * ∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * i + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h := integral_sin_pow (a := 0) (b := Real.pi / 2) (n := 2 * n)
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, h, ih, Finset.prod_range_succ]
      simp [Real.sin_pi_div_two, Real.cos_pi_div_two]
      field_simp

/-- The Wallis product is `(1/2)ₙ / n!`. -/
private theorem prod_wallis_eq (n : ℕ) :
    ((∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * i + 2) : ℝ) : ℂ) = wallisCoeff n := by
  induction n with
  | zero => simp [wallisCoeff]
  | succ n ih =>
      have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hn : (2 * (n : ℂ) + 2) ≠ 0 := by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      rw [Finset.prod_range_succ, Complex.ofReal_mul, ih, wallisCoeff, wallisCoeff,
        ascPochhammer_succ_eval, Nat.factorial_succ]
      push_cast
      field_simp
      ring

/-- Wallis' integral, complex-valued form: `∫₀^{π/2} sin²ⁿ t dt = (π/2) (1/2)ₙ / n!`. -/
private theorem integral_sin_pow_two_mul_complex (n : ℕ) :
    (∫ t in (0 : ℝ)..(Real.pi / 2), (Real.sin t : ℂ) ^ (2 * n))
      = (Real.pi / 2 : ℝ) * wallisCoeff n := by
  rw [show (fun t : ℝ => (Real.sin t : ℂ) ^ (2 * n))
      = fun t : ℝ => ((Real.sin t ^ (2 * n) : ℝ) : ℂ) by funext t; push_cast; ring,
    intervalIntegral.integral_ofReal, integral_sin_pow_two_mul, ← prod_wallis_eq]
  push_cast
  ring

end Wallis

section Termwise

/-- `‖(-1/2)ₙ / n!‖ ≤ 1`. -/
private theorem norm_ascPochhammer_neg_half_div_factorial_le (n : ℕ) :
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
          div_le_one (by positivity), abs_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity),
          abs_le]
        constructor <;> linarith
      calc ‖(ascPochhammer ℂ n).eval (-1 / 2) / (n ! : ℂ)‖ * ‖(-1 / 2 + (n : ℂ)) / ((n : ℂ) + 1)‖
          ≤ 1 * 1 := mul_le_mul ih h2 (norm_nonneg _) zero_le_one
        _ = 1 := by ring

/-- Term-by-term integration of the binomial series over `[0, π/2]`. -/
private theorem hasSum_integral_binomial {a : ℂ}
    (hb : ∀ n : ℕ, ‖(ascPochhammer ℂ n).eval a / (n ! : ℂ)‖ ≤ 1) {m : ℂ} (hm : ‖m‖ < 1) :
    HasSum (fun n : ℕ => ((ascPochhammer ℂ n).eval a / (n ! : ℂ)) * m ^ n *
        ((Real.pi / 2 : ℝ) : ℂ) * wallisCoeff n)
      (∫ t in (0 : ℝ)..(Real.pi / 2), (1 - m * (Real.sin t : ℂ) ^ 2) ^ (-a)) := by
  have hm0 : (0 : ℝ) ≤ ‖m‖ := norm_nonneg m
  have hnorm : ∀ t : ℝ, ‖m * (Real.sin t : ℂ) ^ 2‖ ≤ ‖m‖ := by
    intro t
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |Real.sin t| ^ 2 ≤ 1 := by
      nlinarith [abs_nonneg (Real.sin t), Real.abs_sin_le_one t]
    calc ‖m‖ * |Real.sin t| ^ 2 ≤ ‖m‖ * 1 := by
          exact mul_le_mul_of_nonneg_left h1 (norm_nonneg m)
      _ = ‖m‖ := mul_one _
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
      (F := fun (n : ℕ) (t : ℝ) =>
        ((ascPochhammer ℂ n).eval a / (n ! : ℂ)) * (m * (Real.sin t : ℂ) ^ 2) ^ n)
      (f := fun t : ℝ => (1 - m * (Real.sin t : ℂ) ^ 2) ^ (-a))
      (bound := fun (n : ℕ) (_ : ℝ) => ‖m‖ ^ n) (a := 0) (b := Real.pi / 2)
      (μ := MeasureTheory.volume) ?_ ?_ ?_ ?_ ?_
  · refine key.congr_fun fun n => ?_
    have hfun : (fun t : ℝ =>
        ((ascPochhammer ℂ n).eval a / (n ! : ℂ)) * (m * (Real.sin t : ℂ) ^ 2) ^ n)
        = fun t : ℝ => (((ascPochhammer ℂ n).eval a / (n ! : ℂ)) * m ^ n)
            * (Real.sin t : ℂ) ^ (2 * n) := by
      funext t
      rw [mul_pow, pow_mul']
      ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_sin_pow_two_mul_complex]
    ring
  · intro n
    exact (Continuous.aestronglyMeasurable (by fun_prop))
  · intro n
    filter_upwards with t _
    rw [norm_mul, norm_pow]
    calc ‖(ascPochhammer ℂ n).eval a / (n ! : ℂ)‖ * ‖m * (Real.sin t : ℂ) ^ 2‖ ^ n
        ≤ 1 * ‖m‖ ^ n :=
          mul_le_mul (hb n) (pow_le_pow_left₀ (norm_nonneg _) (hnorm t) n)
            (by positivity) zero_le_one
      _ = ‖m‖ ^ n := one_mul _
  · filter_upwards with t _
    exact summable_geometric_of_lt_one hm0 hm
  · exact intervalIntegrable_const
  · filter_upwards with t _
    exact hasSum_regularized1F0 (lt_of_le_of_lt (hnorm t) hm)

end Termwise

section Coefficients

private theorem one_not_nonpos_int : ∀ j ∈ ({1} : Multiset ℂ), ∀ k : ℕ, j ≠ -(k : ℂ) := by
  intro j hj k
  rw [Multiset.mem_singleton] at hj
  subst hj
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

/-- The coefficients of `₂F₁(1/2, 1/2; 1; ·)` are `((1/2)ₙ / n!)²`. -/
private theorem HGFunCoeff_ellipticK (n : ℕ) :
    HGFunCoeff {1 / 2, 1 / 2} {1} n = wallisCoeff n * wallisCoeff n := by
  have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [HGFunCoeff_eq_ascPochhammer _ one_not_nonpos_int n,
    show ({1 / 2, 1 / 2} : Multiset ℂ) = (1 / 2 : ℂ) ::ₘ {1 / 2} from rfl, wallisCoeff]
  simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, ascPochhammer_eval_one]
  field_simp

/-- The coefficients of `₂F₁(-1/2, 1/2; 1; ·)` are `((-1/2)ₙ / n!) ((1/2)ₙ / n!)`. -/
private theorem HGFunCoeff_ellipticE (n : ℕ) :
    HGFunCoeff {-1 / 2, 1 / 2} {1} n
      = ((ascPochhammer ℂ n).eval (-1 / 2) / (n ! : ℂ)) * wallisCoeff n := by
  have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [HGFunCoeff_eq_ascPochhammer _ one_not_nonpos_int n,
    show ({-1 / 2, 1 / 2} : Multiset ℂ) = (-1 / 2 : ℂ) ::ₘ {1 / 2} from rfl, wallisCoeff]
  simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, ascPochhammer_eval_one]
  field_simp

end Coefficients

/-- **The identity** `₂F₁(1/2, 1/2; 1; m) = 2 K(m) / π`, for `‖m‖ < 1`. -/
theorem HGFun2F1_ellipticK {m : ℂ} (hm : ‖m‖ < 1) :
    HGFun {1 / 2, 1 / 2} {1} m = 2 * ellipticK m / (Real.pi : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsum : HasSum (fun n : ℕ => ((ascPochhammer ℂ n).eval (1 / 2) / (n ! : ℂ)) * m ^ n *
      ((Real.pi / 2 : ℝ) : ℂ) * wallisCoeff n) (ellipticK m) := by
    rw [ellipticK]
    exact hasSum_integral_binomial norm_ascPochhammer_half_div_factorial_le hm
  have hK : HasSum (fun n : ℕ => HGFunCoeff {1 / 2, 1 / 2} {1} n * m ^ n)
      (2 * ellipticK m / (Real.pi : ℂ)) := by
    have h2 := hsum.mul_left (2 / (Real.pi : ℂ))
    rw [show (2 : ℂ) / (Real.pi : ℂ) * ellipticK m = 2 * ellipticK m / (Real.pi : ℂ) by ring] at h2
    refine h2.congr_fun fun n => ?_
    rw [HGFunCoeff_ellipticK, wallisCoeff]
    push_cast
    field_simp
  exact (HGFun_eq_tsum _ _ _).trans hK.tsum_eq

/-- **The identity** `₂F₁(-1/2, 1/2; 1; m) = 2 E(m) / π`, for `‖m‖ < 1`. -/
theorem HGFun2F1_ellipticE {m : ℂ} (hm : ‖m‖ < 1) :
    HGFun {-1 / 2, 1 / 2} {1} m = 2 * ellipticE m / (Real.pi : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsum : HasSum (fun n : ℕ => ((ascPochhammer ℂ n).eval (-1 / 2) / (n ! : ℂ)) * m ^ n *
      ((Real.pi / 2 : ℝ) : ℂ) * wallisCoeff n) (ellipticE m) := by
    rw [ellipticE, show ((1 / 2 : ℂ)) = -(-1 / 2 : ℂ) by ring]
    exact hasSum_integral_binomial norm_ascPochhammer_neg_half_div_factorial_le hm
  have hE : HasSum (fun n : ℕ => HGFunCoeff {-1 / 2, 1 / 2} {1} n * m ^ n)
      (2 * ellipticE m / (Real.pi : ℂ)) := by
    have h2 := hsum.mul_left (2 / (Real.pi : ℂ))
    rw [show (2 : ℂ) / (Real.pi : ℂ) * ellipticE m = 2 * ellipticE m / (Real.pi : ℂ) by ring] at h2
    refine h2.congr_fun fun n => ?_
    rw [HGFunCoeff_ellipticE]
    push_cast
    field_simp
  exact (HGFun_eq_tsum _ _ _).trans hE.tsum_eq

/-- The Gamma factor for the lower parameter `1` is `Γ(1) = 1`, so the regularized function
agrees with the classical one. -/
private theorem prod_map_Gamma_one : ((({1} : Multiset ℂ)).map Gamma).prod = 1 := by simp

/-- The regularized form of `₂F₁(1/2, 1/2; 1; m) = 2 K(m) / π`; since `Γ(1) = 1` the
right-hand side is unchanged. -/
theorem regularized2F1_ellipticK {m : ℂ} (hm : ‖m‖ < 1) :
    regularizedHGFun {1 / 2, 1 / 2} {1} m = 2 * ellipticK m / (Real.pi : ℂ) := by
  rw [← HGFun_eq_regularizedHGFun_of_prod_eq_one prod_map_Gamma_one, HGFun2F1_ellipticK hm]

/-- The regularized form of `₂F₁(-1/2, 1/2; 1; m) = 2 E(m) / π`; since `Γ(1) = 1` the
right-hand side is unchanged. -/
theorem regularized2F1_ellipticE {m : ℂ} (hm : ‖m‖ < 1) :
    regularizedHGFun {-1 / 2, 1 / 2} {1} m = 2 * ellipticE m / (Real.pi : ℂ) := by
  rw [← HGFun_eq_regularizedHGFun_of_prod_eq_one prod_map_Gamma_one, HGFun2F1_ellipticE hm]

/-- Sanity check on the normalisation: `K(0) = π/2`. -/
theorem ellipticK_zero : ellipticK 0 = (Real.pi / 2 : ℝ) := by
  simp [ellipticK]

/-- Sanity check on the normalisation: `E(0) = π/2`. -/
theorem ellipticE_zero : ellipticE 0 = (Real.pi / 2 : ℝ) := by
  simp [ellipticE]

end Complex
