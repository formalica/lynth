import Mathlib
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Lynth.HGIdentities.Common
import Lynth.Hypergeometric
import Lynth.ComplexFuncs

/-!
# The logarithmic case `₂F₁(1, 1; 2; z) = -log(1 - z) / z`

Since `Γ(2) = 1`, the regularized function `₂F̃₁(1, 1; 2; ·)` coincides with the classical
Gauss hypergeometric function `₂F₁(1, 1; 2; ·)`, whose coefficients are `1 / (n + 1)`.

Inside the disc of convergence we prove
`regularizedHGFun {1, 1} {2} z = - (log (1 - z) / z)`  for `z ≠ 0` and `‖z‖ < 1`.

The hypothesis `‖z‖ < 1` cannot be dropped: the defining series diverges for `‖z‖ ≥ 1`
(also for `‖z‖ = 1`, where the coefficient family `zⁿ/(n+1)` is not absolutely summable),
so the left-hand side is `0` by Lean's convention for non-summable families, while the
right-hand side is not.  See `Complex.not_regularized2F1_1`.
-/

open scoped Nat

namespace Complex

/-- The coefficients of `₂F̃₁(1, 1; 2; ·)` are `1 / (n + 1)`. -/
private theorem regularizedHGFunCoeff_log (n : ℕ) :
    regularizedHGFunCoeff {1, 1} {2} n = 1 / ((n : ℂ) + 1) := by
  have hgamma : Gamma ((2 : ℂ) + n) = ((n + 1)! : ℕ) := by
    have := Complex.Gamma_nat_eq_factorial (n + 1)
    rw [show ((2 : ℂ) + n) = ((n + 1 : ℕ) : ℂ) + 1 by push_cast; ring]
    exact this
  have hfac : ((n + 1)! : ℂ) = ((n : ℂ) + 1) * (n ! : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    have h := Nat.cast_ne_zero (R := ℂ) (n := n + 1) |>.mpr (Nat.succ_ne_zero n)
    simpa using h
  have hnum : (Multiset.map (fun x => Polynomial.eval x (ascPochhammer ℂ n)) {1, 1}).prod
      = (n ! : ℂ) ^ 2 := by
    rw [show ({1, 1} : Multiset ℂ) = (1 : ℂ) ::ₘ {1} from rfl]
    simp [ascPochhammer_eval_one, sq]
  simp only [regularizedHGFunCoeff, hnum, Multiset.map_singleton,
    Multiset.prod_singleton, hgamma]
  rw [hfac]
  field_simp

/-- **The requested identity** (corrected): `₂F̃₁(1, 1; 2; z) = -log(1-z)/z` on the punctured
unit disc.  The extra hypothesis `‖z‖ < 1` is necessary, see `Complex.not_regularized2F1_1`. -/
theorem regularized2F1_1 {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    regularizedHGFun {1, 1} {2} z = -(Complex.log (1 - z) / z) := by
  rw [regularizedHGFun, FormalMultilinearSeries.sum]
  refine ((hasSum_neg_log_div z hz hz0).congr_fun fun n => ?_).tsum_eq
  rw [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    regularizedHGFunCoeff_log, smul_eq_mul]

/-- The Gamma factor relating `₂F₁(1, 1; 2; ·)` and `₂F̃₁(1, 1; 2; ·)` is `Γ(2) = 1`. -/
private theorem prod_map_Gamma_two : ((({2} : Multiset ℂ)).map Gamma).prod = 1 := by simp

/-- **The requested identity** (corrected) for the non-regularized function:
`₂F₁(1, 1; 2; z) = -log(1-z)/z` on the punctured unit disc.  Since `Γ(2) = 1`, the right-hand
side is the same as in `Complex.regularized2F1_1`. -/
theorem HGFun2F1_1 {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HGFun {1, 1} {2} z = -(Complex.log (1 - z) / z) := by
  rw [HGFun_eq_regularizedHGFun_of_prod_eq_one prod_map_Gamma_two]
  exact regularized2F1_1 hz hz0

/-- The identity `₂F̃₁(1, 1; 2; z) = -log(1-z)/z` fails without the hypothesis `‖z‖ < 1`:
for `z = 2` the defining series diverges (so its sum is `0` by convention), while the
right-hand side is `-(π i / 2) ≠ 0`. -/
theorem not_regularized2F1_1 :
    ¬ ∀ z : ℂ, z ≠ 0 → regularizedHGFun {1, 1} {2} z = -(Complex.log (1 - z) / z) := by
  intro h
  have h1 := h 2 two_ne_zero
  have hnorm : ∀ N : ℕ, ‖(1 / ((N : ℂ) + 1)) * 2 ^ N‖ = 2 ^ N / ((N : ℝ) + 1) := by
    intro N
    rw [show ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) by push_cast; ring, norm_mul, norm_div, norm_one,
      Complex.norm_natCast, Complex.norm_pow]
    push_cast
    rw [Complex.norm_ofNat]
    ring
  have hns : ¬ Summable (fun n : ℕ => (1 / ((n : ℂ) + 1)) * 2 ^ n) := by
    intro hs
    have hlim := hs.tendsto_atTop_zero
    rw [tendsto_zero_iff_norm_tendsto_zero] at hlim
    obtain ⟨N, hN⟩ := (hlim.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)).exists
    rw [hnorm N] at hN
    have hpow : ((N : ℝ) + 1) ≤ 2 ^ N := by
      have h2 := Nat.lt_two_pow_self (n := N)
      have : (N : ℝ) + 1 ≤ ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast h2
      simpa using this
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [div_lt_one hN1] at hN
    linarith
  have hzero : regularizedHGFun {1, 1} {2} (2 : ℂ) = 0 := by
    rw [regularizedHGFun, FormalMultilinearSeries.sum]
    refine tsum_eq_zero_of_not_summable fun hs => hns (hs.congr fun n => ?_)
    rw [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      regularizedHGFunCoeff_log, smul_eq_mul]
  rw [hzero, show (1 - 2 : ℂ) = -1 by ring, Complex.log_neg_one] at h1
  have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  exact hpi (by linear_combination 2 * h1)

/-- The identity `₂F₁(1, 1; 2; z) = -log(1-z)/z` fails without the hypothesis `‖z‖ < 1`, for the
same reason as in `Complex.not_regularized2F1_1`. -/
theorem not_HGFun2F1_1 :
    ¬ ∀ z : ℂ, z ≠ 0 → HGFun {1, 1} {2} z = -(Complex.log (1 - z) / z) := by
  intro h
  refine not_regularized2F1_1 fun z hz0 => ?_
  rw [← HGFun_eq_regularizedHGFun_of_prod_eq_one (a := {1, 1}) prod_map_Gamma_two]
  exact h z hz0

end Complex

/-
The statement as originally requested is not provable as stated: the hypothesis `z ≠ 0` alone
does not suffice, since the defining series diverges for `‖z‖ ≥ 1`; see
`Complex.not_regularized2F1_1`.  The corrected version is `Complex.regularized2F1_1` above, and
its non-regularized counterpart is `Complex.HGFun2F1_1` (the two agree here, since `Γ(2) = 1`).

theorem Complex.regularized2F1_1 {z : ℂ} (hz : z ≠ 0) :
    regularizedHGFun {1, 1} {2} z = - (Complex.log (1 - z) / z) := by
  sorry
-/
