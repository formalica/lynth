import Mathlib
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Lynth.HGIdentities.Common
import Lynth.Hypergeometric

open scoped BigOperators
open scoped Real
open scoped Nat

set_option maxHeartbeats 1000000

/-!
# The hypergeometric function `₁F₀`

This file proves the requested identity
$$ {}_1F_0(a; ; z) = (1-z)^{-a} $$
for the generalized hypergeometric function `Complex.HGFun` defined in
`Lynth.Hypergeometric` (which calls the regularized function
`Complex.regularizedHGFun` of Mathlib's
`Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric` under the hood),
inside the disc of convergence `‖z‖ < 1`.

Since the list of lower parameters is empty, the Gamma factor relating the two functions is `1`,
so `₁F₀` and `₁F̃₀` coincide here.

The unrestricted statement is **false**: outside the closed unit disc the defining series
diverges, so (with Lean's convention that the sum of a non-summable family is `0`) the
left-hand side vanishes while the right-hand side does not.  This is recorded in
`Complex.not_HGFun1F0_of_norm_ge_one` below.

The auxiliary results on the binomial series live in `Lynth.Common`.
-/

namespace Complex

/-- The coefficients of `₁F̃₀(a; ; ·)` are `(a)ₙ / n!`. -/
private theorem regularizedHGFunCoeff_singleton_empty (a : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {a} {} n = (ascPochhammer ℂ n).eval a / (Nat.factorial n : ℂ) := by
  simp [regularizedHGFunCoeff]

/-- The coefficients of `₁F₀(a; ; ·)` are `(a)ₙ / n!`. -/
private theorem HGFunCoeff_singleton_empty (a : ℂ) (n : ℕ) :
    HGFunCoeff {a} {} n = (ascPochhammer ℂ n).eval a / (Nat.factorial n : ℂ) := by
  rw [HGFunCoeff_def, regularizedHGFunCoeff_singleton_empty]
  simp

/-- **The requested identity** for the regularized function: `₁F̃₀(a; ; z) = (1 - z)^(-a)` for
`‖z‖ < 1`. -/
theorem regularized1F0 {a z : ℂ} (hz : ‖z‖ < 1) :
    regularizedHGFun {a} {} z = (1 - z) ^ (-a) := by
  rw [regularizedHGFun, FormalMultilinearSeries.sum]
  refine ((hasSum_regularized1F0 (a := a) hz).congr_fun fun n => ?_).tsum_eq
  rw [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    regularizedHGFunCoeff_singleton_empty, smul_eq_mul]

/-- **The requested identity**: `₁F₀(a; ; z) = (1 - z)^(-a)` for `‖z‖ < 1`.

The hypothesis `‖z‖ < 1` is necessary; see `Complex.not_HGFun1F0_of_norm_ge_one`. -/
theorem HGFun1F0 {a z : ℂ} (hz : ‖z‖ < 1) :
    HGFun {a} {} z = (1 - z) ^ (-a) := by
  rw [HGFun_empty]
  exact regularized1F0 hz

/-- The identity `₁F̃₀(a; ; z) = (1 - z)^(-a)` fails without a restriction on `z`: for `a = 1`
and `z = 2` the defining series diverges (so its sum is `0` by convention), whereas
`(1 - 2)^(-1) = -1`. -/
theorem not_regularized1F0_of_norm_ge_one :
    ¬ ∀ a z : ℂ, regularizedHGFun {a} {} z = (1 - z) ^ (-a) := by
  intro h
  have h1 := h 1 2
  have hns : ¬ Summable (fun n : ℕ => (2 : ℂ) ^ n) := by
    rw [summable_geometric_iff_norm_lt_one]; norm_num
  have hzero : regularizedHGFun {1} {} (2 : ℂ) = 0 := by
    rw [regularizedHGFun, FormalMultilinearSeries.sum]
    refine tsum_eq_zero_of_not_summable fun hs => hns (hs.congr fun n => ?_)
    rw [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      regularizedHGFunCoeff_singleton_empty, smul_eq_mul, ascPochhammer_eval_one,
      div_self (by exact_mod_cast Nat.factorial_ne_zero n), one_mul]
  rw [hzero, show (1 - 2 : ℂ) = -1 by ring,
    show (-(1 : ℂ)) = ((-1 : ℤ) : ℂ) by norm_num, cpow_intCast] at h1
  norm_num at h1

/-- The identity `₁F₀(a; ; z) = (1 - z)^(-a)` fails without a restriction on `z`, for the same
reason as in `Complex.not_regularized1F0_of_norm_ge_one`. -/
theorem not_HGFun1F0_of_norm_ge_one :
    ¬ ∀ a z : ℂ, HGFun {a} {} z = (1 - z) ^ (-a) := by
  intro h
  exact not_regularized1F0_of_norm_ge_one fun a z => by
    rw [← HGFun_empty]; exact h a z

end Complex

/-
The statement as originally requested is not provable as stated, for the reason recorded in
`Complex.not_regularized1F0_of_norm_ge_one` (the series defining the left-hand side diverges
for `‖z‖ ≥ 1`, so its sum is `0` by Lean's convention).  The corrected versions, with the
hypothesis `‖z‖ < 1`, are `Complex.regularized1F0` and `Complex.HGFun1F0` above.

import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

theorem Complex.regularized1F0 {a z : ℂ} :
    regularizedHGFun {a} {} z = (1- z)^(-a) := by
  sorry
-/
