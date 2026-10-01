import Mathlib
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Lynth.HGIdentities.Common
import Lynth.Hypergeometric
import Lynth.ComplexFuncs

/-!
# `₂F₁(1/2, 1; 3/2; z) = artanh √z / √z`

The coefficients of this hypergeometric series are
`(1/2)ₙ (1)ₙ / (n! (3/2)ₙ) = (1/2)ₙ / (3/2)ₙ = 1/(2n+1)`,
so the identity to be proved is the classical series
`∑ₙ zⁿ/(2n+1) = artanh(√z)/√z`.

It is proved by showing that `v ↦ v ∑ₙ cₙ (v²)ⁿ` and `artanh` have the same derivative
`1/(1-v²)` on the unit disc and the same value `0` at the origin; that series computation is
`Complex.tsum_atanhCoeff_eq`, in `Lynth.ComplexFuncs`.

## Main results

* `Complex.HGFun2F1_atanh` : `₂F₁(1/2, 1; 3/2; z) = artanh(√z)/√z` for `0 < ‖z‖ < 1`;
* `Complex.regularized2F1_atanh` : the regularized version, which carries the extra factor
  `1/Γ(3/2)`;
* `Complex.not_HGFun2F1_atanh_at_zero` : the hypothesis `z ≠ 0` cannot be dropped.
-/

open scoped Nat
open Metric

namespace Complex

/-- The coefficients of `₂F₁(1/2, 1; 3/2; ·)` are `1/(2n+1)`. -/
private theorem HGFunCoeff_atanh (n : ℕ) : HGFunCoeff {1 / 2, 1} {3 / 2} n = atanhCoeff n := by
  rw [HGFunCoeff_eq_ascPochhammer _ three_half_not_nonpos_int n, atanhCoeff,
    show ({1 / 2, 1} : Multiset ℂ) = (1 / 2 : ℂ) ::ₘ {1} from rfl]
  simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, ascPochhammer_eval_one, ascPochhammer_three_half]
  have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hhalf := ascPochhammer_half_ne_zero n
  have h2n := two_mul_add_one_ne_zero n
  field_simp

/-- **The identity** `₂F₁(1/2, 1; 3/2; z) = artanh(√z)/√z`, valid on the punctured unit disc. -/
theorem HGFun2F1_atanh {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HGFun {1 / 2, 1} {3 / 2} z = artanh (Complex.sqrt z) / Complex.sqrt z := by
  have hw : ‖Complex.sqrt z‖ < 1 := norm_sqrt_lt_one hz
  have hw0 : Complex.sqrt z ≠ 0 := sqrt_ne_zero_of_ne_zero hz0
  have hsq : Complex.sqrt z ^ 2 = z := sqrt_sq_eq z
  have key := tsum_atanhCoeff_eq hw
  rw [hsq] at key
  rw [HGFun_eq_tsum]
  rw [show (∑' n : ℕ, HGFunCoeff {1 / 2, 1} {3 / 2} n * z ^ n)
      = ∑' n : ℕ, atanhCoeff n * z ^ n from tsum_congr fun n => by rw [HGFunCoeff_atanh]]
  rw [← key]
  field_simp

/-- The regularized form of the identity: the regularized function carries an extra factor
`1/Γ(3/2)`. -/
theorem regularized2F1_atanh {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    regularizedHGFun {1 / 2, 1} {3 / 2} z =
      artanh (Complex.sqrt z) / Complex.sqrt z / Gamma (3 / 2) := by
  have hGne : ((({3 / 2} : Multiset ℂ)).map Gamma).prod ≠ 0 :=
    prod_map_Gamma_ne_zero three_half_not_nonpos_int
  rw [regularizedHGFun_eq_HGFun_div hGne, HGFun2F1_atanh hz hz0]
  simp

/-- The hypothesis `z ≠ 0` is necessary: at `z = 0` the left-hand side is `1` while the
right-hand side is `0/0 = 0`. -/
theorem not_HGFun2F1_atanh_at_zero :
    ¬ ∀ z : ℂ, HGFun {1 / 2, 1} {3 / 2} z = artanh (Complex.sqrt z) / Complex.sqrt z := by
  intro h
  have h0 := h 0
  rw [HGFun_eq_tsum] at h0
  have hzero : (∑' n : ℕ, HGFunCoeff {1 / 2, 1} {3 / 2} n * (0 : ℂ) ^ n) = 1 := by
    rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn]), HGFunCoeff_atanh]
    simp [atanhCoeff]
  rw [hzero] at h0
  simp [Complex.sqrt] at h0

end Complex
