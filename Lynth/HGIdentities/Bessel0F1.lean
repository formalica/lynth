import Mathlib
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Lynth.HGIdentities.Common
import Lynth.Hypergeometric

/-!
# The confluent case `₀F₁(; 1/2; z) = cosh (2 √z)`

We prove, for every `z : ℂ` (the series is entire, so no hypothesis on `z` is needed),

`Complex.HGFun {} {1 / 2} z = Complex.cosh (2 * Complex.sqrt z)`.

The proof is the classical one: the coefficients of `₀F₁(; 1/2; ·)` are `1 / (n! (1/2)ₙ)`, and
the series for `cosh (2 √z)` is `∑ₙ (2√z)^{2n} / (2n)! = ∑ₙ 4ⁿ zⁿ / (2n)!`, so the two series
agree by the duplication formula `(2n)! = 4ⁿ n! (1/2)ₙ` (`Complex.factorial_two_mul_cast`).

The regularized version carries the extra factor `1 / Γ(1/2) = 1 / √π`, see
`Complex.regularized0F1_0`.
-/

open scoped Nat

namespace Complex

/-- The coefficients of `₀F̃₁(; 1/2; ·)` are `1 / (n! (1/2)ₙ Γ(1/2))`. -/
private theorem regularizedHGFunCoeff_bessel_half (n : ℕ) :
    regularizedHGFunCoeff {} {1 / 2} n
      = 1 / ((n ! : ℂ) * (ascPochhammer ℂ n).eval (1 / 2) * Gamma (1 / 2)) := by
  rw [regularizedHGFunCoeff]
  simp only [Multiset.empty_eq_zero, Multiset.map_zero, Multiset.prod_zero,
    Multiset.map_singleton, Multiset.prod_singleton]
  rw [Gamma_half_add_nat n, mul_assoc]

/-- The coefficients of `₀F₁(; 1/2; ·)` are `1 / (n! (1/2)ₙ)`. -/
private theorem HGFunCoeff_bessel_half (n : ℕ) :
    HGFunCoeff {} {1 / 2} n = 1 / ((n ! : ℂ) * (ascPochhammer ℂ n).eval (1 / 2)) := by
  have hk : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hp : (ascPochhammer ℂ n).eval (1 / 2) ≠ 0 := ascPochhammer_half_ne_zero n
  have hg : Gamma ((1 : ℂ) / 2) ≠ 0 := Gamma_one_half_ne_zero
  rw [HGFunCoeff_def, regularizedHGFunCoeff_bessel_half]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  field_simp

/-- The series of `₀F₁(; 1/2; z)` sums to `cosh (2 √z)`. -/
private theorem hasSum_HGFun0F1_0 (z : ℂ) :
    HasSum (fun n : ℕ => HGFunCoeff {} {1 / 2} n * z ^ n) (Complex.cosh (2 * Complex.sqrt z)) := by
  refine (Complex.hasSum_cosh (2 * Complex.sqrt z)).congr_fun fun n => ?_
  have hsq : Complex.sqrt z ^ 2 = z := sqrt_sq_eq z
  have hpow : (2 * Complex.sqrt z) ^ (2 * n) = 4 ^ n * z ^ n := by
    rw [mul_pow, pow_mul, pow_mul, hsq]
    norm_num
  have hk : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hp : (ascPochhammer ℂ n).eval (1 / 2) ≠ 0 := ascPochhammer_half_ne_zero n
  have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [hpow, factorial_two_mul_cast n, HGFunCoeff_bessel_half]
  field_simp

/-- **The requested identity**: `₀F₁(; 1/2; z) = cosh (2 √z)` for every `z : ℂ`. -/
theorem hypergeometric0F1_0 {z : ℂ} :
    HGFun {} {1 / 2} z = Complex.cosh (2 * Complex.sqrt z) := by
  rw [HGFun_eq_tsum]
  exact (hasSum_HGFun0F1_0 z).tsum_eq

/-- The regularized version of the identity: the regularized function differs from the classical
one by the factor `1 / Γ(1/2) = 1 / √π`. -/
theorem regularized0F1_0 {z : ℂ} :
    regularizedHGFun {} {1 / 2} z = Complex.cosh (2 * Complex.sqrt z) / Gamma (1 / 2) := by
  have hg : Gamma ((1 : ℂ) / 2) ≠ 0 := Gamma_one_half_ne_zero
  have h := hypergeometric0F1_0 (z := z)
  rw [HGFun_def] at h
  simp only [Multiset.map_singleton, Multiset.prod_singleton] at h
  rw [eq_div_iff hg, mul_comm]
  exact h

end Complex
