import Mathlib
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Lynth.HGIdentities.Common

/-!
# The (non-regularized) generalized hypergeometric function `HGFun`

`Complex.regularizedHGFun a b` (defined in Mathlib, in the file
`Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric`) is the
*regularized* generalized hypergeometric function
$$ {}_p\tilde F_q(a; b; z) = \sum_n \frac{\prod_i (a_i)_n}{n!\,\prod_j \Gamma(b_j + n)} z^n . $$

The classical (non-regularized) hypergeometric function is obtained from it by multiplying with
`∏ⱼ Γ(bⱼ)`:
$$ {}_pF_q(a; b; z) = \Big(\prod_j \Gamma(b_j)\Big)\, {}_p\tilde F_q(a; b; z)
  = \sum_n \frac{\prod_i (a_i)_n}{n!\,\prod_j (b_j)_n} z^n . $$

This is the definition of `Complex.HGFun` below: it calls `Complex.regularizedHGFun` under the
hood.  The classical series representation is `Complex.HGFunCoeff_eq_ascPochhammer` together with
`Complex.HGFun_eq_tsum`.

## Main definitions

* `Complex.HGFun` : the generalized hypergeometric function `pFq`;
* `Complex.HGFunCoeff` : its Taylor coefficients.

## Main results

* `Complex.HGFun_eq_tsum` : `HGFun a b z = ∑' n, HGFunCoeff a b n * z ^ n`
  (the `HGFun` analogue of `Complex.regularizedHGFun_eq_tsum`);
* `Complex.HGFunCoeff_eq_ascPochhammer` : the coefficients are the classical ones,
  `∏ᵢ (aᵢ)ₙ / (n! ∏ⱼ (bⱼ)ₙ)`, whenever no `bⱼ` is a non-positive integer;
* `Complex.HGFun_eq_regularizedHGFun_of_prod_eq_one`,
  `Complex.regularizedHGFun_eq_HGFun_div` : the dictionary between the two functions.
-/

open scoped Nat

namespace Complex

variable {a b : Multiset ℂ} {z : ℂ} {n : ℕ}

/-- The coefficients of the (non-regularized) generalized hypergeometric series; they are the
coefficients of the regularized series multiplied by `∏ⱼ Γ(bⱼ)`. -/
noncomputable def HGFunCoeff (a b : Multiset ℂ) (n : ℕ) : ℂ :=
  (b.map Gamma).prod * regularizedHGFunCoeff a b n

/-- The (non-regularized) generalized hypergeometric function `pFq`, defined through the
regularized one by `pFq(a; b; z) = (∏ⱼ Γ(bⱼ)) · pF̃q(a; b; z)`. -/
noncomputable def HGFun (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  (b.map Gamma).prod * regularizedHGFun a b z

theorem HGFun_def (a b : Multiset ℂ) (z : ℂ) :
    HGFun a b z = (b.map Gamma).prod * regularizedHGFun a b z := rfl

theorem HGFunCoeff_def (a b : Multiset ℂ) (n : ℕ) :
    HGFunCoeff a b n = (b.map Gamma).prod * regularizedHGFunCoeff a b n := rfl

/-- The `HGFun` analogue of `Complex.regularizedHGFun_eq_tsum`: the hypergeometric function is
the sum of its power series. -/
theorem HGFun_eq_tsum (a b : Multiset ℂ) (z : ℂ) :
    HGFun a b z = ∑' n : ℕ, HGFunCoeff a b n * z ^ n := by
  rw [HGFun_def, regularizedHGFun_eq_tsum, ← tsum_mul_left]
  exact tsum_congr fun n => by rw [HGFunCoeff_def]; ring

/-- If `∏ⱼ Γ(bⱼ) = 1` (for instance if `b` is empty, or consists of positive integers with
`∏ⱼ (bⱼ - 1)! = 1`), the hypergeometric function agrees with the regularized one. -/
theorem HGFun_eq_regularizedHGFun_of_prod_eq_one (h : (b.map Gamma).prod = 1) :
    HGFun a b z = regularizedHGFun a b z := by
  rw [HGFun_def, h, one_mul]

@[simp]
theorem HGFun_empty (a : Multiset ℂ) (z : ℂ) : HGFun a {} z = regularizedHGFun a {} z :=
  HGFun_eq_regularizedHGFun_of_prod_eq_one (by simp)

/-- The regularized function in terms of the non-regularized one. -/
theorem regularizedHGFun_eq_HGFun_div (h : (b.map Gamma).prod ≠ 0) :
    regularizedHGFun a b z = HGFun a b z / (b.map Gamma).prod := by
  rw [HGFun_def, mul_comm, mul_div_assoc, div_self h, mul_one]

section Classical

/-- `Γ(c + n) = (c)ₙ Γ(c)` for `c` not a non-positive integer. -/
theorem Gamma_add_natCast {c : ℂ} (hc : ∀ m : ℕ, c ≠ -m) (n : ℕ) :
    Gamma (c + n) = (ascPochhammer ℂ n).eval c * Gamma c := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hne : c + n ≠ 0 := fun h => hc n (by linear_combination h)
      rw [show c + ((n + 1 : ℕ) : ℂ) = (c + n) + 1 by push_cast; ring,
        Complex.Gamma_add_one _ hne, ih]
      simp only [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_natCast]
      ring

theorem prod_map_Gamma_add (hb : ∀ j ∈ b, ∀ m : ℕ, j ≠ -m) (n : ℕ) :
    (b.map (fun j => Gamma (j + n))).prod
      = (b.map (ascPochhammer ℂ n).eval).prod * (b.map Gamma).prod := by
  rw [← Multiset.prod_map_mul]
  exact congrArg Multiset.prod (Multiset.map_congr rfl (fun j hj => Gamma_add_natCast (hb j hj) n))

theorem prod_map_Gamma_ne_zero (hb : ∀ j ∈ b, ∀ m : ℕ, j ≠ -m) :
    (b.map Gamma).prod ≠ 0 := by
  intro h
  obtain ⟨j, hj, hj0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h)
  exact Gamma_ne_zero (hb j hj) hj0

/-- The classical form of the hypergeometric coefficients: if no `bⱼ` is a non-positive integer,
then `HGFunCoeff a b n = ∏ᵢ (aᵢ)ₙ / (n! ∏ⱼ (bⱼ)ₙ)`. -/
theorem HGFunCoeff_eq_ascPochhammer (a : Multiset ℂ) (hb : ∀ j ∈ b, ∀ m : ℕ, j ≠ -m) (n : ℕ) :
    HGFunCoeff a b n =
      (a.map (ascPochhammer ℂ n).eval).prod / (n ! * (b.map (ascPochhammer ℂ n).eval).prod) := by
  have hG : (b.map Gamma).prod ≠ 0 := prod_map_Gamma_ne_zero hb
  rw [HGFunCoeff_def, regularizedHGFunCoeff, prod_map_Gamma_add hb n]
  field_simp

end Classical

end Complex
