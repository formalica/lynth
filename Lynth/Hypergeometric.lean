module

public import Init.Core
public import Init.Prelude
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Multiset.ZeroCons
public import Lynth.Hypergeometric.Defs
import Mathlib
import all Lynth.Hypergeometric.Defs
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import all Lynth.HGIdentities.Common

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

theorem not_isPfaffRegime_of_card_a (h : a.card ≠ 2) : ¬ IsPfaffRegime a b z := by
  rintro ⟨_, _, ⟨p, ha, _⟩, _⟩
  apply h
  rw [ha]
  simp

theorem not_isPfaffRegime_of_card_b (h : b.card ≠ 1) : ¬ IsPfaffRegime a b z := by
  rintro ⟨_, _, _, ⟨c, hb⟩⟩
  apply h
  rw [hb]
  simp

theorem not_isPfaffRegime_of_re_ge (h : -1 ≤ z.re) : ¬ IsPfaffRegime a b z := by
  rintro ⟨hz, _⟩
  linarith

theorem not_isPfaffRegime_of_norm_le_one (h : ‖z‖ ≤ 1) : ¬ IsPfaffRegime a b z := by
  apply not_isPfaffRegime_of_re_ge
  have h1 := (abs_re_le_norm z).trans h
  linarith [abs_le.mp h1]

theorem not_isPfaffRegime_of_norm_lt_one (h : ‖z‖ < 1) : ¬ IsPfaffRegime a b z :=
  not_isPfaffRegime_of_norm_le_one h.le

macro "not_pfaff_tac" : tactic => `(tactic|
  first
  | assumption
  | (apply not_isPfaffRegime_of_card_a; simp; done)
  | (apply not_isPfaffRegime_of_card_b; simp; done)
  | (apply not_isPfaffRegime_of_re_ge; norm_num; done)
  | (apply not_isPfaffRegime_of_norm_le_one; assumption)
  | (apply not_isPfaffRegime_of_norm_lt_one; assumption))

theorem HGFun_def (a b : Multiset ℂ) (z : ℂ)
    (hnp : ¬ IsPfaffRegime a b z := by not_pfaff_tac) :
    HGFun a b z = (b.map Gamma).prod * regularizedHGFun a b z := by
  simp only [HGFun, HGFunBase, hnp, dite_false]

theorem HGFunCoeff_def (a b : Multiset ℂ) (n : ℕ) :
    HGFunCoeff a b n = (b.map Gamma).prod * regularizedHGFunCoeff a b n := rfl

/-- The `HGFun` analogue of `Complex.regularizedHGFun_eq_tsum`: the hypergeometric function is
the sum of its power series. -/
theorem HGFun_eq_tsum (a b : Multiset ℂ) (z : ℂ)
    (hnp : ¬ IsPfaffRegime a b z := by not_pfaff_tac) :
    HGFun a b z = ∑' n : ℕ, HGFunCoeff a b n * z ^ n := by
  rw [HGFun_def a b z hnp, regularizedHGFun_eq_tsum, ← tsum_mul_left]
  exact tsum_congr fun n => by rw [HGFunCoeff_def]; ring

/-- If `∏ⱼ Γ(bⱼ) = 1` (for instance if `b` is empty, or consists of positive integers with
`∏ⱼ (bⱼ - 1)! = 1`), the hypergeometric function agrees with the regularized one. -/
theorem HGFun_eq_regularizedHGFun_of_prod_eq_one (h : (b.map Gamma).prod = 1)
    (hnp : ¬ IsPfaffRegime a b z := by not_pfaff_tac) :
    HGFun a b z = regularizedHGFun a b z := by
  rw [HGFun_def a b z hnp, h, one_mul]

@[simp]
public theorem HGFun_empty (a : Multiset ℂ) (z : ℂ) : HGFun a {} z = regularizedHGFun a {} z :=
  HGFun_eq_regularizedHGFun_of_prod_eq_one (by simp) (not_isPfaffRegime_of_card_b (by simp))

/-- The regularized function in terms of the non-regularized one. -/
theorem regularizedHGFun_eq_HGFun_div (h : (b.map Gamma).prod ≠ 0)
    (hnp : ¬ IsPfaffRegime a b z := by not_pfaff_tac) :
    regularizedHGFun a b z = HGFun a b z / (b.map Gamma).prod := by
  rw [HGFun_def a b z hnp, mul_comm, mul_div_assoc, div_self h, mul_one]

theorem div_sub_one_re_pos {z : ℂ} (hz : z.re < -1) : 0 < (z / (z - 1)).re := by
  rw [Complex.div_re, ← add_div]
  have h1 : (z - 1).re = z.re - 1 := by simp
  have h2 : (z - 1).im = z.im := by simp
  have hns : 0 < Complex.normSq (z - 1) := by
    rw [Complex.normSq_apply, h1, h2]
    have : 0 < (z.re - 1) * (z.re - 1) := by nlinarith
    nlinarith [mul_self_nonneg z.im]
  have hnum : 0 < z.re * (z - 1).re + z.im * (z - 1).im := by
    rw [h1, h2]
    have : 0 < z.re * (z.re - 1) := by nlinarith
    nlinarith [mul_self_nonneg z.im]
  exact div_pos hnum hns

theorem pair_eq_of_cplxLe {a₀ a₁ a₀' a₁' : ℂ}
    (heq : ({a₀, a₁} : Multiset ℂ) = {a₀', a₁'})
    (h1 : cplxLe a₀ a₁) (h2 : cplxLe a₀' a₁') :
    a₀ = a₀' ∧ a₁ = a₁' := by
  have hmem0 : a₀' ∈ ({a₀, a₁} : Multiset ℂ) := by rw [heq]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem0
  have hsum : a₀ + a₁ = a₀' + a₁' := by
    have := congrArg Multiset.sum heq
    simpa [Multiset.insert_eq_cons] using this
  rcases hmem0 with rfl | rfl
  · exact ⟨rfl, add_left_cancel hsum⟩
  · have ha1 : a₀ = a₁' := by linear_combination hsum
    subst ha1
    have heq' := cplxLe_antisymm h1 h2
    exact ⟨heq', heq'.symm⟩

theorem HGFun_pfaff_eq (a₀ a₁ c z : ℂ) (hz : z.re < -1)
    (ha₀ : 0 < a₀.re) (ha₁ : 0 < a₁.re) (hle : cplxLe a₀ a₁) :
    HGFun {a₀, a₁} {c} z =
      (1 - z) ^ (-a₀) * HGFun {a₀, c - a₁} {c} (z / (z - 1)) := by
  have hPf : IsPfaffRegime {a₀, a₁} {c} z := by
    refine ⟨hz, ?_, ⟨(a₀, a₁), rfl, hle⟩, ⟨c, rfl⟩⟩
    intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hNotPf : ¬ IsPfaffRegime {a₀, c - a₁} {c} (z / (z - 1)) :=
    not_isPfaffRegime_of_re_ge (by linarith [div_sub_one_re_pos hz])
  simp only [HGFun, hPf, hNotPf, dite_true, dite_false]
  have hp_spec := Classical.choose_spec hPf.2.2.1
  have hc_spec := Classical.choose_spec hPf.2.2.2
  obtain ⟨ha0_eq, ha1_eq⟩ := pair_eq_of_cplxLe hp_spec.1 hle hp_spec.2
  have hc_eq : c = Classical.choose hPf.2.2.2 := by
    have := congrArg Multiset.sum hc_spec
    simpa using this
  rw [← ha0_eq, ← ha1_eq, ← hc_eq]

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
