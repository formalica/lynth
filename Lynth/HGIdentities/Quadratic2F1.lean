import Mathlib
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Lynth.HGIdentities.Common
import Lynth.Hypergeometric

/-!
# The quadratic transformation `₂F̃₁(a, a + 1/2; 1/2; z)`

We prove, for `‖z‖ < 1`,
`regularizedHGFun {a, a + 1/2} {1/2} z
  = ((√z + 1)^(-2a) / 2 + (1 - √z)^(-2a) / 2) / Γ(1/2)`.

The factor `1 / Γ(1/2) = 1 / √π` is forced by the fact that `regularizedHGFun` is the
*regularized* hypergeometric function (its coefficients carry `1 / Γ(c + n)` instead of
`1 / (c)ₙ`); the classical identity is
`₂F₁(a, a + 1/2; 1/2; z) = ((1 + √z)^(-2a) + (1 - √z)^(-2a)) / 2`.

The proof is elementary: the binomial series for `(1 ± √z)^(-2a)` are added, which kills the
odd powers of `√z`, and the resulting even coefficients `(2a)_{2k} / (2k)!` are identified with
the hypergeometric coefficients by the duplication formulas
`(2a)_{2k} = 4^k (a)_k (a + 1/2)_k` and `(2k)! = 4^k k! (1/2)_k`.
-/

open scoped Nat

namespace Complex

/-- Duplication formula for the ascending Pochhammer symbol:
`(2a)_{2k} = 4^k (a)_k (a + 1/2)_k`. -/
private theorem ascPochhammer_two_mul_eval (a : ℂ) (k : ℕ) :
    (ascPochhammer ℂ (2 * k)).eval (2 * a)
      = 4 ^ k * ((ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval (a + 1 / 2)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h2 : 2 * (k + 1) = (2 * k) + 1 + 1 := by ring
      rw [h2, ascPochhammer_succ_eval, ascPochhammer_succ_eval, ascPochhammer_succ_eval,
        ascPochhammer_succ_eval, ih]
      push_cast
      ring

/-- The coefficients of `₂F̃₁(a, a + 1/2; 1/2; ·)` are `((2a)_{2k} / (2k)!) / Γ(1/2)`. -/
private theorem regularizedHGFunCoeff_quadratic (a : ℂ) (k : ℕ) :
    regularizedHGFunCoeff {a, a + 1 / 2} {1 / 2} k
      = ((ascPochhammer ℂ (2 * k)).eval (2 * a) / (((2 * k)! : ℕ) : ℂ)) / Gamma (1 / 2) := by
  have hnum : (Multiset.map (fun x => Polynomial.eval x (ascPochhammer ℂ k)) {a, a + 1 / 2}).prod
      = (ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval (a + 1 / 2) := by
    rw [show ({a, a + 1 / 2} : Multiset ℂ) = a ::ₘ {a + 1 / 2} from rfl]
    simp
  have hden : (Multiset.map (fun x => Gamma (x + k)) ({1 / 2} : Multiset ℂ)).prod
      = (ascPochhammer ℂ k).eval (1 / 2) * Gamma (1 / 2) := by
    rw [Multiset.map_singleton, Multiset.prod_singleton, Gamma_half_add_nat k]
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hp : (ascPochhammer ℂ k).eval (1 / 2) ≠ 0 := ascPochhammer_half_ne_zero k
  have hg : Gamma ((1 : ℂ) / 2) ≠ 0 := by
    rw [show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    exact Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  simp only [regularizedHGFunCoeff, hnum, hden]
  rw [ascPochhammer_two_mul_eval, factorial_two_mul_cast]
  have h4 : (4 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- The even-index binomial expansion: for `‖w‖ < 1`,
`((1 + w)^(-2a) + (1 - w)^(-2a)) / 2 = ∑ₖ ((2a)_{2k} / (2k)!) w^{2k}`. -/
private theorem hasSum_even_binomial (a w : ℂ) (hw : ‖w‖ < 1) :
    HasSum (fun k : ℕ => ((ascPochhammer ℂ (2 * k)).eval (2 * a) / (((2 * k)! : ℕ) : ℂ))
        * (w ^ 2) ^ k)
      ((1 + w) ^ (-(2 * a)) / 2 + (1 - w) ^ (-(2 * a)) / 2) := by
  have H₁ := hasSum_regularized1F0 (a := 2 * a) (z := -w) (by simpa using hw)
  have H₂ := hasSum_regularized1F0 (a := 2 * a) (z := w) hw
  rw [show (1 : ℂ) - -w = 1 + w by ring] at H₁
  have Hsum := (H₁.add H₂).div_const 2
  have Hval : ((1 + w) ^ (-(2 * a)) + (1 - w) ^ (-(2 * a))) / 2
      = (1 + w) ^ (-(2 * a)) / 2 + (1 - w) ^ (-(2 * a)) / 2 := by ring
  rw [Hval] at Hsum
  -- now select the even terms
  set F : ℕ → ℂ := fun n =>
    (((ascPochhammer ℂ n).eval (2 * a) / (n ! : ℂ)) * (-w) ^ n
      + ((ascPochhammer ℂ n).eval (2 * a) / (n ! : ℂ)) * w ^ n) / 2 with hF
  have HF : HasSum F ((1 + w) ^ (-(2 * a)) / 2 + (1 - w) ^ (-(2 * a)) / 2) := Hsum
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun m n h => by
    simp only [] at h; omega
  have hzero : ∀ x ∉ Set.range (fun k : ℕ => 2 * k), F x = 0 := by
    intro x hx
    have hodd : Odd x := by
      rcases Nat.even_or_odd x with he | ho
      · obtain ⟨t, ht⟩ := he
        exact absurd ⟨t, by simp only []; omega⟩ hx
      · exact ho
    have : (-w) ^ x = -(w ^ x) := hodd.neg_pow w
    simp [hF, this]
  have := (hinj.hasSum_iff (f := F) hzero).mpr HF
  refine this.congr_fun fun k => ?_
  have heven : Even (2 * k) := ⟨k, by ring⟩
  have hpow : (-w) ^ (2 * k) = w ^ (2 * k) := heven.neg_pow w
  simp only [Function.comp_apply, hF, hpow]
  rw [← pow_mul]
  ring

/-- **The requested identity** (corrected): for `‖z‖ < 1`,
`₂F̃₁(a, a + 1/2; 1/2; z) = ((√z + 1)^(-2a) / 2 + (1 - √z)^(-2a) / 2) / Γ(1/2)`. -/
theorem regularized2F1_2 {a z : ℂ} (hz : ‖z‖ < 1) :
    regularizedHGFun {a, a + 1 / 2} {1 / 2} z =
      ((Complex.sqrt z + 1) ^ (-2 * a) / 2 + (1 - Complex.sqrt z) ^ (-2 * a) / 2) /
        Gamma (1 / 2) := by
  have hw : ‖Complex.sqrt z‖ < 1 := norm_sqrt_lt_one hz
  have hsq : Complex.sqrt z ^ 2 = z := by simp [Complex.sqrt]
  have H := (hasSum_even_binomial a (Complex.sqrt z) hw).div_const (Gamma (1 / 2))
  rw [hsq] at H
  rw [regularizedHGFun, FormalMultilinearSeries.sum]
  rw [show ((Complex.sqrt z + 1) ^ (-2 * a) / 2 + (1 - Complex.sqrt z) ^ (-2 * a) / 2)
      = ((1 + Complex.sqrt z) ^ (-(2 * a)) / 2 + (1 - Complex.sqrt z) ^ (-(2 * a)) / 2) by
    rw [add_comm (Complex.sqrt z) 1, neg_mul]]
  refine (H.congr_fun fun k => ?_).tsum_eq
  rw [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    regularizedHGFunCoeff_quadratic, smul_eq_mul, div_mul_eq_mul_div]

/-- **The requested identity** for the non-regularized function: for `‖z‖ < 1`,
`₂F₁(a, a + 1/2; 1/2; z) = (√z + 1)^(-2a) / 2 + (1 - √z)^(-2a) / 2`.

Multiplying the regularized function by `Γ(1/2)` cancels the factor `1 / Γ(1/2)` of
`Complex.regularized2F1_2`, so this is exactly the classical quadratic transformation. -/
theorem HGFun2F1_2 {a z : ℂ} (hz : ‖z‖ < 1) :
    HGFun {a, a + 1 / 2} {1 / 2} z =
      (Complex.sqrt z + 1) ^ (-2 * a) / 2 + (1 - Complex.sqrt z) ^ (-2 * a) / 2 := by
  have hG : Gamma ((1 : ℂ) / 2) ≠ 0 := Gamma_one_half_ne_zero
  rw [HGFun_def, regularized2F1_2 hz]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  field_simp

/-- The identity without the factor `1 / Γ(1/2)` is false: `regularizedHGFun` is the
*regularized* hypergeometric function.  Already at `a = 0`, `z = 0` the left-hand side is
`1 / Γ(1/2) = 1 / √π`, whereas the right-hand side is `1`. -/
theorem not_regularized2F1_2 :
    ¬ ∀ a z : ℂ, regularizedHGFun {a, a + 1 / 2} {1 / 2} z =
      (Complex.sqrt z + 1) ^ (-2 * a) / 2 + (1 - Complex.sqrt z) ^ (-2 * a) / 2 := by
  intro h
  have h1 := h 0 0
  have h2 := regularized2F1_2 (a := 0) (z := 0) (by norm_num)
  rw [h1] at h2
  have hs : Complex.sqrt (0 : ℂ) = 0 := by simp [Complex.sqrt]
  rw [hs] at h2
  norm_num at h2
  -- `h2 : Gamma (1/2) = 1`, i.e. `√π = 1`
  rw [Complex.Gamma_one_half_eq] at h2
  have h3 : ((Real.pi : ℂ) ^ ((1 : ℂ) / 2)) ^ 2 = (Real.pi : ℂ) := by
    rw [show ((1 : ℂ) / 2) = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
    exact Complex.cpow_nat_inv_pow _ two_ne_zero
  rw [h2] at h3
  norm_num at h3
  have h4 : (1 : ℝ) = Real.pi := by exact_mod_cast h3
  linarith [Real.pi_gt_three]

end Complex

/-
The statement as originally requested is not provable as stated, for two reasons: the series
defining the left-hand side converges only for `‖z‖ < 1`, and the *regularized* hypergeometric
function differs from the classical one by the factor `1 / Γ(1/2) = 1 / √π`; see
`Complex.not_regularized2F1_2`.  The corrected version is `Complex.regularized2F1_2` above.
For the non-regularized function `Complex.HGFun` the factor `1 / Γ(1/2)` disappears, so the
requested right-hand side is correct as written; see `Complex.HGFun2F1_2` (which still needs
the convergence hypothesis `‖z‖ < 1`).

theorem Complex.regularized2F1_2 {a z : ℂ} :
    regularizedHGFun {a, a + 1 / 2} {1 / 2} z =
      (Complex.sqrt z + 1) ^ (-2 * a) / 2 + (1 - Complex.sqrt z) ^ (-2 * a) / 2 := by
  sorry
-/
