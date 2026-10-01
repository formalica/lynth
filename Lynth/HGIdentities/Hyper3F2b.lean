import Mathlib
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Lynth.HGIdentities.Common
import Lynth.Hypergeometric
import Lynth.ComplexFuncs

/-!
# `₃F₂(-1/2, 1, 1; 1/2, 2; z) = -2√z artanh(√z)/3 + 2/3 - log(1-z)/(3z)`

The coefficients of this series are
`(-1/2)ₙ (1)ₙ (1)ₙ / (n! (1/2)ₙ (2)ₙ) = (-1/2)ₙ / ((1/2)ₙ (n+1)) = -1/((2n-1)(n+1))`,
and the partial fraction decomposition
`-1/((2n-1)(n+1)) = -2/(3(2n-1)) + 1/(3(n+1))`
reduces the identity to the two series already available in this project:
`∑ₙ zⁿ/(2n+1) = artanh(√z)/√z` (`Complex.HGFun2F1_atanh`) and
`∑ₙ zⁿ/(n+1) = -log(1-z)/z` (`Complex.hasSum_neg_log_div`).

## Main results

* `Complex.HGFun3F2_1` : the identity, for `0 < ‖z‖ < 1`;
* `Complex.regularized3F2_1` : the regularized version (extra factor `1/Γ(1/2)`);
* `Complex.not_HGFun3F2_1_at_zero` : the hypothesis `z ≠ 0` cannot be dropped.
-/

open scoped Nat

namespace Complex

/-- `2n - 1 ≠ 0` for a natural number `n`. -/
private theorem two_mul_sub_one_ne_zero (n : ℕ) : (2 * (n : ℂ) - 1) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.zero_re] at hre
  have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (n : ℝ) ≠ 1 / 2 := by
    intro hn
    have : ((2 * n : ℕ) : ℝ) = 1 := by push_cast; linarith
    have h2 : (2 * n : ℕ) = 1 := by exact_mod_cast this
    omega
  apply h1
  linarith

/-- `(2n-1) (-1/2)ₙ = -(1/2)ₙ`. -/
private theorem two_mul_sub_one_mul_ascPochhammer_neg_half (n : ℕ) :
    (2 * (n : ℂ) - 1) * (ascPochhammer ℂ n).eval (-1 / 2)
      = -(ascPochhammer ℂ n).eval (1 / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
      push_cast
      linear_combination ((n : ℂ) + 1 / 2) * ih

/-- `(2)ₙ = (n+1)!`. -/
private theorem ascPochhammer_eval_two (n : ℕ) :
    (ascPochhammer ℂ n).eval 2 = ((n + 1)! : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_eval, ih, Nat.factorial_succ (n + 1)]
      push_cast
      ring

private theorem half_two_not_nonpos_int : ∀ j ∈ ({1 / 2, 2} : Multiset ℂ), ∀ m : ℕ, j ≠ -(m : ℂ) := by
  intro j hj m
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hj
  rcases hj with rfl | rfl <;> intro h <;>
    · have hre := congrArg Complex.re h
      simp only [Complex.div_re, Complex.neg_re, Complex.natCast_re, Complex.re_ofNat] at hre
      norm_num at hre
      linarith

/-- The coefficients of `₃F₂(-1/2, 1, 1; 1/2, 2; ·)` are `-1/((2n-1)(n+1))`. -/
private theorem HGFunCoeff_3F2_1 (n : ℕ) :
    HGFunCoeff {-1 / 2, 1, 1} {1 / 2, 2} n
      = -(1 / ((2 * (n : ℂ) - 1) * ((n : ℂ) + 1))) := by
  have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hhalf := ascPochhammer_half_ne_zero n
  have h2n := two_mul_sub_one_ne_zero n
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    have h := Nat.cast_ne_zero (R := ℂ) (n := n + 1) |>.mpr (Nat.succ_ne_zero n)
    simpa using h
  have hkey := two_mul_sub_one_mul_ascPochhammer_neg_half n
  rw [HGFunCoeff_eq_ascPochhammer _ half_two_not_nonpos_int n,
    show ({-1 / 2, 1, 1} : Multiset ℂ) = (-1 / 2 : ℂ) ::ₘ (1 : ℂ) ::ₘ {1} from rfl,
    show ({1 / 2, 2} : Multiset ℂ) = (1 / 2 : ℂ) ::ₘ {2} from rfl]
  simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, ascPochhammer_eval_one, ascPochhammer_eval_two]
  rw [show ((-1 : ℂ) / 2) = -(1 / 2) by norm_num] at hkey
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  linear_combination hkey

/-- The series `∑ₙ zⁿ/(2n+1)` sums to `artanh(√z)/√z`. -/
private theorem hasSum_atanh_series {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasSum (fun n : ℕ => (1 / (2 * (n : ℂ) + 1)) * z ^ n)
      (artanh (Complex.sqrt z) / Complex.sqrt z) := by
  have hw : ‖Complex.sqrt z‖ < 1 := norm_sqrt_lt_one hz
  have hw0 : Complex.sqrt z ≠ 0 := sqrt_ne_zero_of_ne_zero hz0
  have hsq : Complex.sqrt z ^ 2 = z := sqrt_sq_eq z
  have hkey := tsum_atanhCoeff_eq hw
  rw [hsq] at hkey
  have h := seriesOnDisc_atanhCoeff.hasSum hz
  rw [show (∑' n : ℕ, atanhCoeff n * z ^ n) = artanh (Complex.sqrt z) / Complex.sqrt z by
    rw [eq_div_iff hw0, mul_comm]; exact hkey] at h
  exact h

/-- The series `∑ₙ zⁿ/(2n-1)` sums to `-1 + √z artanh(√z)`. -/
private theorem hasSum_atanh_shift {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasSum (fun n : ℕ => (1 / (2 * (n : ℂ) - 1)) * z ^ n)
      (-1 + Complex.sqrt z * artanh (Complex.sqrt z)) := by
  have hw0 : Complex.sqrt z ≠ 0 := sqrt_ne_zero_of_ne_zero hz0
  have hsq : Complex.sqrt z ^ 2 = z := sqrt_sq_eq z
  have h := (hasSum_atanh_series hz hz0).mul_left z
  have hzz : z / Complex.sqrt z = Complex.sqrt z := by
    rw [div_eq_iff hw0, ← sq, hsq]
  have hval : z * (artanh (Complex.sqrt z) / Complex.sqrt z)
      = Complex.sqrt z * artanh (Complex.sqrt z) :=
    calc z * (artanh (Complex.sqrt z) / Complex.sqrt z)
        = (z / Complex.sqrt z) * artanh (Complex.sqrt z) := by ring
      _ = Complex.sqrt z * artanh (Complex.sqrt z) := by rw [hzz]
  rw [hval] at h
  have h' : HasSum (fun n : ℕ => (1 / (2 * ((n : ℂ) + 1) - 1)) * z ^ (n + 1))
      (Complex.sqrt z * artanh (Complex.sqrt z)) := by
    refine h.congr_fun fun n => ?_
    rw [show (2 : ℂ) * ((n : ℂ) + 1) - 1 = 2 * (n : ℂ) + 1 by ring]
    ring
  have h'' : HasSum (fun n : ℕ => (fun k : ℕ => (1 / (2 * (k : ℂ) - 1)) * z ^ k) (n + 1))
      (Complex.sqrt z * artanh (Complex.sqrt z)) := by
    refine h'.congr_fun fun n => ?_
    push_cast
    ring_nf
  have hfin := (hasSum_nat_add_iff (f := fun k : ℕ => (1 / (2 * (k : ℂ) - 1)) * z ^ k) 1).mp h''
  rw [Finset.sum_range_one] at hfin
  simpa [add_comm] using hfin

/-- **The requested identity**, on the punctured unit disc. -/
theorem HGFun3F2_1 {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HGFun {-1 / 2, 1, 1} {1 / 2, 2} z
      = -(2 * Complex.sqrt z * artanh (Complex.sqrt z) / 3) + 2 / 3
        - Complex.log (1 - z) / (3 * z) := by
  have hS1 := (hasSum_atanh_shift hz hz0).mul_left (-2 / 3)
  have hS2 := (hasSum_neg_log_div z hz hz0).mul_left (1 / 3)
  have hS := hS1.add hS2
  have hval : (-2 / 3) * (-1 + Complex.sqrt z * artanh (Complex.sqrt z))
      + (1 / 3) * (-(Complex.log (1 - z) / z))
      = -(2 * Complex.sqrt z * artanh (Complex.sqrt z) / 3) + 2 / 3
        - Complex.log (1 - z) / (3 * z) := by
    field_simp
    ring
  rw [hval] at hS
  refine (HGFun_eq_tsum _ _ _).trans ?_
  refine (hS.congr_fun fun n => ?_).tsum_eq
  have h2n := two_mul_sub_one_ne_zero n
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    have h := Nat.cast_ne_zero (R := ℂ) (n := n + 1) |>.mpr (Nat.succ_ne_zero n)
    simpa using h
  rw [HGFunCoeff_3F2_1]
  field_simp
  ring

/-- The regularized form of the identity: the regularized function carries the extra factor
`1/(Γ(1/2) Γ(2)) = 1/Γ(1/2)`. -/
theorem regularized3F2_1 {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    regularizedHGFun {-1 / 2, 1, 1} {1 / 2, 2} z
      = (-(2 * Complex.sqrt z * artanh (Complex.sqrt z) / 3) + 2 / 3
          - Complex.log (1 - z) / (3 * z)) / Gamma (1 / 2) := by
  have hGne : ((({1 / 2, 2} : Multiset ℂ)).map Gamma).prod ≠ 0 :=
    prod_map_Gamma_ne_zero half_two_not_nonpos_int
  rw [regularizedHGFun_eq_HGFun_div hGne, HGFun3F2_1 hz hz0,
    show ({1 / 2, 2} : Multiset ℂ) = (1 / 2 : ℂ) ::ₘ {2} from rfl]
  simp

/-- The hypothesis `z ≠ 0` is necessary: at `z = 0` the left-hand side is `1`, while the
right-hand side evaluates to `2/3` because `log 1 / 0 = 0` by convention. -/
theorem not_HGFun3F2_1_at_zero :
    ¬ ∀ z : ℂ, HGFun {-1 / 2, 1, 1} {1 / 2, 2} z
      = -(2 * Complex.sqrt z * artanh (Complex.sqrt z) / 3) + 2 / 3
        - Complex.log (1 - z) / (3 * z) := by
  intro h
  have h0 := h 0
  rw [HGFun_eq_tsum] at h0
  have hzero : (∑' n : ℕ, HGFunCoeff {-1 / 2, 1, 1} {1 / 2, 2} n * (0 : ℂ) ^ n) = 1 := by
    rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn]), HGFunCoeff_3F2_1]
    norm_num
  rw [hzero] at h0
  norm_num [Complex.sqrt] at h0

end Complex
