import Mathlib
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Lynth.HGIdentities.Common
import Lynth.Hypergeometric

/-!
# `₀F₁(; b; z) = z^{(1-b)/2} I_{b-1}(2 √z) Γ(b)`

Mathlib does not contain the Bessel functions, so the modified Bessel function of the first
kind is defined here by its classical series (DLMF 10.25.2)
$$ I_\nu(w) = (w/2)^\nu \sum_{k\ge 0} \frac{(w^2/4)^k}{k!\,\Gamma(\nu + k + 1)} , $$
the power `(w/2)^ν` being the principal branch.

## Main results

* `Complex.besselI_zero`, `Complex.besselI_natCast` : for integer order the definition reduces
  to the familiar series `I_n(w) = (w/2)^n ∑ₖ (w²/4)^k / (k! (n+k)!)`;
* `Complex.HGFun0F1_besselI` : `₀F₁(; b; z) = z^{1/2 - b/2} I_{b-1}(2√z) Γ(b)` for `z ≠ 0`.
-/

open scoped Nat

namespace Complex

/-- The modified Bessel function of the first kind, defined by its classical series. -/
noncomputable def besselI (ν w : ℂ) : ℂ :=
  (w / 2) ^ ν * ∑' k : ℕ, (w ^ 2 / 4) ^ k / ((k ! : ℂ) * Gamma (ν + k + 1))

/-- For order `0` the definition is the classical series `I₀(w) = ∑ₖ (w²/4)^k / (k!)²`. -/
theorem besselI_zero (w : ℂ) :
    besselI 0 w = ∑' k : ℕ, (w ^ 2 / 4) ^ k / ((k ! : ℂ) * (k ! : ℂ)) := by
  rw [besselI, cpow_zero, one_mul]
  refine tsum_congr fun k => ?_
  rw [show (0 : ℂ) + k + 1 = (k : ℂ) + 1 by ring, Gamma_nat_eq_factorial]

/-- For integer order the definition is the classical series
`I_n(w) = (w/2)^n ∑ₖ (w²/4)^k / (k! (n+k)!)`. -/
theorem besselI_natCast (n : ℕ) (w : ℂ) :
    besselI n w = (w / 2) ^ n * ∑' k : ℕ, (w ^ 2 / 4) ^ k / ((k ! : ℂ) * ((n + k)! : ℂ)) := by
  rw [besselI, cpow_natCast]
  refine congrArg _ (tsum_congr fun k => ?_)
  rw [show (n : ℂ) + k + 1 = ((n + k : ℕ) : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]

/-- The principal square root satisfies `(√z)^c = z^(c/2)`. -/
private theorem sqrt_cpow (z c : ℂ) : (Complex.sqrt z) ^ c = z ^ (c / 2) := by
  have harg : (Complex.log z * 2⁻¹).im = Complex.arg z / 2 := by
    simp only [Complex.mul_im, Complex.log_im, Complex.log_re, Complex.inv_im, Complex.inv_re]
    norm_num
    ring
  have h1 : -Real.pi < (Complex.log z * 2⁻¹).im := by
    rw [harg]
    have := Complex.neg_pi_lt_arg z
    have := Real.pi_pos
    linarith
  have h2 : (Complex.log z * 2⁻¹).im ≤ Real.pi := by
    rw [harg]
    have := Complex.arg_le_pi z
    have := Real.pi_pos
    linarith
  rw [show c / 2 = 2⁻¹ * c by ring, Complex.cpow_mul _ h1 h2]
  rfl

/-- The `₀F₁` series in terms of the Gamma function. -/
private theorem HGFun0F1_eq (b z : ℂ) :
    HGFun {} {b} z = Gamma b * ∑' n : ℕ, z ^ n / ((n ! : ℂ) * Gamma (b + n)) := by
  rw [HGFun_eq_tsum, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [HGFunCoeff_def, regularizedHGFunCoeff]
  simp only [Multiset.empty_eq_zero, Multiset.map_zero, Multiset.prod_zero,
    Multiset.map_singleton, Multiset.prod_singleton]
  ring

/-- `I_{b-1}(2√z)` in terms of the `₀F₁` series. -/
private theorem besselI_two_sqrt (b z : ℂ) :
    besselI (b - 1) (2 * Complex.sqrt z)
      = z ^ ((b - 1) / 2) * ∑' n : ℕ, z ^ n / ((n ! : ℂ) * Gamma (b + n)) := by
  have hsq : Complex.sqrt z ^ 2 = z := sqrt_sq_eq z
  rw [besselI, show 2 * Complex.sqrt z / 2 = Complex.sqrt z by ring,
    show (2 * Complex.sqrt z) ^ 2 / 4 = z by rw [mul_pow, hsq]; ring, sqrt_cpow z _]
  refine congrArg _ (tsum_congr fun n => ?_)
  rw [show b - 1 + (n : ℂ) + 1 = b + n by ring]

/-- **The requested identity**: `₀F₁(; b; z) = z^{1/2 - b/2} I_{b-1}(2√z) Γ(b)`, for `z ≠ 0`. -/
theorem HGFun0F1_besselI {b z : ℂ} (hz : z ≠ 0) :
    HGFun {} {b} z = z ^ (1 / 2 - b / 2) * besselI (b - 1) (2 * Complex.sqrt z) * Gamma b := by
  rw [besselI_two_sqrt b z, HGFun0F1_eq, ← mul_assoc, ← Complex.cpow_add _ _ hz,
    show 1 / 2 - b / 2 + (b - 1) / 2 = 0 by ring, cpow_zero, one_mul]
  ring

/-- The regularized version: the regularized function is the classical one divided by `Γ(b)`,
so the Gamma factor disappears. -/
theorem regularized0F1_besselI {b z : ℂ} (hz : z ≠ 0) (hb : ∀ m : ℕ, b ≠ -m) :
    regularizedHGFun {} {b} z = z ^ (1 / 2 - b / 2) * besselI (b - 1) (2 * Complex.sqrt z) := by
  have hG : ((({b} : Multiset ℂ)).map Gamma).prod ≠ 0 := by
    simpa using Gamma_ne_zero hb
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero hb
  rw [regularizedHGFun_eq_HGFun_div hG, HGFun0F1_besselI hz]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  rw [mul_div_assoc, div_self hGb, mul_one]

end Complex
