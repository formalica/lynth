import Lynth.Interval.Fns.EulerGamma.Proof.NumericalBounds
import Lynth.Interval.Fns.EulerGamma.Proof.CoefficientSeries

/-!
# A finite sum estimate for the coefficients `c_j`
-/

open Real Finset

namespace BM

lemma cc_mul_sqrt_succ_le (n : ℕ) : cc n * √((n : ℝ) + 1) ≤ 1 := by
  have h := cc_sq_le n
  have hc := cc_pos n
  have h1 : (cc n * √((n : ℝ) + 1)) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    calc cc n ^ 2 * ((n : ℝ) + 1) ≤ 1 / (3 * n + 1) * ((n : ℝ) + 1) := by gcongr
      _ ≤ 1 := by rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have h2 : 0 ≤ cc n * √((n : ℝ) + 1) := by positivity
  nlinarith

lemma sum_cc_le (n : ℕ) : ∑ k ∈ range n, cc k ≤ 2 * √(n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 := cc_mul_sqrt_succ_le n
    have hs1 : √(n : ℝ) ≤ √((n : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hs0 : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
    have hsq : √((n : ℝ) + 1) ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
    have hsq0 : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
    have hc := cc_pos n
    -- `cc n ≤ 2 (√(n+1) - √n)`
    have key : cc n ≤ 2 * (√((n : ℝ) + 1) - √(n : ℝ)) := by
      have hpos : 0 < √((n : ℝ) + 1) + √(n : ℝ) := by
        have : 0 < √((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
        linarith
      have e : 2 * (√((n : ℝ) + 1) - √(n : ℝ)) * (√((n : ℝ) + 1) + √(n : ℝ)) = 2 := by
        nlinarith
      have : cc n * (√((n : ℝ) + 1) + √(n : ℝ)) ≤ 2 := by nlinarith
      nlinarith
    push_cast
    linarith

lemma cc_sub_le (a : ℕ) : ∀ b : ℕ, a ≤ b → cc a - cc b ≤ (b - a) * (cc a / (2 * a + 2)) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [cc_succ]
    have hcb : cc b ≤ cc a := cc_antitone hab
    have hb : (a : ℝ) ≤ b := by exact_mod_cast hab
    have h1 : cc b / (2 * b + 2) ≤ cc a / (2 * a + 2) := by
      apply div_le_div₀ (cc_pos a).le hcb (by positivity) (by linarith)
    have : cc b - cc b * ((2 * b + 1) / (2 * b + 2)) = cc b / (2 * b + 2) := by
      field_simp; ring
    push_cast
    nlinarith

lemma Z2_sum_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ range n, (cc (n - 1 - i) - cc (n + i)) / ((i : ℝ) + 1 / 2) ≤ 4 / √(n : ℝ) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ i ∈ range n, (cc (n - 1 - i) - cc (n + i)) / ((i : ℝ) + 1 / 2)
      ≤ 2 / ((n : ℝ) + 1 / 2) * cc (n - 1 - i) := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hc := cc_pos (n - 1 - i)
    have hD := cc_sub_le (n - 1 - i) (n + i) (by omega)
    have hcast : ((n - 1 - i : ℕ) : ℝ) = n - 1 - i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [hcast] at hD
    push_cast at hD
    have hD0 : cc (n - 1 - i) - cc (n + i) ≤ cc (n - 1 - i) := by
      have := cc_pos (n + i); linarith
    have hi0 : (0 : ℝ) ≤ i := by positivity
    have hin : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi'
    rw [div_le_iff₀ (by positivity)]
    -- two cases according to which of `n - i`, `i + 1/2` is larger
    have h3 : 0 < (n : ℝ) + 1 / 2 := by positivity
    rcases le_total ((n : ℝ) - i) ((i : ℝ) + 1 / 2) with h | h
    · calc cc (n - 1 - i) - cc (n + i) ≤ cc (n - 1 - i) := hD0
        _ ≤ 2 / ((n : ℝ) + 1 / 2) * cc (n - 1 - i) * ((i : ℝ) + 1 / 2) := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ h3]
          have : (n : ℝ) + 1 / 2 ≤ 2 * ((i : ℝ) + 1 / 2) := by linarith
          have := mul_le_mul_of_nonneg_left this hc.le
          linarith
    · have e : ((n : ℝ) + i - (n - 1 - i)) * (cc (n - 1 - i) / (2 * (n - 1 - i) + 2))
          = (2 * i + 1) * cc (n - 1 - i) / (2 * ((n : ℝ) - i)) := by
        have : 2 * ((n : ℝ) - i) ≠ 0 := by
          have : (0:ℝ) < n - i := by linarith
          positivity
        field_simp; ring
      rw [e] at hD
      have hni : (0 : ℝ) < n - i := by linarith
      calc cc (n - 1 - i) - cc (n + i) ≤ (2 * i + 1) * cc (n - 1 - i) / (2 * ((n : ℝ) - i)) := hD
        _ ≤ 2 / ((n : ℝ) + 1 / 2) * cc (n - 1 - i) * ((i : ℝ) + 1 / 2) := by
          rw [div_le_iff₀ (by positivity)]
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ h3]
          have h4 : (n : ℝ) + 1 / 2 ≤ 2 * ((n : ℝ) - i) := by linarith
          have h5 : 0 ≤ (2 * (i : ℝ) + 1) * cc (n - 1 - i) := by positivity
          have := mul_le_mul_of_nonneg_left h4 h5
          nlinarith
  calc ∑ i ∈ range n, (cc (n - 1 - i) - cc (n + i)) / ((i : ℝ) + 1 / 2)
      ≤ ∑ i ∈ range n, 2 / ((n : ℝ) + 1 / 2) * cc (n - 1 - i) := Finset.sum_le_sum hterm
    _ = 2 / ((n : ℝ) + 1 / 2) * ∑ k ∈ range n, cc k := by
        rw [← Finset.mul_sum, Finset.sum_range_reflect (fun k => cc k) n]
    _ ≤ 2 / ((n : ℝ) + 1 / 2) * (2 * √(n : ℝ)) := by gcongr; exact sum_cc_le n
    _ ≤ 4 / √(n : ℝ) := by
        have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hN
        have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hN.le
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hs]
        nlinarith

end BM
