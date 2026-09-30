import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.PSeries

/-!
# Power-law tails: `∑_{j ≥ 0} (j + c)^α` for `α < -1`

Two-sided bounds by telescoping (no integrals): with `β = α + 1 < 0` and
`F x = x^β / (-β)`, Bernoulli's inequality for non-positive exponents gives

* `x^α ≥ F x - F (x+1)`         ⇒ `∑ (j+c)^α ≥ F c`,
* `(x+1)^α ≤ F x - F (x+1)`     ⇒ `∑ (j+c)^α ≤ c^α + F c`.

See `docs/interval/08-series.md §3–4`.
-/

namespace Lynth.Interval.Series

open Finset

/-- Bernoulli's inequality for exponents `β ≤ 0`: `(1+s)^β ≥ 1 + β s` for `s > -1`. -/
theorem one_add_mul_le_rpow_of_nonpos {s : ℝ} (hs : -1 < s) {β : ℝ} (hβ : β ≤ 0) :
    1 + β * s ≤ (1 + s) ^ β := by
  have h1s : 0 < 1 + s := by linarith
  set q := -β with hq
  have hq0 : 0 ≤ q := by linarith
  have hpow : (1 + s) ^ β = ((1 + s) ^ q)⁻¹ := by
    rw [hq, Real.rpow_neg h1s.le, inv_inv]
  rw [hpow]
  rcases le_total q 1 with hq1 | hq1
  · -- concave Bernoulli: (1+s)^q ≤ 1 + q s
    have hb := rpow_one_add_le_one_add_mul_self (by linarith : -1 ≤ s) hq0 hq1
    have hpos : 0 < (1 + s) ^ q := Real.rpow_pos_of_pos h1s q
    have hqs : 0 < 1 + q * s := lt_of_lt_of_le hpos hb
    calc 1 + β * s = 1 - q * s := by rw [hq]; ring
      _ ≤ (1 + q * s)⁻¹ := by
          rw [← one_div, le_div_iff₀ hqs]
          nlinarith [sq_nonneg (q * s)]
      _ ≤ ((1 + s) ^ q)⁻¹ := inv_anti₀ hpos hb
  · -- q ≥ 1: apply convex Bernoulli to t = 1/(1+s) - 1
    by_cases hneg : 1 + β * s ≤ 0
    · exact le_trans hneg (inv_nonneg.2 (Real.rpow_nonneg h1s.le _))
    push Not at hneg
    set t := 1 / (1 + s) - 1
    have ht : -1 ≤ t := by
      have : 0 < 1 / (1 + s) := by positivity
      linarith
    have hb := one_add_mul_self_le_rpow_one_add ht hq1
    have h1t : 1 + t = (1 + s)⁻¹ := by simp [t, one_div]
    rw [h1t, Real.inv_rpow h1s.le] at hb
    calc 1 + β * s = 1 - q * s := by rw [hq]; ring
      _ ≤ 1 + q * t := by
          simp only [t]
          have : q * s ≥ q * (1 - 1 / (1 + s)) := by
            have hx : s ≥ 1 - 1 / (1 + s) := by
              have : 1 - s ≤ 1 / (1 + s) := by
                rw [le_div_iff₀ h1s]; nlinarith [sq_nonneg s]
              linarith
            exact mul_le_mul_of_nonneg_left hx hq0
          linarith
      _ ≤ _ := hb

/-- `F x = x^(α+1) / (-(α+1))` -/
noncomputable def tailF (α x : ℝ) : ℝ := x ^ (α + 1) / (-(α + 1))

theorem tailF_nonneg {α x : ℝ} (hα : α < -1) (hx : 0 ≤ x) : 0 ≤ tailF α x :=
  div_nonneg (Real.rpow_nonneg hx _) (by linarith)

/-- `x^α ≥ F x - F (x+1)` -/
theorem rpow_ge_tailF_sub {α x : ℝ} (hα : α < -1) (hx : 0 < x) :
    tailF α x - tailF α (x + 1) ≤ x ^ α := by
  have hβ : α + 1 < 0 := by linarith
  have hx0 : 0 < 1 / x := by positivity
  have hb := one_add_mul_le_rpow_of_nonpos (s := 1 / x) (by linarith) hβ.le
  -- (x+1)^β = x^β (1 + 1/x)^β
  have e1 : (x + 1) ^ (α + 1) = x ^ (α + 1) * (1 + 1 / x) ^ (α + 1) := by
    rw [← Real.mul_rpow hx.le (by positivity)]; congr 1; field_simp
  have e2 : x ^ (α + 1) = x ^ α * x := by rw [Real.rpow_add hx, Real.rpow_one]
  have hxb : 0 < x ^ (α + 1) := Real.rpow_pos_of_pos hx _
  unfold tailF
  rw [div_sub_div_same, div_le_iff₀ (by linarith), e1]
  have : x ^ (α + 1) * (1 + (α + 1) * (1 / x)) ≤ x ^ (α + 1) * (1 + 1 / x) ^ (α + 1) :=
    mul_le_mul_of_nonneg_left hb hxb.le
  have e3 : x ^ (α + 1) * (1 + (α + 1) * (1 / x)) = x ^ (α + 1) + (α + 1) * x ^ α := by
    rw [e2]; field_simp
  nlinarith

/-- `(x+1)^α ≤ F x - F (x+1)` -/
theorem rpow_succ_le_tailF_sub {α x : ℝ} (hα : α < -1) (hx : 0 < x) :
    (x + 1) ^ α ≤ tailF α x - tailF α (x + 1) := by
  have hβ : α + 1 < 0 := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hlt : 1 / (x + 1) < 1 := by rw [div_lt_one hx1]; linarith
  have hb := one_add_mul_le_rpow_of_nonpos (s := -(1 / (x + 1))) (by linarith) hβ.le
  have hnn : (0 : ℝ) ≤ 1 + -(1 / (x + 1)) := by linarith
  have e1 : x ^ (α + 1) = (x + 1) ^ (α + 1) * (1 + -(1 / (x + 1))) ^ (α + 1) := by
    have hx' : (x + 1) * (1 + -(1 / (x + 1))) = x := by field_simp; ring
    rw [← Real.mul_rpow hx1.le hnn, hx']
  have e2 : (x + 1) ^ (α + 1) = (x + 1) ^ α * (x + 1) := by rw [Real.rpow_add hx1, Real.rpow_one]
  have hxb : 0 < (x + 1) ^ (α + 1) := Real.rpow_pos_of_pos hx1 _
  unfold tailF
  rw [div_sub_div_same, le_div_iff₀ (by linarith), e1]
  have : (x + 1) ^ (α + 1) * (1 + (α + 1) * -(1 / (x + 1))) ≤
      (x + 1) ^ (α + 1) * (1 + -(1 / (x + 1))) ^ (α + 1) :=
    mul_le_mul_of_nonneg_left hb hxb.le
  have e3 : (x + 1) ^ (α + 1) * (1 + (α + 1) * -(1 / (x + 1))) =
      (x + 1) ^ (α + 1) - (α + 1) * (x + 1) ^ α := by
    rw [e2]; field_simp; ring
  nlinarith

/-- Summability and two-sided bounds for `∑_{j≥0} (j + c)^α`, `α < -1`, `c > 0`. -/
theorem powTail {α c : ℝ} (hα : α < -1) (hc : 0 < c) :
    Summable (fun j : ℕ => ((j : ℝ) + c) ^ α) ∧
      tailF α c ≤ ∑' j : ℕ, ((j : ℝ) + c) ^ α ∧
      ∑' j : ℕ, ((j : ℝ) + c) ^ α ≤ c ^ α + tailF α c := by
  set w : ℕ → ℝ := fun j => ((j : ℝ) + c) ^ α
  have hw0 : ∀ j, 0 ≤ w j := fun j => Real.rpow_nonneg (by positivity) _
  have hjc : ∀ j : ℕ, 0 < (j : ℝ) + c := fun j => by positivity
  -- upper bound on partial sums
  have hup : ∀ n, ∑ j ∈ range n, w j ≤ c ^ α + tailF α c := by
    intro n
    cases n with
    | zero => simp; exact add_nonneg (Real.rpow_nonneg hc.le _) (tailF_nonneg hα hc.le)
    | succ n =>
      rw [sum_range_succ']
      have hstep : ∀ j ∈ range n, w (j + 1) ≤ tailF α ((j : ℝ) + c) - tailF α ((j : ℝ) + 1 + c) := by
        intro j _
        have := rpow_succ_le_tailF_sub hα (hjc j)
        simp only [w]; push_cast
        rw [show (j : ℝ) + 1 + c = (j : ℝ) + c + 1 by ring]
        exact this
      have hsum := sum_le_sum hstep
      have htel : ∑ j ∈ range n, (tailF α ((j : ℝ) + c) - tailF α ((j : ℝ) + 1 + c)) =
          tailF α c - tailF α ((n : ℝ) + c) := by
        have := Finset.sum_range_sub' (fun j : ℕ => tailF α ((j : ℝ) + c)) n
        simpa [add_comm, add_left_comm, add_assoc] using this
      have hF := tailF_nonneg hα (hjc n).le
      simp only [w, Nat.cast_zero, zero_add] at hsum ⊢
      rw [htel] at hsum
      linarith
  have hsum : Summable w := summable_of_sum_range_le hw0 hup
  refine ⟨hsum, ?_, Real.tsum_le_of_sum_range_le hw0 hup⟩
  -- lower bound: partial sums ≥ F c - F (c + n) → F c
  have hlow : ∀ n : ℕ, tailF α c - tailF α ((n : ℝ) + c) ≤ ∑' j, w j := by
    intro n
    refine le_trans ?_ (hsum.sum_le_tsum (range n) (fun j _ => hw0 j))
    have hstep : ∀ j ∈ range n, tailF α ((j : ℝ) + c) - tailF α ((j : ℝ) + 1 + c) ≤ w j := by
      intro j _
      have := rpow_ge_tailF_sub hα (hjc j)
      rw [show (j : ℝ) + 1 + c = (j : ℝ) + c + 1 by ring]
      exact this
    have htel : ∑ j ∈ range n, (tailF α ((j : ℝ) + c) - tailF α ((j : ℝ) + 1 + c)) =
        tailF α c - tailF α ((n : ℝ) + c) := by
      have := Finset.sum_range_sub' (fun j : ℕ => tailF α ((j : ℝ) + c)) n
      simpa [add_comm, add_left_comm, add_assoc] using this
    rw [← htel]; exact sum_le_sum hstep
  -- F (c + n) → 0
  have hlim : Filter.Tendsto (fun n : ℕ => tailF α c - tailF α ((n : ℝ) + c)) Filter.atTop
      (nhds (tailF α c)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + c) ^ (α + 1)) Filter.atTop (nhds 0) := by
      have := (tendsto_rpow_neg_atTop (y := -(α + 1)) (by linarith)).comp
        (Filter.tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop)
      simp only [neg_neg] at this
      exact this
    have h2 : Filter.Tendsto (fun n : ℕ => tailF α ((n : ℝ) + c)) Filter.atTop (nhds 0) := by
      have := h1.div_const (-(α + 1))
      simpa [tailF] using this
    simpa using (tendsto_const_nhds (x := tailF α c)).sub h2
  exact le_of_tendsto' hlim hlow

end Lynth.Interval.Series
