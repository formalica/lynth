import Lynth.Interval.Series.Atanh
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The arctangent series and `π` (Machin)

`arctan z = Σ (-1)^k z^(2k+1)/(2k+1)` for `|z| < 1` (real version of
`Complex.hasSum_arctan`), evaluated for `z ∈ Z`, `|Z| ≤ 1/2` (ratio `1/4`).
`π = 4 (4 arctan (1/5) - arctan (1/239))`
(`Real.four_mul_arctan_inv_5_sub_arctan_inv_239`).
-/

namespace Lynth.Interval

open Dy

theorem hasSum_arctan_real {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => (-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) (Real.arctan x) := by
  have h := Complex.hasSum_arctan (z := (x : ℂ)) (by simpa [Complex.norm_real] using hx)
  rw [← Complex.ofReal_arctan] at h
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  funext n
  push_cast
  ring

def arctanStep (w : Nat) (Z2 : Ival) (k : Nat) (T : Ival) : Ival :=
  Ival.divNat w (Ival.mul w (Ival.mul w (Ival.neg T) Z2) (Ival.pt (Dy.ofNat (2 * k + 1)))) (2 * k + 3)

/-- enclosure of `arctan z` for `z ∈ Z`, `|Z| ≤ 1/2` (else `[-2, 2]`) -/
def arctanSeries (w : Nat) (Z : Ival) : Ival :=
  if smallHalf Z then
    (serLoop w (arctanStep w (Ival.sq w Z)) (smallT w) (w + 16) (SerState.start Z)).encl w (Dy.ofNat 2)
  else ⟨some (Dy.ofInt (-2)), some (Dy.ofInt 2)⟩

theorem abs_arctan_le_two (x : ℝ) : |Real.arctan x| ≤ 2 := by
  have h1 := Real.arctan_lt_pi_div_two x
  have h2 := Real.neg_pi_div_two_lt_arctan x
  have := Real.pi_lt_d2
  rw [abs_le]; constructor <;> linarith

theorem mem_arctanSeries (w : Nat) {Z : Ival} {z : ℝ} (hz : z ∈ Z) :
    Real.arctan z ∈ arctanSeries w Z := by
  unfold arctanSeries
  split
  · rename_i h
    have hz2 := abs_le_half_of_smallHalf h hz
    have hlt : |z| < 1 := by linarith
    set t : ℕ → ℝ := fun n => (-1) ^ n * z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) with ht
    have hsq : z ^ 2 ∈ Ival.sq w Z := Ival.mem_sq hz
    have hrec : ∀ k, t (k + 1) = -t k * z ^ 2 * ((2 * k + 1 : ℕ) : ℝ) / ((2 * k + 3 : ℕ) : ℝ) := by
      intro k
      simp only [ht]; push_cast
      have h1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
      have h3 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, pow_succ (-1 : ℝ) k]
      push_cast
      field_simp
      ring
    have hstep : ∀ k X, t k ∈ X → t (k + 1) ∈ arctanStep w (Ival.sq w Z) k X := by
      intro k X hX
      rw [hrec]
      have := Ival.mem_mul (p := w) (Ival.mem_mul (p := w) (Ival.mem_neg hX) hsq)
        (Ival.mem_pt_nat (2 * k + 1))
      exact Ival.mem_divNat (n := 2 * k + 3) this (by omega)
    have h0 : t 0 ∈ Z := by simpa [ht] using hz
    have hinv := serLoop_inv (p := w) (small := smallT w) hstep (w + 16) _ (SerState.start_inv h0)
    refine SerState.mem_encl (hasSum_arctan_real hlt) hinv (q := 1 / 4)
      (by norm_num) (by norm_num) ?_ (by simp [toReal_def]; norm_num)
    intro k _
    show |t (k + 1)| ≤ 1 / 4 * |t k|
    rw [hrec]
    have hr0 : 0 ≤ (((2 * k + 1 : ℕ) : ℝ) / ((2 * k + 3 : ℕ) : ℝ)) := by positivity
    have hr : (((2 * k + 1 : ℕ) : ℝ) / ((2 * k + 3 : ℕ) : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; push_cast; linarith
    have hz2' : z ^ 2 ≤ 1 / 4 := by have := sq_abs z; nlinarith [abs_nonneg z]
    rw [mul_div_assoc, abs_mul, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg z), abs_of_nonneg hr0,
      mul_assoc, mul_comm (1 / 4 : ℝ)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    nlinarith [sq_nonneg z]
  · have := abs_arctan_le_two z
    refine ⟨by simp [toReal_def]; linarith [(abs_le.1 this).1], by simp [toReal_def]; linarith [(abs_le.1 this).2]⟩

/-- `π` to precision `p` by Machin's formula -/
def piSeries (p : Nat) : Ival :=
  let w := p + 10
  let a := arctanSeries w (Ival.ofRat w (1 / 5))
  let b := arctanSeries w (Ival.ofRat w (1 / 239))
  Ival.mul w (Ival.pt (Dy.ofNat 4)) (Ival.sub w (Ival.mul w (Ival.pt (Dy.ofNat 4)) a) b)

theorem mem_piSeries (p : Nat) : Real.pi ∈ piSeries p := by
  have ha := mem_arctanSeries (p + 10) (Ival.mem_ofRat (p + 10) (1 / 5))
  have hb := mem_arctanSeries (p + 10) (Ival.mem_ofRat (p + 10) (1 / 239))
  have e : Real.pi = 4 * (4 * Real.arctan ((1 / 5 : ℚ) : ℝ) - Real.arctan ((1 / 239 : ℚ) : ℝ)) := by
    have := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    push_cast
    rw [one_div, one_div]; linarith
  rw [e]
  exact Ival.mem_mul (Ival.mem_pt_nat 4) (Ival.mem_sub (Ival.mem_mul (Ival.mem_pt_nat 4) ha) hb)

end Lynth.Interval
