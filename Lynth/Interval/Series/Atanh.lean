import Lynth.Interval.Series.Tail
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The `atanh`-type logarithm series

`log (1 + z) - log (1 - z) = 2 Σ z^(2k+1)/(2k+1)` for `|z| < 1`
(`Real.hasSum_log_sub_log_of_abs_lt_one`), evaluated for `z ∈ Z`, `|Z| ≤ 1/2`,
with ratio `q = 1/4`.  Used by `log` and by `log 2 = log(4/3) - log(2/3)`.
-/

namespace Lynth.Interval

open Dy

def quarterHalf : Dy := ⟨1, -1⟩
def negQuarterHalf : Dy := ⟨-1, -1⟩

/-- `Z ⊆ [-1/2, 1/2]` -/
def smallHalf (Z : Ival) : Bool :=
  match Z.lo, Z.hi with
  | some a, some b => Dy.leB negQuarterHalf a && Dy.leB b quarterHalf
  | _, _ => false

theorem abs_le_half_of_smallHalf {Z : Ival} (h : smallHalf Z = true) {z : ℝ} (hz : z ∈ Z) :
    |z| ≤ 1 / 2 := by
  unfold smallHalf at h
  split at h
  · rename_i a b ha hb
    simp only [Bool.and_eq_true] at h
    have h1 := toReal_le_of_leB h.1; have h2 := toReal_le_of_leB h.2
    have hz1 := hz.1 a ha; have hz2 := hz.2 b hb
    simp [negQuarterHalf, quarterHalf, toReal_def] at h1 h2
    simp only [toReal_def] at hz1 hz2
    rw [abs_le]; constructor <;> linarith
  · simp at h

/-- the (vanishing-precision) test for small terms -/
def smallT (w : Nat) (T : Ival) : Bool :=
  match Ival.magHi T with
  | some m => Dy.ltB m ⟨1, -(w : Int)⟩
  | none => false

def atanhStep (w : Nat) (Z2 : Ival) (k : Nat) (T : Ival) : Ival :=
  Ival.divNat w (Ival.mul w (Ival.mul w T Z2) (Ival.pt (Dy.ofNat (2 * k + 1)))) (2 * k + 3)

/-- enclosure of `log (1 + z) - log (1 - z)` for `z ∈ Z` -/
def atanh2Series (w : Nat) (Z : Ival) : Ival :=
  if smallHalf Z then
    let Z2 := Ival.sq w Z
    let T0 := Ival.mul w (Ival.pt (Dy.ofNat 2)) Z
    (serLoop w (atanhStep w Z2) (smallT w) (w + 16) (SerState.start T0)).encl w (Dy.ofNat 2)
  else Ival.top

theorem mem_atanh2Series (w : Nat) {Z : Ival} {z : ℝ} (hz : z ∈ Z) :
    Real.log (1 + z) - Real.log (1 - z) ∈ atanh2Series w Z := by
  unfold atanh2Series
  split
  · rename_i h
    have hz2 := abs_le_half_of_smallHalf h hz
    have hlt : |z| < 1 := by linarith
    set t : ℕ → ℝ := fun k => (2 : ℝ) * (1 / (2 * k + 1)) * z ^ (2 * k + 1) with ht
    have hsq : z ^ 2 ∈ Ival.sq w Z := Ival.mem_sq hz
    have hstep : ∀ k X, t k ∈ X → t (k + 1) ∈ atanhStep w (Ival.sq w Z) k X := by
      intro k X hX
      have e : t (k + 1) = t k * z ^ 2 * ((2 * k + 1 : ℕ) : ℝ) / ((2 * k + 3 : ℕ) : ℝ) := by
        simp only [ht]; push_cast
        have h1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
        have h2 : (2 * ((k : ℝ) + 1) + 1) ≠ 0 := by positivity
        have h3 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
        rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring]
        field_simp
        ring
      rw [e]
      have := Ival.mem_mul (p := w) (Ival.mem_mul (p := w) hX hsq) (Ival.mem_pt_nat (2 * k + 1))
      exact Ival.mem_divNat (n := 2 * k + 3) this (by omega)
    have h0 : t 0 ∈ Ival.mul w (Ival.pt (Dy.ofNat 2)) Z := by
      have := Ival.mem_mul (p := w) (Ival.mem_pt_nat 2) hz
      simpa [ht] using this
    have hinv := serLoop_inv (p := w) (small := smallT w) hstep (w + 16) _ (SerState.start_inv h0)
    refine SerState.mem_encl (Real.hasSum_log_sub_log_of_abs_lt_one hlt) hinv (q := 1 / 4)
      (by norm_num) (by norm_num) ?_ (by simp [toReal_def]; norm_num)
    intro k _
    have e : t (k + 1) = t k * (z ^ 2 * (((2 * k + 1 : ℕ) : ℝ) / ((2 * k + 3 : ℕ) : ℝ))) := by
      simp only [ht]; push_cast
      have h1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
      have h3 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring]
      field_simp
      ring
    show |t (k + 1)| ≤ 1 / 4 * |t k|
    rw [e, abs_mul, mul_comm (1 / 4 : ℝ)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hr : (((2 * k + 1 : ℕ) : ℝ) / ((2 * k + 3 : ℕ) : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; push_cast; linarith
    have hr0 : 0 ≤ (((2 * k + 1 : ℕ) : ℝ) / ((2 * k + 3 : ℕ) : ℝ)) := by positivity
    have hz2' : z ^ 2 ≤ 1 / 4 := by
      have := sq_abs z; nlinarith [abs_nonneg z]
    rw [abs_mul, abs_of_nonneg (sq_nonneg z), abs_of_nonneg hr0]
    nlinarith [sq_nonneg z]
  · exact Ival.mem_top _

/-- `log t = log (1 + z) - log (1 - z)` for `z = (t - 1)/(t + 1)`, `t > 0` -/
theorem log_eq_atanh2 {t : ℝ} (ht : 0 < t) :
    Real.log t = Real.log (1 + (t - 1) / (t + 1)) - Real.log (1 - (t - 1) / (t + 1)) := by
  have h1 : 1 + (t - 1) / (t + 1) = 2 * t / (t + 1) := by field_simp; ring
  have h2 : 1 - (t - 1) / (t + 1) = 2 / (t + 1) := by field_simp; ring
  rw [h1, h2, ← Real.log_div (by positivity) (by positivity)]
  congr 1; field_simp

/-- series enclosure of `log 2` -/
def ln2Series (p : Nat) : Ival := atanh2Series (p + 8) (Ival.ofRat (p + 8) (1 / 3))

theorem mem_ln2Series (p : Nat) : Real.log 2 ∈ ln2Series p := by
  have := mem_atanh2Series (p + 8) (Ival.mem_ofRat (p + 8) (1 / 3))
  have e : Real.log 2 = Real.log (1 + ((1 / 3 : ℚ) : ℝ)) - Real.log (1 - ((1 / 3 : ℚ) : ℝ)) := by
    rw [log_eq_atanh2 (by norm_num : (0 : ℝ) < 2)]; norm_num
  rw [e]; exact this

end Lynth.Interval
