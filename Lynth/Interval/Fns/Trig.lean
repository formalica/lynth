import Lynth.Interval.Fns.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# sin, cos, tan, cot

Point kernels: Taylor series (`Real.hasSum_sin`, `Real.hasSum_cos`) for
`|y| ≤ 2` by term recurrences with ratio `q = 1/2` (valid from the second term).
Interval extension: reduction `y = x - kπ` (any integer `k` is sound;
`sin x = (-1)^k sin y`), then monotonicity of `sin` / evenness and
antitonicity of `cos` on `[-π/2, π/2]`; otherwise the Lipschitz enclosure
`sin m ± r` intersected with `[-1, 1]`.
See `docs/interval/04-functions.md §7–8`.
-/

namespace Lynth.Interval.Fns

open Lynth.Interval Dy

def two : Dy := ⟨2, 0⟩
def negTwo : Dy := ⟨-2, 0⟩

/-- `-2 ≤ y ≤ 2` -/
def isTrigArg (y : Dy) : Bool := Dy.leB y two && Dy.leB negTwo y

theorem abs_le_two_of_isTrigArg {y : Dy} (h : isTrigArg y = true) : |y.toReal| ≤ 2 := by
  simp only [isTrigArg, Bool.and_eq_true] at h
  have h1 := toReal_le_of_leB h.1; have h2 := toReal_le_of_leB h.2
  simp [two, negTwo, toReal_def] at h1 h2
  simp only [toReal_def]
  exact abs_le.2 ⟨h2, h1⟩

/-- the unit interval `[-1, 1]` -/
def unitIval : Ival := ⟨some (Dy.ofInt (-1)), some Dy.one⟩

theorem mem_unitIval {x : ℝ} (h1 : -1 ≤ x) (h2 : x ≤ 1) : x ∈ unitIval := by
  simp [unitIval, toReal_def]; exact ⟨h1, h2⟩

def sinStep (w : Nat) (Y2 : Ival) (k : Nat) (T : Ival) : Ival :=
  Ival.divNat w (Ival.mul w (Ival.neg T) Y2) ((2 * k + 2) * (2 * k + 3))

def cosStep (w : Nat) (Y2 : Ival) (k : Nat) (T : Ival) : Ival :=
  Ival.divNat w (Ival.mul w (Ival.neg T) Y2) ((2 * k + 1) * (2 * k + 2))

/-- series state with at least one step taken -/
def encl1 (w : Nat) (st : SerState) : Ival :=
  if 1 ≤ st.k then st.encl w (Dy.ofNat 2) else unitIval

/-- `sin y` for `|y| ≤ 2` -/
def sinSer (w : Nat) (y : Dy) : Ival :=
  if isTrigArg y then
    let Y := Ival.pt y
    encl1 w (serLoop w (sinStep w (Ival.sq w Y)) (smallTerm w) (w + 16) (SerState.start Y))
  else unitIval

/-- `cos y` for `|y| ≤ 2` -/
def cosSer (w : Nat) (y : Dy) : Ival :=
  if isTrigArg y then
    let Y := Ival.pt y
    encl1 w (serLoop w (cosStep w (Ival.sq w Y)) (smallTerm w) (w + 16) (SerState.start Ival.one))
  else unitIval

/-- the ratio estimate `y²/d ≤ 1/2` for `|y| ≤ 2`, `d ≥ 8` -/
private theorem ratio_aux {y : ℝ} (hy : |y| ≤ 2) {d : ℕ} (hd : 8 ≤ d) : y ^ 2 / (d : ℝ) ≤ 1 / 2 := by
  have hy2 : y ^ 2 ≤ 4 := by have := sq_abs y; nlinarith [abs_nonneg y]
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  rw [div_le_iff₀ (by linarith)]; nlinarith

private theorem ratio_step {tk yv : ℝ} {d : ℕ} (hd : 0 < d) (h : yv ^ 2 / (d : ℝ) ≤ 1 / 2) :
    |-tk * yv ^ 2 / (d : ℝ)| ≤ 1 / 2 * |tk| := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [neg_mul, neg_div, abs_neg, mul_div_assoc, abs_mul,
    abs_of_nonneg (div_nonneg (sq_nonneg yv) hd'.le), mul_comm (1 / 2 : ℝ)]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- membership of the endpoints -/
theorem mem_lo_of {I : Ival} {a b : Dy} (ha : I.lo = some a) (hb : I.hi = some b)
    (hab : a.toReal ≤ b.toReal) : a.toReal ∈ I :=
  ⟨fun l hl => by rw [ha] at hl; cases hl; exact le_rfl,
   fun h hh => by rw [hb] at hh; cases hh; exact hab⟩

theorem mem_hi_of {I : Ival} {a b : Dy} (ha : I.lo = some a) (hb : I.hi = some b)
    (hab : a.toReal ≤ b.toReal) : b.toReal ∈ I :=
  ⟨fun l hl => by rw [ha] at hl; cases hl; exact hab,
   fun h hh => by rw [hb] at hh; cases hh; exact le_rfl⟩

theorem mem_sinSer (w : Nat) (y : Dy) : Real.sin y.toReal ∈ sinSer w y := by
  unfold sinSer
  split
  · rename_i h
    have hy := abs_le_two_of_isTrigArg h
    simp only
    set t : ℕ → ℝ := fun n => (-1) ^ n * y.toReal ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) with ht
    have hsq : y.toReal ^ 2 ∈ Ival.sq w (Ival.pt y) := Ival.mem_sq (Ival.mem_pt y)
    have hrec : ∀ k, t (k + 1) = -t k * y.toReal ^ 2 / (((2 * k + 2) * (2 * k + 3) : ℕ) : ℝ) := by
      intro k
      simp only [ht]
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    have hstep : ∀ k X, t k ∈ X → t (k + 1) ∈ sinStep w (Ival.sq w (Ival.pt y)) k X := by
      intro k X hX
      rw [hrec]
      exact Ival.mem_divNat (Ival.mem_mul (Ival.mem_neg hX) hsq) (by positivity)
    have h0 : t 0 ∈ Ival.pt y := by simpa [ht] using Ival.mem_pt y
    have hinv := serLoop_inv (p := w) (small := smallTerm w) hstep (w + 16) _ (SerState.start_inv h0)
    unfold encl1
    split
    · rename_i hk
      refine SerState.mem_encl (Real.hasSum_sin y.toReal) hinv (q := 1 / 2) (by norm_num)
        (by norm_num) ?_ (by simp [toReal_def]; norm_num)
      intro k hk2
      show |t (k + 1)| ≤ 1 / 2 * |t k|
      rw [hrec]
      have hk1 : 1 ≤ k := le_trans hk hk2
      exact ratio_step (by positivity) (ratio_aux hy (by nlinarith))
    · exact mem_unitIval (Real.neg_one_le_sin _) (Real.sin_le_one _)
  · exact mem_unitIval (Real.neg_one_le_sin _) (Real.sin_le_one _)

theorem mem_cosSer (w : Nat) (y : Dy) : Real.cos y.toReal ∈ cosSer w y := by
  unfold cosSer
  split
  · rename_i h
    have hy := abs_le_two_of_isTrigArg h
    simp only
    set t : ℕ → ℝ := fun n => (-1) ^ n * y.toReal ^ (2 * n) / ((2 * n).factorial : ℝ) with ht
    have hsq : y.toReal ^ 2 ∈ Ival.sq w (Ival.pt y) := Ival.mem_sq (Ival.mem_pt y)
    have hrec : ∀ k, t (k + 1) = -t k * y.toReal ^ 2 / (((2 * k + 1) * (2 * k + 2) : ℕ) : ℝ) := by
      intro k
      simp only [ht]
      rw [show 2 * (k + 1) = (2 * k) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    have hstep : ∀ k X, t k ∈ X → t (k + 1) ∈ cosStep w (Ival.sq w (Ival.pt y)) k X := by
      intro k X hX
      rw [hrec]
      exact Ival.mem_divNat (Ival.mem_mul (Ival.mem_neg hX) hsq) (by positivity)
    have h0 : t 0 ∈ Ival.one := by simpa [ht] using Ival.mem_one
    have hinv := serLoop_inv (p := w) (small := smallTerm w) hstep (w + 16) _ (SerState.start_inv h0)
    unfold encl1
    split
    · rename_i hk
      refine SerState.mem_encl (Real.hasSum_cos y.toReal) hinv (q := 1 / 2) (by norm_num)
        (by norm_num) ?_ (by simp [toReal_def]; norm_num)
      intro k hk2
      show |t (k + 1)| ≤ 1 / 2 * |t k|
      rw [hrec]
      have hk1 : 1 ≤ k := le_trans hk hk2
      exact ratio_step (by positivity) (ratio_aux hy (by nlinarith))
    · exact mem_unitIval (Real.neg_one_le_cos _) (Real.cos_le_one _)
  · exact mem_unitIval (Real.neg_one_le_cos _) (Real.cos_le_one _)

/-! ### Range reduction -/

/-- `⌊d⌋` for a dyadic -/
def Dy.floor (d : Dy) : Int :=
  if 0 ≤ d.exponent then d.mantissa * 2 ^ d.exponent.toNat else d.mantissa >>> (-d.exponent).toNat

/-- a good integer `k ≈ m / π` (any integer is sound) -/
def piMultiple (c : Ctx) (m : Dy) : Int :=
  match c.pi.lo with
  | some pl => if isPos pl then Dy.floor (Vendor.Dyadic.add (divD 64 m pl) half) else 0
  | none => 0

/-- `Y ⊆ [-π/2, π/2]` certified with the context's `π` -/
def inHalfPi (c : Ctx) (Y : Ival) : Bool :=
  match Y.lo, Y.hi, c.pi.lo with
  | some a, some b, some pl => Dy.leB (Vendor.Dyadic.neg (Dy.scale2 pl (-1))) a && Dy.leB b (Dy.scale2 pl (-1))
  | _, _, _ => false

theorem inHalfPi_sound {c : Ctx} (hc : c.Valid) {Y : Ival} (h : inHalfPi c Y = true) {y : ℝ}
    (hy : y ∈ Y) : -(Real.pi / 2) ≤ y ∧ y ≤ Real.pi / 2 := by
  unfold inHalfPi at h
  split at h
  · rename_i a b pl ha hb hp
    simp only [Bool.and_eq_true] at h
    have h1 := toReal_le_of_leB h.1; have h2 := toReal_le_of_leB h.2
    have hpl := hc.pi_mem.1 pl hp
    have hya := hy.1 a ha; have hyb := hy.2 b hb
    simp only [toReal_def, toRat_neg', toRat_scale2, Rat.cast_neg, Rat.cast_mul, Rat.cast_zpow,
      Rat.cast_ofNat] at h1 h2 hpl hya hyb
    norm_num at h1 h2
    constructor <;> linarith
  · simp at h

/-- sin on `Y ⊆ [-π/2, π/2]` (monotone) -/
def sinMono (w : Nat) (Y : Ival) : Ival :=
  match Y.lo, Y.hi with
  | some a, some b => ⟨(sinSer w a).lo, (sinSer w b).hi⟩
  | _, _ => unitIval

theorem mem_sinMono {c : Ctx} (hc : c.Valid) {w : Nat} {Y : Ival} (hY : inHalfPi c Y = true) {y : ℝ}
    (hy : y ∈ Y) : Real.sin y ∈ sinMono w Y := by
  have hb := inHalfPi_sound hc hY hy
  unfold sinMono
  split
  · rename_i a b ha hb'
    have hya := hy.1 a ha; have hyb := hy.2 b hb'
    have hab := inHalfPi_sound hc hY (mem_lo_of ha hb' (le_trans hya hyb))
    have hbb := inHalfPi_sound hc hY (mem_hi_of ha hb' (le_trans hya hyb))
    refine ⟨fun l hl => le_trans ((mem_sinSer w a).1 l hl) ?_, fun h hh => le_trans ?_ ((mem_sinSer w b).2 h hh)⟩
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two hab.1 hb.2 hya
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two hb.1 hbb.2 hyb
  · exact mem_unitIval (Real.neg_one_le_sin _) (Real.sin_le_one _)

/-- cos on `Y ⊆ [-π/2, π/2]` (even, antitone on `[0, π/2]`) -/
def cosEven (w : Nat) (Y : Ival) : Ival :=
  match Y.lo, Y.hi with
  | some a, some b =>
    if isNonneg a then ⟨(cosSer w b).lo, (cosSer w a).hi⟩
    else if isNonneg (Vendor.Dyadic.neg b) then ⟨(cosSer w a).lo, (cosSer w b).hi⟩
    else ⟨Ival.omin (cosSer w a).lo (cosSer w b).lo, some Dy.one⟩
  | _, _ => unitIval

theorem mem_cosEven {c : Ctx} (hc : c.Valid) {w : Nat} {Y : Ival} (hY : inHalfPi c Y = true) {y : ℝ}
    (hy : y ∈ Y) : Real.cos y ∈ cosEven w Y := by
  have hb := inHalfPi_sound hc hY hy
  have hpi := Real.pi_pos
  -- cos is antitone in |y| on [-π/2, π/2]
  have key : ∀ u v : ℝ, |u| ≤ |v| → |v| ≤ Real.pi / 2 → Real.cos v ≤ Real.cos u := by
    intro u v huv hv
    rw [← Real.cos_abs u, ← Real.cos_abs v]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg u) (by linarith) huv
  unfold cosEven
  split
  · rename_i a b ha hb'
    have hya := hy.1 a ha; have hyb := hy.2 b hb'
    have hab := inHalfPi_sound hc hY (mem_lo_of ha hb' (le_trans hya hyb))
    have hbb := inHalfPi_sound hc hY (mem_hi_of ha hb' (le_trans hya hyb))
    have habs : |y| ≤ Real.pi / 2 := abs_le.2 hb
    split
    · rename_i hnn
      have ha0 : 0 ≤ a.toReal := by simp only [toReal_def]; exact_mod_cast (isNonneg_iff a).1 hnn
      refine ⟨fun l hl => le_trans ((mem_cosSer w b).1 l hl) ?_, fun h hh => le_trans ?_ ((mem_cosSer w a).2 h hh)⟩
      · apply key
        · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; exact hyb
        · rw [abs_of_nonneg (by linarith)]; exact hbb.2
      · apply key
        · rw [abs_of_nonneg ha0, abs_of_nonneg (by linarith)]; exact hya
        · exact habs
    split
    · rename_i _ hnp
      have hb0 : b.toReal ≤ 0 := by
        have := (isNonneg_iff _).1 hnp; simp only [toRat_neg'] at this
        simp only [toReal_def]; exact_mod_cast (by linarith : b.toRat ≤ 0)
      refine ⟨fun l hl => le_trans ((mem_cosSer w a).1 l hl) ?_, fun h hh => le_trans ?_ ((mem_cosSer w b).2 h hh)⟩
      · apply key
        · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
        · rw [abs_of_nonpos (by linarith)]; linarith [hab.1]
      · apply key
        · rw [abs_of_nonpos hb0, abs_of_nonpos (by linarith)]; linarith
        · exact habs
    · refine ⟨?_, by simp [toReal_def]; exact Real.cos_le_one _⟩
      apply Ival.loLe_omap2
      intro u v hu hv
      rcases le_total 0 y with h0 | h0
      · refine le_trans (Ival.min_toReal_le_right u v) (le_trans ((mem_cosSer w b).1 v hv) ?_)
        apply key
        · rw [abs_of_nonneg h0]; exact le_trans hyb (le_abs_self _)
        · exact abs_le.2 hbb
      · refine le_trans (Ival.min_toReal_le_left u v) (le_trans ((mem_cosSer w a).1 u hu) ?_)
        apply key
        · rw [abs_of_nonpos h0]; exact le_trans (by linarith) (neg_le_abs a.toReal)
        · exact abs_le.2 hab
  · exact mem_unitIval (Real.neg_one_le_cos _) (Real.cos_le_one _)

/-! ### Interval extensions -/

/-- Lipschitz enclosure `f(m) ± r` around the midpoint of `Y` (for `|m| ≤ 2`) -/
def lipEncl (w : Nat) (ser : Nat → Dy → Ival) (Y : Ival) : Ival :=
  match Y.mid, Y.width with
  | some m, some wd => Ival.widen w (ser w m) (Dy.scale2 wd (-1))
  | _, _ => unitIval

theorem mem_lipEncl {w : Nat} {ser : Nat → Dy → Ival} {f : ℝ → ℝ}
    (hf : ∀ u v, |f u - f v| ≤ |u - v|) (hser : ∀ m : Dy, f m.toReal ∈ ser w m)
    (hbound : ∀ u, -1 ≤ f u ∧ f u ≤ 1) {Y : Ival} {y : ℝ} (hy : y ∈ Y) : f y ∈ lipEncl w ser Y := by
  unfold lipEncl
  split
  · rename_i m wd hm hwd
    apply Ival.mem_widen (hser m)
    refine le_trans (hf y m.toReal) ?_
    rcases Y with ⟨lo, hi⟩
    cases lo with
    | none => simp [Ival.mid, Ival.omap2] at hm
    | some a =>
      cases hi with
      | none => simp [Ival.mid, Ival.omap2] at hm
      | some b =>
        simp only [Ival.mid, Ival.omap2, Option.some.injEq] at hm
        simp only [Ival.width, Ival.omap2, Option.some.injEq] at hwd
        subst hm; subst hwd
        have h1 := hy.1 a rfl; have h2 := hy.2 b rfl
        have hs' : (b.toRat : ℝ) - a.toRat ≤ ((subU 64 b a).toRat : ℝ) := by
          exact_mod_cast le_subU 64 b a
        simp only [toReal_def, Vendor.Dyadic.toRat_scale2, Dy.toRat_scale2, toRat_add', Rat.cast_mul, Rat.cast_add,
          Rat.cast_zpow, Rat.cast_ofNat] at h1 h2 ⊢
        rw [zpow_neg_one] at *
        rw [abs_le]; constructor <;> nlinarith
  · exact mem_unitIval (hbound y).1 (hbound y).2

/-- `k π` -/
def piMul (w : Nat) (c : Ctx) (k : Int) : Ival := Ival.mul w (Ival.pt (Dy.ofInt k)) c.pi

theorem mem_piMul {w : Nat} {c : Ctx} (hc : c.Valid) (k : Int) : (k : ℝ) * Real.pi ∈ piMul w c k := by
  refine Ival.mem_mul ?_ hc.pi_mem
  have := Ival.mem_pt (Dy.ofInt k); simpa [toReal_def] using this

/-- `sin` on an interval -/
def sinIval (c : Ctx) (X : Ival) : Ival :=
  let w := c.prec + 8
  match X.mid with
  | some m =>
    let k := piMultiple c m
    let Y := Ival.sub w X (piMul w c k)
    let S := if inHalfPi c Y then sinMono w Y else lipEncl w sinSer Y
    if k % 2 == 0 then S else Ival.neg S
  | none => unitIval

/-- `cos` on an interval -/
def cosIval (c : Ctx) (X : Ival) : Ival :=
  let w := c.prec + 8
  match X.mid with
  | some m =>
    let k := piMultiple c m
    let Y := Ival.sub w X (piMul w c k)
    let S := if inHalfPi c Y then cosEven w Y else lipEncl w cosSer Y
    if k % 2 == 0 then S else Ival.neg S
  | none => unitIval

theorem neg_one_zpow_cases (k : Int) : ((-1 : ℝ) ^ k = 1 ∧ k % 2 = 0) ∨ ((-1 : ℝ) ^ k = -1 ∧ k % 2 ≠ 0) := by
  rcases Int.even_or_odd k with h | h
  · left; exact ⟨h.neg_one_zpow, Int.even_iff.1 h⟩
  · right; exact ⟨h.neg_one_zpow, by have := Int.odd_iff.1 h; omega⟩

theorem mem_sinIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival} (hx : x ∈ X) : Real.sin x ∈ sinIval c X := by
  unfold sinIval
  simp only
  split
  · rename_i m _
    set k := piMultiple c m
    have hy : x - k * Real.pi ∈ Ival.sub (c.prec + 8) X (piMul (c.prec + 8) c k) :=
      Ival.mem_sub hx (mem_piMul hc k)
    have hsin : Real.sin x = (-1 : ℝ) ^ k * Real.sin (x - k * Real.pi) := by
      rw [← Real.sin_add_int_mul_pi]; ring_nf
    have hS : Real.sin (x - k * Real.pi) ∈
        (if inHalfPi c (Ival.sub (c.prec + 8) X (piMul (c.prec + 8) c k)) then
          sinMono (c.prec + 8) (Ival.sub (c.prec + 8) X (piMul (c.prec + 8) c k))
        else lipEncl (c.prec + 8) sinSer (Ival.sub (c.prec + 8) X (piMul (c.prec + 8) c k))) := by
      split
      · rename_i h; exact mem_sinMono hc h hy
      · exact mem_lipEncl Real.abs_sin_sub_sin_le (mem_sinSer _)
          (fun u => ⟨Real.neg_one_le_sin u, Real.sin_le_one u⟩) hy
    rcases neg_one_zpow_cases k with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hsin, h1, one_mul]; simp only [h2, beq_self_eq_true, ↓reduceIte]; exact hS
    · rw [hsin, h1, neg_one_mul]
      have : (k % 2 == 0) = false := by simp [h2]
      simp only [this]; exact Ival.mem_neg hS
  · exact mem_unitIval (Real.neg_one_le_sin _) (Real.sin_le_one _)

theorem mem_cosIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival} (hx : x ∈ X) : Real.cos x ∈ cosIval c X := by
  unfold cosIval
  simp only
  split
  · rename_i m _
    set k := piMultiple c m
    have hy : x - k * Real.pi ∈ Ival.sub (c.prec + 8) X (piMul (c.prec + 8) c k) :=
      Ival.mem_sub hx (mem_piMul hc k)
    have hcos : Real.cos x = (-1 : ℝ) ^ k * Real.cos (x - k * Real.pi) := by
      rw [← Real.cos_add_int_mul_pi]; ring_nf
    have hS : Real.cos (x - k * Real.pi) ∈
        (if inHalfPi c (Ival.sub (c.prec + 8) X (piMul (c.prec + 8) c k)) then
          cosEven (c.prec + 8) (Ival.sub (c.prec + 8) X (piMul (c.prec + 8) c k))
        else lipEncl (c.prec + 8) cosSer (Ival.sub (c.prec + 8) X (piMul (c.prec + 8) c k))) := by
      split
      · rename_i h; exact mem_cosEven hc h hy
      · exact mem_lipEncl Real.abs_cos_sub_cos_le (mem_cosSer _)
          (fun u => ⟨Real.neg_one_le_cos u, Real.cos_le_one u⟩) hy
    rcases neg_one_zpow_cases k with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hcos, h1, one_mul]; simp only [h2, beq_self_eq_true, ↓reduceIte]; exact hS
    · rw [hcos, h1, neg_one_mul]
      have : (k % 2 == 0) = false := by simp [h2]
      simp only [this]; exact Ival.mem_neg hS
  · exact mem_unitIval (Real.neg_one_le_cos _) (Real.cos_le_one _)

@[lynth_fn] def sinR : Fn1 .real .real where
  name := "sin"
  graph x y := y = Real.sin x
  exu := exu_eq _
  ev := sinIval
  sound := fun _ _ _ _ hc hy hx => by obtain rfl := hy; exact mem_sinIval hc hx
  cost := 50

@[lynth_fn] def cosR : Fn1 .real .real where
  name := "cos"
  graph x y := y = Real.cos x
  exu := exu_eq _
  ev := cosIval
  sound := fun _ _ _ _ hc hy hx => by obtain rfl := hy; exact mem_cosIval hc hx
  cost := 50

@[lynth_fn] def tanR : Fn1 .real .real where
  name := "tan"
  graph x y := y = Real.tan x
  exu := exu_eq _
  ev c X := Ival.div (c.prec + 8) (sinIval c X) (cosIval c X)
  sound := fun _ _ _ _ hc hy hx => by
    obtain rfl := hy; rw [Real.tan_eq_sin_div_cos]
    exact Ival.mem_div (mem_sinIval hc hx) (mem_cosIval hc hx)
  cost := 100

@[lynth_fn] def cotR : Fn1 .real .real where
  name := "cot"
  graph x y := y = Real.cot x
  exu := exu_eq _
  ev c X := Ival.div (c.prec + 8) (cosIval c X) (sinIval c X)
  sound := fun _ _ _ _ hc hy hx => by
    obtain rfl := hy; rw [Real.cot_eq_cos_div_sin]
    exact Ival.mem_div (mem_cosIval hc hx) (mem_sinIval hc hx)
  cost := 100

@[lynth_fn] def piR : Fn0 .real where
  name := "π"
  graph y := y = Real.pi
  exu := exu_eq₀ _
  ev c := c.pi
  sound := fun _ _ hc hy => by obtain rfl := hy; exact hc.pi_mem

end Lynth.Interval.Fns
