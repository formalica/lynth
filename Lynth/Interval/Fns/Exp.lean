import Lynth.Interval.Series.Tail
import Lynth.Interval.Reify.Registry
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponential

Point kernel: argument reduction `a = 2^s r` with `|r| ≤ 1/2`, Taylor series of
`exp r` by the term recurrence `t_{k+1} = t_k r / (k+1)` with geometric tail
(`q = 1/2`), then `s` squarings.  The interval extension uses monotonicity.
See `docs/interval/04-functions.md §3`.
-/

namespace Lynth.Interval.Fns

open Lynth.Interval Dy

theorem hasSum_exp_series (x : ℝ) : HasSum (fun n => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x

def half : Dy := ⟨1, -1⟩
def negHalf : Dy := ⟨-1, -1⟩

theorem half_toReal : half.toReal = 1 / 2 := by simp [half, toReal_def]
theorem negHalf_toReal : negHalf.toReal = -(1 / 2) := by simp [negHalf, toReal_def]

/-- the term is below `2^-w` in magnitude -/
def smallTerm (w : Nat) (T : Ival) : Bool :=
  match Ival.magHi T with
  | some m => Dy.ltB m ⟨1, -(w : Int)⟩
  | none => false

/-- `r` lies in `[-1/2, 1/2]` -/
def isSmallArg (r : Dy) : Bool := Dy.leB r half && Dy.leB negHalf r

theorem abs_le_half_of_isSmallArg {r : Dy} (h : isSmallArg r = true) : |r.toReal| ≤ 1 / 2 := by
  simp only [isSmallArg, Bool.and_eq_true] at h
  have h1 := toReal_le_of_leB h.1
  have h2 := toReal_le_of_leB h.2
  rw [half_toReal] at h1; rw [negHalf_toReal] at h2
  exact abs_le.2 ⟨h2, h1⟩

def expStep (w : Nat) (r : Dy) (k : Nat) (T : Ival) : Ival :=
  Ival.divNat w (Ival.mul w T (Ival.pt r)) (k + 1)

/-- `exp r` for `|r| ≤ 1/2` (else the trivial enclosure `[0, ∞)`) -/
def expSmall (w : Nat) (r : Dy) : Ival :=
  if isSmallArg r then
    ((serLoop w (expStep w r) (smallTerm w) (w + 16) (SerState.start Ival.one)).encl w
      (Dy.ofNat 2)).clampLo Dy.zero
  else ⟨some Dy.zero, none⟩

theorem mem_expSmall (w : Nat) (r : Dy) : Real.exp r.toReal ∈ expSmall w r := by
  have hpos := Real.exp_pos r.toReal
  unfold expSmall
  split
  · rename_i h
    have hr := abs_le_half_of_isSmallArg h
    refine Ival.mem_clampLo ?_ (by simp [toReal_def]; exact hpos.le)
    set t : ℕ → ℝ := fun n => r.toReal ^ n / (n.factorial : ℝ) with ht
    have hstep : ∀ k X, t k ∈ X → t (k + 1) ∈ expStep w r k X := by
      intro k X hX
      have e : t (k + 1) = t k * r.toReal / ((k + 1 : ℕ) : ℝ) := by
        simp only [ht, pow_succ, Nat.factorial_succ]; push_cast
        field_simp
      rw [e]
      exact Ival.mem_divNat (Ival.mem_mul hX (Ival.mem_pt r)) (Nat.succ_pos k)
    have hinv := serLoop_inv (p := w) (small := smallTerm w) hstep (w + 16) _
      (SerState.start_inv (t := t) (by simpa [ht] using Ival.mem_one))
    refine SerState.mem_encl (hasSum_exp_series r.toReal) hinv (q := 1 / 2) (by norm_num)
      (by norm_num) ?_ (by simp [toReal_def]; norm_num)
    intro k _
    have e : t (k + 1) = t k * (r.toReal / ((k + 1 : ℕ) : ℝ)) := by
      simp only [ht, pow_succ, Nat.factorial_succ]; push_cast; field_simp
    show |t (k + 1)| ≤ 1 / 2 * |t k|
    rw [e, abs_mul, mul_comm (1/2 : ℝ)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < ((k + 1 : ℕ) : ℝ))]
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    nlinarith
  · exact ⟨by simp [toReal_def]; exact hpos.le, by simp⟩

/-- repeated squaring -/
def sqIter (p : Nat) (E : Ival) : Nat → Ival
  | 0 => E
  | s + 1 => sqIter p (Ival.sq p E) s

theorem mem_sqIter {p : Nat} {x : ℝ} {E : Ival} (hx : x ∈ E) : ∀ s, x ^ (2 ^ s) ∈ sqIter p E s
  | 0 => by simpa [sqIter] using hx
  | s + 1 => by
    have := mem_sqIter (p := p) (Ival.mem_sq (p := p) hx) s
    rw [← pow_mul, ← pow_succ'] at this
    exact this

/-- reduction exponent `s` with `|a| / 2^s ≤ 1/2` (when possible) -/
def expRed (a : Dy) : Nat := Int.toNat ((bits a.mantissa : Int) + a.exponent + 1)

/-- point enclosure of `exp a` at working precision about `w` bits -/
def expPt (w : Nat) (a : Dy) : Ival :=
  let s := expRed a
  sqIter (w + s) (expSmall (w + s + 8) (Dy.scale2 a (-(s : Int)))) s

theorem mem_expPt (w : Nat) (a : Dy) : Real.exp a.toReal ∈ expPt w a := by
  unfold expPt
  simp only
  set s := expRed a
  have ha : a.toReal = ((2 ^ s : ℕ) : ℝ) * (Dy.scale2 a (-(s : Int))).toReal := by
    simp only [toReal_def, toRat_scale2]; push_cast
    rw [zpow_neg, zpow_natCast]; field_simp
  rw [ha, Real.exp_nat_mul]
  exact mem_sqIter (mem_expSmall _ _) s

/-- interval extension of `exp` (monotone) -/
def expIval (c : Ctx) (X : Ival) : Ival :=
  let w := c.prec + 8
  ⟨some (match X.lo with
      | some a => (expPt w a).lo.getD Dy.zero
      | none => Dy.zero),
   match X.hi with
      | some b => (expPt w b).hi
      | none => none⟩

theorem mem_expIval (c : Ctx) {x : ℝ} {X : Ival} (hx : x ∈ X) : Real.exp x ∈ expIval c X := by
  obtain ⟨hx1, hx2⟩ := hx
  have hpos := Real.exp_pos x
  refine ⟨?_, ?_⟩
  · simp only [expIval, Ival.loLe_some]
    split
    · rename_i a ha
      have hax := Real.exp_le_exp.2 (hx1 a ha)
      have hm := mem_expPt (c.prec + 8) a
      cases hl : (expPt (c.prec + 8) a).lo with
      | none => simp [toReal_def]; exact hpos.le
      | some l => simp only [Option.getD_some]; exact le_trans (hm.1 l hl) hax
    · simp [toReal_def]; exact hpos.le
  · simp only [expIval]
    split
    · rename_i b hb
      have hxb := Real.exp_le_exp.2 (hx2 b hb)
      have hm := mem_expPt (c.prec + 8) b
      intro h hh
      exact le_trans hxb (hm.2 h hh)
    · simp

@[lynth_fn] def expR : Fn1 .real .real where
  name := "exp"
  graph x y := y = Real.exp x
  exu := exu_eq _
  ev := expIval
  sound := fun c _ _ _ _ hy hx => by obtain rfl := hy; exact mem_expIval c hx
  cost := 40

end Lynth.Interval.Fns
