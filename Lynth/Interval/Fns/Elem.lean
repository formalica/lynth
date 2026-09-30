import Lynth.Interval.Fns.Trig
import Lynth.Interval.Fns.Log
import Lynth.Interval.Series.Arctan
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# More elementary functions

arctan (reductions `arctan z = arctan (1/2) + arctan ((z - 1/2)/(1 + z/2))` on
`[0, 1]`, `arctan a = π/2 - arctan (1/a)` for `a > 1`, oddness), arcsin,
arccos, sinh, cosh, tanh, arsinh, arcosh, artanh, logb, rpow, sinc.
See `docs/interval/04-functions.md §6, §9–12`.
-/

namespace Lynth.Interval.Fns

open Lynth.Interval Dy

/-! ### arctan -/

/-- `arctan z` for `z ∈ Z ⊆ [0, 1]` -/
def atanUnit (w : Nat) (Z : Ival) : Ival :=
  if Z.nonneg && Ival.leB Z Ival.one then
    let half := Ival.ofRat w (1 / 2)
    let Y := Ival.div w (Ival.sub w Z half) (Ival.add w Ival.one (Ival.mul w half Z))
    Ival.add w (arctanSeries w half) (arctanSeries w Y)
  else ⟨some (Dy.ofInt (-2)), some (Dy.ofInt 2)⟩

theorem arctan_half_shift {z : ℝ} (h0 : 0 ≤ z) :
    Real.arctan z = Real.arctan (1 / 2) + Real.arctan ((z - 1 / 2) / (1 + 1 / 2 * z)) := by
  have hd : 0 < 1 + 1 / 2 * z := by linarith
  have hy : 1 / 2 * ((z - 1 / 2) / (1 + 1 / 2 * z)) < 1 := by
    rw [← mul_div_assoc, div_lt_one hd]; linarith
  rw [Real.arctan_add hy]
  congr 1
  field_simp
  ring

theorem mem_atanUnit (w : Nat) {Z : Ival} {z : ℝ} (hz : z ∈ Z) : Real.arctan z ∈ atanUnit w Z := by
  unfold atanUnit
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    have h0 := Ival.nonneg_of h.1 hz
    have hhalf : ((1 / 2 : ℚ) : ℝ) ∈ Ival.ofRat w (1 / 2) := Ival.mem_ofRat w _
    push_cast at hhalf
    rw [arctan_half_shift h0]
    exact Ival.mem_add (mem_arctanSeries w hhalf)
      (mem_arctanSeries w (Ival.mem_div (Ival.mem_sub hz hhalf)
        (Ival.mem_add Ival.mem_one (Ival.mem_mul hhalf hz))))
  · have := abs_arctan_le_two z
    exact ⟨by simp [toReal_def]; linarith [(abs_le.1 this).1], by simp [toReal_def]; linarith [(abs_le.1 this).2]⟩

/-- `π/2` -/
def halfPi (c : Ctx) : Ival := Ival.divNat (c.prec + 8) c.pi 2

theorem mem_halfPi {c : Ctx} (hc : c.Valid) : Real.pi / 2 ∈ halfPi c := by
  have := Ival.mem_divNat (p := c.prec + 8) hc.pi_mem (n := 2) (by norm_num)
  unfold halfPi; simpa using this

/-- `arctan a` for `a ≥ 0` -/
def atanNonneg (c : Ctx) (w : Nat) (a : Dy) : Ival :=
  if Dy.leB a Dy.one then atanUnit w (Ival.pt a)
  else Ival.sub w (halfPi c) (atanUnit w (Ival.inv w (Ival.pt a)))

theorem mem_atanNonneg {c : Ctx} (hc : c.Valid) (w : Nat) {a : Dy} (ha : 0 ≤ a.toReal) :
    Real.arctan a.toReal ∈ atanNonneg c w a := by
  unfold atanNonneg
  split
  · exact mem_atanUnit w (Ival.mem_pt a)
  · rename_i h
    have h1 : 1 < a.toReal := by
      have : ¬ a.toRat ≤ Dy.one.toRat := fun h' => h ((leB_iff _ _).2 h')
      simp only [toReal_def]; simp at this; exact_mod_cast this
    have hpos : 0 < a.toReal := by linarith
    have e : Real.arctan a.toReal = Real.pi / 2 - Real.arctan (a.toReal)⁻¹ := by
      have := Real.arctan_inv_of_pos (inv_pos.2 hpos)
      rw [inv_inv] at this; exact this
    rw [e]
    exact Ival.mem_sub (mem_halfPi hc) (mem_atanUnit w (Ival.mem_inv (Ival.mem_pt a)))

/-- `arctan a` for a dyadic point -/
def atanPt (c : Ctx) (w : Nat) (a : Dy) : Ival :=
  if isNonneg a then atanNonneg c w a else Ival.neg (atanNonneg c w (Vendor.Dyadic.neg a))

theorem mem_atanPt {c : Ctx} (hc : c.Valid) (w : Nat) (a : Dy) : Real.arctan a.toReal ∈ atanPt c w a := by
  unfold atanPt
  split
  · rename_i h
    exact mem_atanNonneg hc w (by simp only [toReal_def]; exact_mod_cast (isNonneg_iff a).1 h)
  · rename_i h
    have hn : a.toRat < 0 := by
      by_contra h'; push Not at h'; exact h ((isNonneg_iff a).2 h')
    have ha : 0 ≤ (Vendor.Dyadic.neg a).toReal := by
      have : ((a.toRat : ℚ) : ℝ) < 0 := by exact_mod_cast hn
      simp only [toReal_def, toRat_neg', Rat.cast_neg]; linarith
    have := Ival.mem_neg (mem_atanNonneg hc w ha)
    simp only [toReal_def, toRat_neg', Rat.cast_neg, Real.arctan_neg, neg_neg] at this ⊢
    exact this

/-- interval extension of `arctan` (monotone, bounded by `±2`) -/
def atanIval (c : Ctx) (X : Ival) : Ival :=
  let w := c.prec + 8
  ⟨some (match X.lo with | some a => ((atanPt c w a).lo).getD (Dy.ofInt (-2)) | none => Dy.ofInt (-2)),
   some (match X.hi with | some b => ((atanPt c w b).hi).getD (Dy.ofInt 2) | none => Dy.ofInt 2)⟩

theorem mem_atanIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    Real.arctan x ∈ atanIval c X := by
  have hb := abs_arctan_le_two x
  refine ⟨?_, ?_⟩
  · simp only [atanIval, Ival.loLe_some]
    split
    · rename_i a ha
      have hax := Real.arctan_mono (hx.1 a ha)
      cases hl : (atanPt c (c.prec + 8) a).lo with
      | none => simp [toReal_def]; linarith [(abs_le.1 hb).1]
      | some l => simp only [Option.getD_some]; exact le_trans ((mem_atanPt hc _ a).1 l hl) hax
    · simp [toReal_def]; linarith [(abs_le.1 hb).1]
  · simp only [atanIval, Ival.leHi_some]
    split
    · rename_i b hb'
      have hxb := Real.arctan_mono (hx.2 b hb')
      cases hh : (atanPt c (c.prec + 8) b).hi with
      | none => simp [toReal_def]; linarith [(abs_le.1 hb).2]
      | some h => simp only [Option.getD_some]; exact le_trans hxb ((mem_atanPt hc _ b).2 h hh)
    · simp [toReal_def]; linarith [(abs_le.1 hb).2]

@[lynth_fn] def arctanR : Fn1 .real .real where
  name := "arctan"
  graph x y := y = Real.arctan x
  exu := exu_eq _
  ev := atanIval
  sound := fun _ _ _ _ hc hy hx => by obtain rfl := hy; exact mem_atanIval hc hx
  cost := 60

/-! ### arcsin, arccos -/

/-- `arcsin a` for a dyadic point -/
def asinPt (c : Ctx) (w : Nat) (a : Dy) : Ival :=
  if Dy.leB Dy.one a then halfPi c
  else if Dy.leB a (Dy.ofInt (-1)) then Ival.neg (halfPi c)
  else
    let A := Ival.pt a
    atanIval c (Ival.div w A (Ival.sqrt w (Ival.sub w Ival.one (Ival.sq w A))))

theorem mem_asinPt {c : Ctx} (hc : c.Valid) (w : Nat) (a : Dy) : Real.arcsin a.toReal ∈ asinPt c w a := by
  unfold asinPt
  split
  · rename_i h
    have : 1 ≤ a.toReal := by have := toReal_le_of_leB h; simpa [toReal_def] using this
    rw [Real.arcsin_of_one_le this]; exact mem_halfPi hc
  split
  · rename_i _ h
    have : a.toReal ≤ -1 := by have := toReal_le_of_leB h; simpa [toReal_def] using this
    rw [Real.arcsin_of_le_neg_one this]; exact Ival.mem_neg (mem_halfPi hc)
  · rename_i h1 h2
    have ha1 : a.toReal < 1 := by
      have : ¬ Dy.one.toRat ≤ a.toRat := fun h' => h1 ((leB_iff _ _).2 h')
      simp only [toReal_def]; simp at this; exact_mod_cast this
    have ha2 : -1 < a.toReal := by
      have : ¬ a.toRat ≤ (Dy.ofInt (-1)).toRat := fun h' => h2 ((leB_iff _ _).2 h')
      simp only [toReal_def]; simp at this; exact_mod_cast this
    rw [Real.arcsin_eq_arctan ⟨ha2, ha1⟩]
    have hA := Ival.mem_pt a
    exact mem_atanIval hc (Ival.mem_div hA (Ival.mem_sqrt (Ival.mem_sub Ival.mem_one (Ival.mem_sq hA))))

def asinIval (c : Ctx) (X : Ival) : Ival :=
  let w := c.prec + 8
  ⟨some (match X.lo with | some a => ((asinPt c w a).lo).getD (Dy.ofInt (-2)) | none => Dy.ofInt (-2)),
   some (match X.hi with | some b => ((asinPt c w b).hi).getD (Dy.ofInt 2) | none => Dy.ofInt 2)⟩

theorem abs_arcsin_le_two (x : ℝ) : |Real.arcsin x| ≤ 2 := by
  have h1 := Real.arcsin_le_pi_div_two x
  have h2 := Real.neg_pi_div_two_le_arcsin x
  have := Real.pi_lt_d2
  rw [abs_le]; constructor <;> linarith

theorem mem_asinIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    Real.arcsin x ∈ asinIval c X := by
  have hb := abs_arcsin_le_two x
  refine ⟨?_, ?_⟩
  · simp only [asinIval, Ival.loLe_some]
    split
    · rename_i a ha
      have hax := Real.arcsin_le_arcsin (hx.1 a ha)
      cases hl : (asinPt c (c.prec + 8) a).lo with
      | none => simp [toReal_def]; linarith [(abs_le.1 hb).1]
      | some l => simp only [Option.getD_some]; exact le_trans ((mem_asinPt hc _ a).1 l hl) hax
    · simp [toReal_def]; linarith [(abs_le.1 hb).1]
  · simp only [asinIval, Ival.leHi_some]
    split
    · rename_i b hb'
      have hxb := Real.arcsin_le_arcsin (hx.2 b hb')
      cases hh : (asinPt c (c.prec + 8) b).hi with
      | none => simp [toReal_def]; linarith [(abs_le.1 hb).2]
      | some h => simp only [Option.getD_some]; exact le_trans hxb ((mem_asinPt hc _ b).2 h hh)
    · simp [toReal_def]; linarith [(abs_le.1 hb).2]

@[lynth_fn] def arcsinR : Fn1 .real .real where
  name := "arcsin"
  graph x y := y = Real.arcsin x
  exu := exu_eq _
  ev := asinIval
  sound := fun _ _ _ _ hc hy hx => by obtain rfl := hy; exact mem_asinIval hc hx
  cost := 80

@[lynth_fn] def arccosR : Fn1 .real .real where
  name := "arccos"
  graph x y := y = Real.arccos x
  exu := exu_eq _
  ev c X := Ival.sub (c.prec + 8) (halfPi c) (asinIval c X)
  sound := fun _ _ _ _ hc hy hx => by
    obtain rfl := hy; rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    exact Ival.mem_sub (mem_halfPi hc) (mem_asinIval hc hx)
  cost := 80

/-! ### Hyperbolic functions -/

def sinhIval (c : Ctx) (X : Ival) : Ival :=
  Ival.divNat (c.prec + 8) (Ival.sub (c.prec + 8) (expIval c X) (expIval c (Ival.neg X))) 2

theorem mem_sinhIval (c : Ctx) {x : ℝ} {X : Ival} (hx : x ∈ X) : Real.sinh x ∈ sinhIval c X := by
  rw [Real.sinh_eq]
  have := Ival.mem_divNat (p := c.prec + 8)
    (Ival.mem_sub (p := c.prec + 8) (mem_expIval c hx) (mem_expIval c (Ival.mem_neg hx))) (n := 2) (by norm_num)
  unfold sinhIval; simpa using this

def coshIval (c : Ctx) (X : Ival) : Ival :=
  Ival.divNat (c.prec + 8) (Ival.add (c.prec + 8) (expIval c X) (expIval c (Ival.neg X))) 2

theorem mem_coshIval (c : Ctx) {x : ℝ} {X : Ival} (hx : x ∈ X) : Real.cosh x ∈ coshIval c X := by
  rw [Real.cosh_eq]
  have := Ival.mem_divNat (p := c.prec + 8)
    (Ival.mem_add (p := c.prec + 8) (mem_expIval c hx) (mem_expIval c (Ival.mem_neg hx))) (n := 2) (by norm_num)
  unfold coshIval; simpa using this

@[lynth_fn] def sinhR : Fn1 .real .real where
  name := "sinh"
  graph x y := y = Real.sinh x
  exu := exu_eq _
  ev := sinhIval
  sound := fun c _ _ _ _ hy hx => by obtain rfl := hy; exact mem_sinhIval c hx
  cost := 80

@[lynth_fn] def coshR : Fn1 .real .real where
  name := "cosh"
  graph x y := y = Real.cosh x
  exu := exu_eq _
  ev := coshIval
  sound := fun c _ _ _ _ hy hx => by obtain rfl := hy; exact mem_coshIval c hx
  cost := 80

@[lynth_fn] def tanhR : Fn1 .real .real where
  name := "tanh"
  graph x y := y = Real.tanh x
  exu := exu_eq _
  ev c X := Ival.div (c.prec + 8) (sinhIval c X) (coshIval c X)
  sound := fun c _ _ _ _ hy hx => by
    obtain rfl := hy; rw [Real.tanh_eq_sinh_div_cosh]
    exact Ival.mem_div (mem_sinhIval c hx) (mem_coshIval c hx)
  cost := 160

@[lynth_fn] def arsinhR : Fn1 .real .real where
  name := "arsinh"
  graph x y := y = Real.arsinh x
  exu := exu_eq _
  ev c X := let w := c.prec + 8
    logIval c (Ival.add w X (Ival.sqrt w (Ival.add w Ival.one (Ival.sq w X))))
  sound := fun _ _ _ _ hc hy hx => by
    obtain rfl := hy
    exact mem_logIval hc (Ival.mem_add hx (Ival.mem_sqrt (Ival.mem_add Ival.mem_one (Ival.mem_sq hx))))
  cost := 80

@[lynth_fn] def arcoshR : Fn1 .real .real where
  name := "arcosh"
  graph x y := y = Real.arcosh x
  exu := exu_eq _
  ev c X := let w := c.prec + 8
    logIval c (Ival.add w X (Ival.sqrt w (Ival.sub w (Ival.sq w X) Ival.one)))
  sound := fun _ _ _ _ hc hy hx => by
    obtain rfl := hy
    exact mem_logIval hc (Ival.mem_add hx (Ival.mem_sqrt (Ival.mem_sub (Ival.mem_sq hx) Ival.mem_one)))
  cost := 80

@[lynth_fn] def artanhR : Fn1 .real .real where
  name := "artanh"
  graph x y := y = Real.artanh x
  exu := exu_eq _
  ev c X := let w := c.prec + 8
    logIval c (Ival.sqrt w (Ival.div w (Ival.add w Ival.one X) (Ival.sub w Ival.one X)))
  sound := fun _ _ _ _ hc hy hx => by
    obtain rfl := hy
    exact mem_logIval hc (Ival.mem_sqrt (Ival.mem_div (Ival.mem_add Ival.mem_one hx)
      (Ival.mem_sub Ival.mem_one hx)))
  cost := 80

/-! ### logb, rpow, sinc -/

@[lynth_fn] def logbR : Fn2 .real .real .real where
  name := "logb"
  graph b x y := y = Real.logb b x
  exu := exu_eq₂ _
  ev c B X := Ival.div (c.prec + 8) (logIval c X) (logIval c B)
  sound := fun _ _ _ _ _ _ hc hy hb hx => by
    obtain rfl := hy
    exact Ival.mem_div (mem_logIval hc hx) (mem_logIval hc hb)
  cost := 100

def rpowIval (c : Ctx) (X Y : Ival) : Ival :=
  if X.pos then expIval c (Ival.mul (c.prec + 8) (logIval c X) Y) else Ival.top

theorem mem_rpowIval {c : Ctx} (hc : c.Valid) {x y : ℝ} {X Y : Ival} (hx : x ∈ X) (hy : y ∈ Y) :
    x ^ y ∈ rpowIval c X Y := by
  unfold rpowIval
  split
  · rename_i h
    rw [Real.rpow_def_of_pos (Ival.pos_of h hx)]
    exact mem_expIval c (Ival.mem_mul (mem_logIval hc hx) hy)
  · exact Ival.mem_top _

@[lynth_fn] def rpowR : Fn2 .real .real .real where
  name := "rpow"
  graph x y z := z = x ^ y
  exu := exu_eq₂ _
  ev := rpowIval
  sound := fun _ _ _ _ _ _ hc hz hx hy => by obtain rfl := hz; exact mem_rpowIval hc hx hy
  cost := 100

def sincIval (c : Ctx) (X : Ival) : Ival :=
  if X.pos || X.negv then Ival.div (c.prec + 8) (sinIval c X) X
  else unitIval

@[lynth_fn] def sincR : Fn1 .real .real where
  name := "sinc"
  graph x y := y = Real.sinc x
  exu := exu_eq _
  ev := sincIval
  sound := fun c x _ X hc hy hx => by
    obtain rfl := hy
    unfold sincIval
    split
    · rename_i h
      have hx0 : x ≠ 0 := by
        simp only [Bool.or_eq_true] at h
        rcases h with h | h
        · exact (Ival.pos_of h hx).ne'
        · exact (Ival.neg_of h hx).ne
      rw [Real.sinc_of_ne_zero hx0]
      exact Ival.mem_div (mem_sinIval hc hx) hx
    · exact mem_unitIval (Real.neg_one_le_sinc x) (Real.sinc_le_one x)
  cost := 120

end Lynth.Interval.Fns
