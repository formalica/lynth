module

public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Data.Rat.Defs
public import Lynth.Interval.Core.Ctx
public import Lynth.Interval.Fns.Trig
public import Lynth.Interval.Integral.Exp
public import Lynth.Interval.Integral.Math.FixedTrig
public import Lynth.Interval.Num.CBox
public import Lynth.Interval.Num.Dy
public import Lynth.Interval.Num.Ival
public import Lynth.Interval.Series.Tail
public import Lynth.Interval.Vendor.Dyadic
import all Lynth.Interval.Integral.Math.FixedTrig
import all Lynth.Interval.Integral.Exp
import all Lynth.Interval.Fns.ComplexElem

/-! Fixed-point kernels for narrow quadrature samples. Wide real ranges use
the existing range evaluator, intersected with the known unit range. -/

namespace Lynth.Interval.Integral

open Fns

@[expose] public def fixedPointTrig (w : Nat) (sine : Bool) (y : Dy) : Ival :=
  let p := w + 8
  let (lo, hi) := Intgrl.fixedTrigBounds p sine y.toRat
  ⟨some ⟨lo, -(p : Int)⟩, some ⟨hi, -(p : Int)⟩⟩

theorem mem_fixedPointTrig (w : Nat) (sine : Bool) (y : Dy)
    (hy : |y.toReal| ≤ 2) :
    (if sine then Real.sin y.toReal else Real.cos y.toReal) ∈ fixedPointTrig w sine y := by
  have h := Intgrl.fixedTrigBounds_sound (w+8) sine y.toRat hy
  simpa only [fixedPointTrig, Ival.mem_mk, Ival.loLe_some, Ival.leHi_some,
    Dy.toReal_def, Dy.toRat_mk, Rat.cast_mul, Rat.cast_intCast, Rat.cast_zpow,
    Rat.cast_ofNat] using h

@[expose] public def fastSinSer (w : Nat) (y : Dy) : Ival :=
  if |y.toRat| < 1/16 then sinSer w y
  else if isTrigArg y then fixedPointTrig w true y else unitIval

@[expose] public def fastCosSer (w : Nat) (y : Dy) : Ival :=
  if isTrigArg y then fixedPointTrig w false y else unitIval

theorem mem_fastSinSer (w : Nat) (y : Dy) : Real.sin y.toReal ∈ fastSinSer w y := by
  unfold fastSinSer
  split
  · exact mem_sinSer w y
  · split
    · rename_i h
      exact mem_fixedPointTrig w true y (abs_le_two_of_isTrigArg h)
    · exact mem_unitIval (Real.neg_one_le_sin _) (Real.sin_le_one _)

theorem mem_fastCosSer (w : Nat) (y : Dy) : Real.cos y.toReal ∈ fastCosSer w y := by
  unfold fastCosSer
  split
  · rename_i h
    exact mem_fixedPointTrig w false y (abs_le_two_of_isTrigArg h)
  · exact mem_unitIval (Real.neg_one_le_cos _) (Real.cos_le_one _)

@[expose] public def clampUnit (X : Ival) : Ival := (X.clampLo (Dy.ofInt (-1))).clampHi Dy.one

theorem mem_clampUnit {x : ℝ} {X : Ival} (hx : x ∈ X) (hb : -1 ≤ x ∧ x ≤ 1) :
    x ∈ clampUnit X := by
  apply Ival.mem_clampHi
  · apply Ival.mem_clampLo hx
    simpa [Dy.toReal_def] using hb.1
  · simpa [Dy.toReal_def] using hb.2

@[expose] public def narrowTrig (X : Ival) : Bool :=
  match X.width with
  | some w => Dy.leB w ⟨1, -10⟩
  | none => false

@[expose] public def wideTrig (X : Ival) : Bool :=
  match X.width with
  | some w => Dy.leB (Dy.ofNat 7) w
  | none => true

@[expose] public def reducedTrig (c : Ctx) (ser : Nat → Dy → Ival) (X : Ival) : Ival :=
  match X.mid with
  | some m =>
    let k := piMultiple c m
    let Y := Ival.sub (c.prec+8) X (piMul (c.prec+8) c k)
    let S := clampUnit (lipEncl (c.prec+8) ser Y)
    if k % 2 == 0 then S else Ival.neg S
  | none => unitIval

theorem mem_reducedTrig {c : Ctx} (hc : c.Valid) {ser : Nat → Dy → Ival}
    {f : ℝ → ℝ} (hf : ∀ u v, |f u - f v| ≤ |u-v|)
    (hser : ∀ w y, f y.toReal ∈ ser w y)
    (hb : ∀ x, -1 ≤ f x ∧ f x ≤ 1)
    (hperiod : ∀ x (k : ℤ), f x = (-1 : ℝ)^k * f (x-k*Real.pi))
    {x : ℝ} {X : Ival} (hx : x ∈ X) : f x ∈ reducedTrig c ser X := by
  unfold reducedTrig
  split
  · rename_i m _
    let k := piMultiple c m
    have hy := Ival.mem_sub (p := c.prec+8) hx (mem_piMul (w := c.prec+8) hc k)
    have hS := mem_clampUnit (mem_lipEncl hf (hser (c.prec+8)) hb hy)
      (hb (x-k*Real.pi))
    rcases neg_one_zpow_cases k with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [hperiod x k, h1, one_mul]
      simpa only [k, h2, beq_self_eq_true, ↓reduceIte] using hS
    · rw [hperiod x k, h1, neg_one_mul]
      have h2' : (k % 2 == 0) = false := by simp [h2]
      simpa only [k, h2', Bool.false_eq_true, ↓reduceIte] using Ival.mem_neg hS
  · exact mem_unitIval (hb x).1 (hb x).2

@[expose] public def fastSinIval (c : Ctx) (X : Ival) : Ival :=
  if wideTrig X then unitIval else
    if narrowTrig X then reducedTrig c fastSinSer X else clampUnit (sinIval c X)

@[expose] public def fastCosIval (c : Ctx) (X : Ival) : Ival :=
  if wideTrig X then unitIval else
    if narrowTrig X then reducedTrig c fastCosSer X else clampUnit (cosIval c X)

theorem mem_fastSinIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    Real.sin x ∈ fastSinIval c X := by
  unfold fastSinIval
  split
  · exact mem_unitIval (Real.neg_one_le_sin _) (Real.sin_le_one _)
  · rename_i hn
    clear hn
    split
    · apply mem_reducedTrig hc Real.abs_sin_sub_sin_le mem_fastSinSer
        (fun u => ⟨Real.neg_one_le_sin u, Real.sin_le_one u⟩) _ hx
      intro u k
      rw [← Real.sin_add_int_mul_pi]
      ring_nf
    · exact mem_clampUnit (mem_sinIval hc hx) ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

theorem mem_fastCosIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    Real.cos x ∈ fastCosIval c X := by
  unfold fastCosIval
  split
  · exact mem_unitIval (Real.neg_one_le_cos _) (Real.cos_le_one _)
  · rename_i hn
    clear hn
    split
    · apply mem_reducedTrig hc Real.abs_cos_sub_cos_le mem_fastCosSer
        (fun u => ⟨Real.neg_one_le_cos u, Real.cos_le_one u⟩) _ hx
      intro u k
      rw [← Real.cos_add_int_mul_pi]
      ring_nf
    · exact mem_clampUnit (mem_cosIval hc hx) ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

@[expose] public def fastSinhIval (c : Ctx) (X : Ival) : Ival :=
  Ival.divNat (c.prec+8)
    (Ival.sub (c.prec+8) (fastExpIval c X) (fastExpIval c (Ival.neg X))) 2

theorem mem_fastSinhIval (c : Ctx) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    Real.sinh x ∈ fastSinhIval c X := by
  rw [Real.sinh_eq]
  exact Ival.mem_divNat (Ival.mem_sub (mem_fastExpIval c hx)
    (mem_fastExpIval c (Ival.mem_neg hx))) (by norm_num : 0 < (2 : Nat))

@[expose] public def fastCoshIval (c : Ctx) (X : Ival) : Ival :=
  Ival.divNat (c.prec+8)
    (Ival.add (c.prec+8) (fastExpIval c X) (fastExpIval c (Ival.neg X))) 2

theorem mem_fastCoshIval (c : Ctx) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    Real.cosh x ∈ fastCoshIval c X := by
  rw [Real.cosh_eq]
  exact Ival.mem_divNat (Ival.mem_add (mem_fastExpIval c hx)
    (mem_fastExpIval c (Ival.mem_neg hx))) (by norm_num : 0 < (2 : Nat))

@[expose] public def fastSinBox (c : Ctx) (Z : CBox) : CBox :=
  ⟨Ival.mul c.prec (fastSinIval c Z.re) (fastCoshIval c Z.im),
   Ival.mul c.prec (fastCosIval c Z.re) (fastSinhIval c Z.im)⟩

theorem mem_fastSinBox {c : Ctx} (hc : c.Valid) {z : ℂ} {Z : CBox} (hz : z ∈ Z) :
    Complex.sin z ∈ fastSinBox c Z := by
  show (Complex.sin z).re ∈ _ ∧ (Complex.sin z).im ∈ _
  rw [Complex.sin_re_of, Complex.sin_im_of]
  exact ⟨Ival.mem_mul (mem_fastSinIval hc hz.1) (mem_fastCoshIval c hz.2),
    Ival.mem_mul (mem_fastCosIval hc hz.1) (mem_fastSinhIval c hz.2)⟩

@[expose] public def fastCosBox (c : Ctx) (Z : CBox) : CBox :=
  ⟨Ival.mul c.prec (fastCosIval c Z.re) (fastCoshIval c Z.im),
   Ival.neg (Ival.mul c.prec (fastSinIval c Z.re) (fastSinhIval c Z.im))⟩

theorem mem_fastCosBox {c : Ctx} (hc : c.Valid) {z : ℂ} {Z : CBox} (hz : z ∈ Z) :
    Complex.cos z ∈ fastCosBox c Z := by
  show (Complex.cos z).re ∈ _ ∧ (Complex.cos z).im ∈ _
  rw [Complex.cos_re_of, Complex.cos_im_of]
  exact ⟨Ival.mem_mul (mem_fastCosIval hc hz.1) (mem_fastCoshIval c hz.2),
    Ival.mem_neg (Ival.mem_mul (mem_fastSinIval hc hz.1) (mem_fastSinhIval c hz.2))⟩

@[expose] public def fastExpBox (c : Ctx) (Z : CBox) : CBox :=
  let E := fastExpIval c Z.re
  ⟨Ival.mul c.prec E (fastCosIval c Z.im), Ival.mul c.prec E (fastSinIval c Z.im)⟩

theorem mem_fastExpBox {c : Ctx} (hc : c.Valid) {z : ℂ} {Z : CBox} (hz : z ∈ Z) :
    Complex.exp z ∈ fastExpBox c Z := by
  show (Complex.exp z).re ∈ _ ∧ (Complex.exp z).im ∈ _
  rw [Complex.exp_re, Complex.exp_im]
  exact ⟨Ival.mem_mul (mem_fastExpIval c hz.1) (mem_fastCosIval hc hz.2),
    Ival.mem_mul (mem_fastExpIval c hz.1) (mem_fastSinIval hc hz.2)⟩

end Lynth.Interval.Integral
