module

public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Lynth.Interval.Core.Ctx
public import Lynth.Interval.Fns.ComplexElem
public import Lynth.Interval.Fns.Elem
public import Lynth.Interval.Num.CBox
public import Lynth.Interval.Num.Dy
public import Lynth.Interval.Num.Ival
public import Lynth.Interval.Series.Tail
public import Lynth.Interval.Vendor.Dyadic
import all Lynth.Interval.Fns.ComplexElem
import Mathlib.Analysis.RCLike.Sqrt

/-! Rational powers with inexpensive, outward-rounded half-integer kernels. -/

namespace Lynth.Interval.Integral

open Fns

@[expose] public def naturalPowerR (p : Nat) (X : Ival) (n : Nat) : Ival :=
  if n = 0 then Ival.one else if n = 1 then X else if n = 2 then Ival.sq p X
  else if n = 3 then Ival.mul p X (Ival.sq p X) else Ival.npow p X n

theorem mem_naturalPowerR {p : Nat} {x : ℝ} {X : Ival} (hx : x ∈ X) (n : Nat) :
    x^n ∈ naturalPowerR p X n := by
  unfold naturalPowerR
  split
  · rename_i h; subst n; simpa using Ival.mem_one
  · split
    · rename_i h; subst n; simpa using hx
    · split
      · rename_i h; subst n; exact Ival.mem_sq hx
      · split
        · rename_i h; subst n
          simpa only [← pow_succ'] using Ival.mem_mul (p := p) hx (Ival.mem_sq (p := p) hx)
        · exact Ival.mem_npow hx n

/-- Reuse the real square-root component in the imaginary component.
This is definitionally the existing principal-square-root enclosure. -/
@[expose] public def sharedSqrtBox (c : Ctx) (B : CBox) : CBox :=
  match B.re.lo with
  | some xl =>
    if 0 < xl.toRat then
      let root := Ival.sqrt c.prec
        (Ival.divNat c.prec (Ival.add c.prec (CBox.norm c.prec B) B.re) 2)
      ⟨root,Ival.div c.prec B.im (Ival.mul c.prec (Ival.ofRat c.prec 2) root)⟩
    else CBox.top
  | none => CBox.top

theorem mem_sharedSqrtBox (c : Ctx) (hc : c.Valid) {z : ℂ} {B : CBox} (hz : z ∈ B) :
    Complex.sqrt z ∈ sharedSqrtBox c B := mem_sqrtBox c hc hz

/-- Dependency-aware complex squaring. Repeated multiplication loses the
nonnegativity of a real square on boxes crossing the imaginary axis. -/
@[expose] public def squareC (p : Nat) (Z : CBox) : CBox :=
  let product := Ival.mul p Z.re Z.im
  ⟨Ival.sub p (Ival.sq p Z.re) (Ival.sq p Z.im), Ival.add p product product⟩

theorem mem_squareC {p : Nat} {z : ℂ} {Z : CBox} (hz : z ∈ Z) :
    z^2 ∈ squareC p Z := by
  have hr : (z^2).re = z.re^2-z.im^2 := by simp only [pow_two, Complex.mul_re]
  have hi : (z^2).im = z.re*z.im+z.re*z.im := by
    simp only [pow_two, Complex.mul_im]
    ring
  constructor
  · change (z^2).re ∈ Ival.sub p (Ival.sq p Z.re) (Ival.sq p Z.im)
    rw [hr]
    exact Ival.mem_sub (p := p) (Ival.mem_sq (p := p) hz.1) (Ival.mem_sq (p := p) hz.2)
  · change (z^2).im ∈ Ival.add p (Ival.mul p Z.re Z.im) (Ival.mul p Z.re Z.im)
    rw [hi]
    exact Ival.mem_add (p := p) (Ival.mem_mul (p := p) hz.1 hz.2)
      (Ival.mem_mul (p := p) hz.1 hz.2)

@[expose] public def naturalPowerC (p : Nat) (Z : CBox) (n : Nat) : CBox :=
  if n = 1 then Z else if n = 2 then squareC p Z
  else if n = 3 then CBox.mul p Z (squareC p Z) else CBox.npow p Z n

theorem mem_naturalPowerC {p : Nat} {z : ℂ} {Z : CBox} (hz : z ∈ Z) (n : Nat) :
    z^n ∈ naturalPowerC p Z n := by
  unfold naturalPowerC
  split
  · rename_i h; subst n; simpa using hz
  · split
    · rename_i h; subst n; exact mem_squareC hz
    · split
      · rename_i h; subst n
        simpa only [← pow_succ'] using CBox.mem_mul (p := p) hz (mem_squareC (p := p) hz)
      · exact CBox.mem_npow hz n

@[expose] public def intPowerR (p : Nat) (X : Ival) : Int → Ival
  | .ofNat n => naturalPowerR p X n
  | .negSucc n => Ival.inv p (naturalPowerR p X (n + 1))

theorem mem_intPowerR {p : Nat} {x : ℝ} {X : Ival} (hx : x ∈ X) (n : Int) :
    x ^ n ∈ intPowerR p X n := by
  cases n with
  | ofNat n => simpa [intPowerR] using mem_naturalPowerR (p := p) hx n
  | negSucc n => simpa [intPowerR, zpow_negSucc] using
      Ival.mem_inv (p := p) (mem_naturalPowerR (p := p) hx (n + 1))

@[expose] public def intPowerC (p : Nat) (Z : CBox) : Int → CBox
  | .ofNat n => naturalPowerC p Z n
  | .negSucc n => CBox.inv p (naturalPowerC p Z (n + 1))

theorem mem_intPowerC {p : Nat} {z : ℂ} {Z : CBox} (hz : z ∈ Z) (n : Int) :
    z ^ n ∈ intPowerC p Z n := by
  cases n with
  | ofNat n => simpa [intPowerC] using mem_naturalPowerC (p := p) hz n
  | negSucc n => simpa [intPowerC, zpow_negSucc] using
      CBox.mem_inv (p := p) (mem_naturalPowerC (p := p) hz (n + 1))

/-- Positive half-integer powers use a square root and integer powers.
Other inputs retain the general real-power enclosure. -/
@[expose] public def rationalPowerR (c : Ctx) (X : Ival) (q : ℚ) : Ival :=
  if q.den = 2 ∧ X.pos = true then intPowerR c.prec (Ival.sqrt c.prec X) q.num
  else rpowIval c X (Ival.ofRat c.prec q)

theorem mem_rationalPowerR {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival}
    (hx : x ∈ X) (q : ℚ) : x ^ (q : ℝ) ∈ rationalPowerR c X q := by
  unfold rationalPowerR
  split
  · rename_i h
    have hq : (q : ℝ) = (q.num : ℝ) / 2 := by
      rw [Rat.cast_def, h.1]
      norm_num
    rw [hq, Real.rpow_div_two_eq_sqrt _ (Ival.pos_of h.2 hx).le, Real.rpow_intCast]
    exact mem_intPowerR (Ival.mem_sqrt hx) q.num
  · exact mem_rpowIval hc hx (Ival.mem_ofRat _ _)

/-- The principal complex square root agrees with the half-integer power,
including for negative integer exponents. -/
@[expose] public def rationalPowerC (c : Ctx) (Z : CBox) (q : ℚ) : CBox :=
  if q.den = 2 then intPowerC c.prec (sharedSqrtBox c Z) q.num
  else expBox c (CBox.mul c.prec (logBox c Z) (CBox.ofReal (Ival.ofRat c.prec q)))

theorem mem_rationalPowerC {c : Ctx} (hc : c.Valid) {z : ℂ} {Z : CBox}
    (hz : z ∈ Z) (hne : z ≠ 0) (q : ℚ) :
    z ^ ((q : ℝ) : ℂ) ∈ rationalPowerC c Z q := by
  unfold rationalPowerC
  split
  · rename_i h
    have hq : ((q : ℝ) : ℂ) = (q.num : ℂ) / 2 := by
      rw [Rat.cast_def, h]
      push_cast
      rfl
    have he : z ^ ((q.num : ℂ) / 2) = (Complex.sqrt z) ^ q.num := by
      rw [Complex.sqrt, ← Complex.cpow_mul_int]
      congr 1
      ring
    rw [hq, he]
    exact mem_intPowerC (mem_sharedSqrtBox c hc hz) q.num
  · rw [Complex.cpow_def_of_ne_zero hne]
    exact mem_expBox c hc (CBox.mem_mul (mem_logBox c hc hz)
      (CBox.mem_ofReal (Ival.mem_ofRat _ _)))

end Lynth.Interval.Integral
