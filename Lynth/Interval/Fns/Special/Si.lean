import Lynth.Interval.Fns.Special.Common

namespace Lynth.Interval.Fns

open SpecialFunctions Integral

def specialHorner (p : ℕ) (xs : List ℚ) (X : Ival) : Ival :=
  match xs with
  | [] => Ival.zero
  | q :: qs => Ival.add p (Ival.ofRat p q) (Ival.mul p X (specialHorner p qs X))

theorem mem_specialHorner {p : ℕ} (xs : List ℚ) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    hornerR xs x ∈ specialHorner p xs X := by
  induction xs with
  | nil => exact Ival.mem_zero
  | cons q qs ih => exact Ival.mem_add (Ival.mem_ofRat p q) (Ival.mem_mul hx ih)

def siAsymptotic (c : Ctx) (x : ℚ) : Ival :=
  let p := c.prec+16
  let n := c.prec/2+8
  let X := Ival.ofRat p x
  let U := Ival.inv p (Ival.sq p X)
  let center := Ival.sub p (Ival.sub p (Ival.divNat p c.pi 2)
    (Ival.mul p (Ival.div p (fastCosIval c X) X) (specialHorner p (siCoeffs n false) U)))
    (Ival.mul p (Ival.div p (fastSinIval c X) (Ival.sq p X))
      (specialHorner p (siCoeffs n true) U))
  let error := Ival.add p
    (Ival.div p (Ival.ofRat p ((2*n).factorial : ℚ)) (Ival.npow p X (2*n+1)))
    (Ival.div p (Ival.ofRat p ((2*n+1).factorial : ℚ)) (Ival.npow p X (2*n+2)))
  specialWiden p center error

theorem mem_siAsymptotic {c : Ctx} (hc : c.Valid) (x : ℚ) (hx : 0 < x) :
    Real.Si (x : ℝ) ∈ siAsymptotic c x := by
  unfold siAsymptotic
  have hX := Ival.mem_ofRat (c.prec+16) x
  apply mem_specialWiden
    (Ival.mem_sub (Ival.mem_sub (by simpa using Ival.mem_divNat hc.pi_mem (n := 2) (by omega))
      (Ival.mem_mul (Ival.mem_div (mem_fastCosIval hc hX) hX)
        (mem_specialHorner _ (Ival.mem_inv (Ival.mem_sq hX)))))
      (Ival.mem_mul (Ival.mem_div (mem_fastSinIval hc hX) (Ival.mem_sq hX))
        (mem_specialHorner _ (Ival.mem_inv (Ival.mem_sq hX)))))
    (Ival.mem_add
      (Ival.mem_div (Ival.mem_ofRat _ _) (Ival.mem_npow hX _))
      (Ival.mem_div (Ival.mem_ofRat _ _) (Ival.mem_npow hX _)))
  simpa only [Rat.cast_natCast] using
    si_asymptotic_horner (x : ℝ) (by exact_mod_cast hx) (c.prec/2+8)

def siPositive (c : Ctx) (x : ℚ) : Ival :=
  if (c.prec+16 : ℚ) ≤ x then siAsymptotic c x
  else
    let p := specialPrec c.prec .si |x|
    Ival.mul p (Ival.ofRat p x) (specialSeriesR p .si (-x^2))

def siPoint (c : Ctx) (x : ℚ) : Ival :=
  if x < 0 then Ival.neg (siPositive c (-x)) else siPositive c x

theorem mem_siPositive {c : Ctx} (hc : c.Valid) (x : ℚ) :
    Real.Si (x : ℝ) ∈ siPositive c x := by
  unfold siPositive
  split
  · rename_i h
    apply mem_siAsymptotic hc x
    have : (0 : ℚ) < (c.prec+16 : ℚ) := by positivity
    exact this.trans_le h
  · let p := specialPrec c.prec .si |x|
    have h := Ival.mem_mul (p := p) (Ival.mem_ofRat p x) (mem_specialSeriesR p .si (-x^2))
    push_cast at h
    exact h

theorem mem_siPoint {c : Ctx} (hc : c.Valid) (x : ℚ) :
    Real.Si (x : ℝ) ∈ siPoint c x := by
  unfold siPoint
  split
  · simpa only [Rat.cast_neg, si_odd, neg_neg] using Ival.mem_neg (mem_siPositive hc (-x))
  · exact mem_siPositive hc x

def siIval (c : Ctx) (X : Ival) : Ival :=
  match X.mid with
  | some m => specialWiden c.prec (siPoint c m.toRat)
      (Ival.abs (Ival.sub c.prec X (Ival.pt m)))
  | none => Ival.top

theorem mem_siIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    Real.Si x ∈ siIval c X := by
  unfold siIval
  split
  · exact mem_specialWiden (mem_siPoint hc _)
      (Ival.mem_abs (Ival.mem_sub hx (Ival.mem_pt _))) (real_lipschitz x _).2.1
  · exact Ival.mem_top _

def siBoxPoint (c : Ctx) (a b : ℚ) : CBox :=
  let p := specialPrec c.prec .si (|a|+|b|)
  let q := specialPower .si a b
  CBox.mul p (rationalBox p a b) (specialSeriesC p .si q.1 q.2)

theorem mem_siBoxPoint (c : Ctx) (a b : ℚ) :
    Complex.Si ((a : ℂ)+(b : ℂ)*Complex.I) ∈ siBoxPoint c a b := by
  have h := mem_specialSeriesC (specialPrec c.prec .si (|a|+|b|)) .si
    (specialPower .si a b).1 (specialPower .si a b).2
  rw [specialPower_cast] at h
  exact CBox.mem_mul (mem_rationalBox _ a b) h

def siCBox (c : Ctx) (Z : CBox) : CBox :=
  match Z.re.mid, Z.im.mid with
  | some a, some b =>
    let m := rationalBox c.prec a.toRat b.toRat
    let r := Ival.add c.prec (CBox.norm c.prec Z) (CBox.norm c.prec m)
    let e := Ival.mul c.prec (fastExpIval c r) (CBox.norm c.prec (CBox.sub c.prec Z m))
    specialWidenC c.prec (siBoxPoint c a.toRat b.toRat) e
  | _, _ => CBox.top

theorem mem_siCBox (c : Ctx) {z : ℂ} {Z : CBox} (hz : z ∈ Z) :
    Complex.Si z ∈ siCBox c Z := by
  unfold siCBox
  split
  · rename_i a b _ _
    have hm := mem_rationalBox c.prec a.toRat b.toRat
    exact mem_specialWidenC (mem_siBoxPoint c _ _)
      (Ival.mem_mul (mem_fastExpIval c (Ival.mem_add (CBox.mem_norm hz) (CBox.mem_norm hm)))
        (CBox.mem_norm (CBox.mem_sub hz hm))) (complex_lipschitz_pair z _).2.1
  · exact CBox.mem_top _

@[lynth_cfn] def siR : Fn1 .real .real where
  name := "Si"
  graph x y := y = Real.Si x
  exu := exu_eq _
  ev := siIval
  sound := fun _ _ _ _ hc hy hx => by cases hy; exact mem_siIval hc hx
  cost := 500000

@[lynth_cfn] def siC : Fn1 .cplx .cplx where
  name := "Si"
  graph x y := y = Complex.Si x
  exu := exu_eq _
  ev := siCBox
  sound := fun c _ _ _ _ hy hx => by cases hy; exact mem_siCBox c hx
  cost := 1000000

end Lynth.Interval.Fns
