import Lynth.Interval.Fns.Special.Common

namespace Lynth.Interval.Fns

open SpecialFunctions Integral

def erfScale (c : Ctx) : Ival :=
  Ival.div c.prec (Ival.ofRat c.prec 2) (Ival.sqrt c.prec c.pi)

theorem mem_erfScale {c : Ctx} (hc : c.Valid) :
    2 / Real.sqrt Real.pi ∈ erfScale c := by
  exact Ival.mem_div (by simpa using Ival.mem_ofRat c.prec 2) (Ival.mem_sqrt hc.pi_mem)

def erfPositive (c : Ctx) (x : ℚ) : Ival :=
  if 1 < x && (c.prec+16 : ℚ) ≤ x*x then
    specialWiden c.prec Ival.one
      (Ival.div c.prec (fastExpIval c (Ival.ofRat (c.prec+16) (-x*x)))
        (Ival.ofRat c.prec x))
  else
    let p := specialPrec c.prec .erf |x|
    Ival.mul p (Ival.mul p (erfScale c) (Ival.ofRat p x))
      (specialSeriesR p .erf (-x^2))

/-- Evaluate negative inputs by oddness; large positive inputs use a Gaussian tail. -/
def erfPoint (c : Ctx) (x : ℚ) : Ival :=
  if x < 0 then Ival.neg (erfPositive c (-x)) else erfPositive c x

theorem mem_erfPositive {c : Ctx} (hc : c.Valid) (x : ℚ) :
    Real.erf (x : ℝ) ∈ erfPositive c x := by
  unfold erfPositive
  split
  · rename_i h
    have hxq : 1 < x := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have hx : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_trans (by norm_num : (0 : ℚ) < 1) hxq)
    apply mem_specialWiden Ival.mem_one
      (Ival.mem_div (mem_fastExpIval c (Ival.mem_ofRat _ (-x*x))) (Ival.mem_ofRat _ x))
    simpa [pow_two] using erf_tail (x : ℝ) hx
  · let p := specialPrec c.prec .erf |x|
    have h := Ival.mem_mul (p := p) (Ival.mem_mul (p := p) (mem_erfScale hc) (Ival.mem_ofRat p x))
      (mem_specialSeriesR p .erf (-x^2))
    push_cast at h
    exact h

theorem mem_erfPoint {c : Ctx} (hc : c.Valid) (x : ℚ) :
    Real.erf (x : ℝ) ∈ erfPoint c x := by
  unfold erfPoint
  split
  · simpa only [Rat.cast_neg, erf_odd, neg_neg] using Ival.mem_neg (mem_erfPositive hc (-x))
  · exact mem_erfPositive hc x

def erfIval (c : Ctx) (X : Ival) : Ival :=
  match X.mid with
  | some m => specialWiden c.prec (erfPoint c m.toRat)
      (Ival.mul c.prec (Ival.ofRat c.prec 2) (Ival.abs (Ival.sub c.prec X (Ival.pt m))))
  | none => Ival.ofRats c.prec (-1) 1

theorem mem_erfIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    Real.erf x ∈ erfIval c X := by
  unfold erfIval
  split
  · exact mem_specialWiden (mem_erfPoint hc _)
      (Ival.mem_mul (by simpa using Ival.mem_ofRat c.prec 2)
        (Ival.mem_abs (Ival.mem_sub hx (Ival.mem_pt _)))) (real_lipschitz x _).1
  · have h := erf_range x
    exact Ival.mem_ofRats (by simpa using h.1) (by simpa using h.2)

def erfBoxPoint (c : Ctx) (a b : ℚ) : CBox :=
  let p := specialPrec c.prec .erf (|a|+|b|)
  let z := rationalBox p a b
  let q := specialPower .erf a b
  CBox.mul p (CBox.mul p (CBox.ofReal (erfScale c)) z)
    (specialSeriesC p .erf q.1 q.2)

theorem mem_erfBoxPoint {c : Ctx} (hc : c.Valid) (a b : ℚ) :
    Complex.erf ((a : ℂ)+(b : ℂ)*Complex.I) ∈ erfBoxPoint c a b := by
  have h := mem_specialSeriesC (specialPrec c.prec .erf (|a|+|b|)) .erf
    (specialPower .erf a b).1 (specialPower .erf a b).2
  rw [specialPower_cast] at h
  exact CBox.mem_mul (CBox.mem_mul (CBox.mem_ofReal (mem_erfScale hc))
    (mem_rationalBox _ a b)) h

/-- Broad rectangles use the vertical-integral bound; narrow boxes evaluate at
an exact rational midpoint and propagate the analytic derivative bound. -/
def erfCBox (c : Ctx) (Z : CBox) : CBox :=
  match Z.re.mid, Z.im.mid with
  | some a, some b =>
    let m := rationalBox c.prec a.toRat b.toRat
    let r := Ival.add c.prec (CBox.norm c.prec Z) (CBox.norm c.prec m)
    let e := Ival.mul c.prec (Ival.mul c.prec (Ival.ofRat c.prec 2)
      (fastExpIval c (Ival.sq c.prec r))) (CBox.norm c.prec (CBox.sub c.prec Z m))
    specialWidenC c.prec (erfBoxPoint c a.toRat b.toRat) e
  | _, _ => CBox.top


theorem mem_erfCBox {c : Ctx} (hc : c.Valid) {z : ℂ} {Z : CBox} (hz : z ∈ Z) :
    Complex.erf z ∈ erfCBox c Z := by
  unfold erfCBox
  split
  · rename_i a b _ _
    have hm := mem_rationalBox c.prec a.toRat b.toRat
    exact mem_specialWidenC (mem_erfBoxPoint hc _ _)
      (Ival.mem_mul (Ival.mem_mul (by simpa using Ival.mem_ofRat c.prec 2)
        (mem_fastExpIval c (Ival.mem_sq (Ival.mem_add (CBox.mem_norm hz) (CBox.mem_norm hm)))))
        (CBox.mem_norm (CBox.mem_sub hz hm))) (complex_lipschitz_pair z _).1
  · exact CBox.mem_top _

@[lynth_cfn] def erfR : Fn1 .real .real where
  name := "erf"
  graph x y := y = Real.erf x
  exu := exu_eq _
  ev := erfIval
  sound := fun _ _ _ _ hc hy hx => by cases hy; exact mem_erfIval hc hx
  cost := 500000

@[lynth_cfn] def erfC : Fn1 .cplx .cplx where
  name := "erf"
  graph x y := y = Complex.erf x
  exu := exu_eq _
  ev := erfCBox
  sound := fun _ _ _ _ hc hy hx => by cases hy; exact mem_erfCBox hc hx
  cost := 1000000

end Lynth.Interval.Fns
