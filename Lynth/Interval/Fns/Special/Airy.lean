import Lynth.Interval.Fns.Special.Common
import Lynth.Interval.Core.Const

namespace Lynth.Interval.Fns

open SpecialFunctions Integral

/-- A 1328-bit enclosure covers the common path. Higher precisions compute the
normalizing constants from Gamma, with a fresh context at the work precision. -/
def airyConstants (p : ℕ) : Ival × Ival :=
  if p ≤ 1200 then
    (Ival.ofRats p (airyConstA / (airyConstScale : ℚ)) ((airyConstA+1) / (airyConstScale : ℚ)),
      Ival.ofRats p (airyConstB / (airyConstScale : ℚ)) ((airyConstB+1) / (airyConstScale : ℚ)))
  else
    let c := Ctx.make (p+32)
    let A := Ival.inv p (Ival.mul p (rpowIval c (Ival.ofRat p 3) (Ival.ofRat p (2/3)))
      (gammaIval c (Ival.ofRat p (2/3))))
    let B := Ival.neg (Ival.inv p (Ival.mul p (rpowIval c (Ival.ofRat p 3) (Ival.ofRat p (1/3)))
      (gammaIval c (Ival.ofRat p (1/3)))))
    (A,B)

theorem mem_airyConstants (p : ℕ) :
    airyA ∈ (airyConstants p).1 ∧ airyB ∈ (airyConstants p).2 := by
  unfold airyConstants
  split
  · constructor
    · apply Ival.mem_ofRats <;> push_cast <;>
        first | exact airy_constants.1 | exact airy_constants.2.1
    · apply Ival.mem_ofRats <;> push_cast
      · exact airy_constants.2.2.1
      · exact airy_constants.2.2.2
  · constructor
    · simpa [airyA, one_div] using Ival.mem_inv
        (Ival.mem_mul (mem_rpowIval (Ctx.make_valid _) (Ival.mem_ofRat _ 3)
          (Ival.mem_ofRat _ (2/3))) (mem_gammaIval (Ctx.make_valid _) (Ival.mem_ofRat _ (2/3))))
    · simpa [airyB, one_div, neg_div] using Ival.mem_neg (Ival.mem_inv
        (Ival.mem_mul (mem_rpowIval (Ctx.make_valid _) (Ival.mem_ofRat _ 3)
          (Ival.mem_ofRat _ (1/3))) (mem_gammaIval (Ctx.make_valid _) (Ival.mem_ofRat _ (1/3)))))

def airyAiPoint (c : Ctx) (x : ℚ) : Ival :=
  let p := specialPrec c.prec .airy0 |x|
  let (a,b) := airyConstants p
  Ival.add p (Ival.mul p a (specialSeriesR p .airy0 (x^3)))
    (Ival.mul p (Ival.mul p b (Ival.ofRat p x)) (specialSeriesR p .airy1 (x^3)))

theorem mem_airyAiPoint (c : Ctx) (x : ℚ) :
    Real.airyAi (x : ℝ) ∈ airyAiPoint c x := by
  let p := specialPrec c.prec .airy0 |x|
  have hc := mem_airyConstants p
  have h := Ival.mem_add (p := p) (Ival.mem_mul (p := p) hc.1 (mem_specialSeriesR p .airy0 (x^3)))
    (Ival.mem_mul (p := p) (Ival.mem_mul (p := p) hc.2 (Ival.mem_ofRat p x))
      (mem_specialSeriesR p .airy1 (x^3)))
  push_cast at h
  exact h

def airyAiIval (c : Ctx) (X : Ival) : Ival :=
  match X.mid with
  | some m =>
    let r := Ival.add c.prec (Ival.abs X) (Ival.abs (Ival.pt m))
    specialWiden c.prec (airyAiPoint c m.toRat)
      (Ival.mul c.prec (Ival.mul c.prec (Ival.add c.prec (Ival.ofRat c.prec 2) r)
        (fastExpIval c r)) (Ival.abs (Ival.sub c.prec X (Ival.pt m))))
  | none => Ival.ofRats c.prec (-1) 1

theorem mem_airyAiIval (c : Ctx) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    Real.airyAi x ∈ airyAiIval c X := by
  unfold airyAiIval
  split
  · rename_i m _
    have hm := Ival.mem_pt m
    have hr := Ival.mem_add (p := c.prec) (Ival.mem_abs hx) (Ival.mem_abs hm)
    apply mem_specialWiden (mem_airyAiPoint c _)
      (Ival.mem_mul (Ival.mem_mul (Ival.mem_add (Ival.mem_ofRat c.prec 2) hr)
        (mem_fastExpIval c hr)) (Ival.mem_abs (Ival.mem_sub hx hm)))
    simpa [add_assoc, Dy.toReal_def] using (real_lipschitz x _).2.2
  · have h := abs_le.mp (airy_real_bound x)
    exact Ival.mem_ofRats (by simpa using h.1) (by simpa using h.2)

def airyAiBoxPoint (c : Ctx) (a b : ℚ) : CBox :=
  let p := specialPrec c.prec .airy0 (|a|+|b|)
  let (A,B) := airyConstants p
  let q := specialPower .airy0 a b
  CBox.add p (CBox.mul p (CBox.ofReal A) (specialSeriesC p .airy0 q.1 q.2))
    (CBox.mul p (CBox.mul p (CBox.ofReal B) (rationalBox p a b))
      (specialSeriesC p .airy1 q.1 q.2))

theorem mem_airyAiBoxPoint (c : Ctx) (a b : ℚ) :
    Complex.airyAi ((a : ℂ)+(b : ℂ)*Complex.I) ∈ airyAiBoxPoint c a b := by
  have h := mem_airyConstants (specialPrec c.prec .airy0 (|a|+|b|))
  have h0 := mem_specialSeriesC (specialPrec c.prec .airy0 (|a|+|b|)) .airy0
    (specialPower .airy0 a b).1 (specialPower .airy0 a b).2
  have h1 := mem_specialSeriesC (specialPrec c.prec .airy0 (|a|+|b|)) .airy1
    (specialPower .airy0 a b).1 (specialPower .airy0 a b).2
  rw [specialPower_cast] at h0 h1
  exact CBox.mem_add (CBox.mem_mul (CBox.mem_ofReal h.1) h0)
    (CBox.mem_mul (CBox.mem_mul (CBox.mem_ofReal h.2) (mem_rationalBox _ a b)) h1)

def airyAiCBox (c : Ctx) (Z : CBox) : CBox :=
  match Z.re.mid, Z.im.mid with
  | some a, some b =>
    let m := rationalBox c.prec a.toRat b.toRat
    let r := Ival.add c.prec (CBox.norm c.prec Z) (CBox.norm c.prec m)
    let e := Ival.mul c.prec
      (Ival.mul c.prec (Ival.sq c.prec (Ival.add c.prec (Ival.ofRat c.prec 2) r))
        (fastExpIval c (Ival.add c.prec (Ival.sq c.prec r) Ival.one)))
      (CBox.norm c.prec (CBox.sub c.prec Z m))
    specialWidenC c.prec (airyAiBoxPoint c a.toRat b.toRat) e
  | _, _ => CBox.top

theorem mem_airyAiCBox (c : Ctx) {z : ℂ} {Z : CBox} (hz : z ∈ Z) :
    Complex.airyAi z ∈ airyAiCBox c Z := by
  unfold airyAiCBox
  split
  · rename_i a b _ _
    have hm := mem_rationalBox c.prec a.toRat b.toRat
    have hr := Ival.mem_add (p := c.prec) (CBox.mem_norm (p := c.prec) hz) (CBox.mem_norm (p := c.prec) hm)
    apply mem_specialWidenC (mem_airyAiBoxPoint c _ _)
      (Ival.mem_mul (Ival.mem_mul (Ival.mem_sq (Ival.mem_add (Ival.mem_ofRat c.prec 2) hr))
        (mem_fastExpIval c (Ival.mem_add (Ival.mem_sq hr) Ival.mem_one)))
        (CBox.mem_norm (CBox.mem_sub hz hm)))
    simpa only [Rat.cast_ofNat, add_assoc] using (complex_lipschitz_pair z _).2.2
  · exact CBox.mem_top _

@[lynth_cfn] def airyAiR : Fn1 .real .real where
  name := "airyAi"
  graph x y := y = Real.airyAi x
  exu := exu_eq _
  ev := airyAiIval
  sound := fun c _ _ _ _ hy hx => by cases hy; exact mem_airyAiIval c hx
  cost := 500000

@[lynth_cfn] def airyAiC : Fn1 .cplx .cplx where
  name := "airyAi"
  graph x y := y = Complex.airyAi x
  exu := exu_eq _
  ev := airyAiCBox
  sound := fun c _ _ _ _ hy hx => by cases hy; exact mem_airyAiCBox c hx
  cost := 1000000

end Lynth.Interval.Fns
