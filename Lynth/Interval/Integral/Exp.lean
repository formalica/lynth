import Lynth.Interval.Integral.Math.FixedExp
import Lynth.Interval.Fns.Exp

/-! Integration-local fixed-point exponential kernels. -/

namespace Lynth.Interval.Integral

open Fns

def fastExpSmall (w : Nat) (a : Dy) : Ival :=
  if isSmallArg a then
    let p := w+8
    let (lo,hi) := Intgrl.fixedExpBounds p a.toRat
    ⟨some ⟨lo,-(p : Int)⟩, some ⟨hi,-(p : Int)⟩⟩
  else ⟨some Dy.zero,none⟩

theorem mem_fastExpSmall (w : Nat) (a : Dy) : Real.exp a.toReal ∈ fastExpSmall w a := by
  unfold fastExpSmall
  split
  · rename_i ha
    have h := Intgrl.fixedExpBounds_sound (w+8) (by omega) a.toRat
      (abs_le_half_of_isSmallArg ha)
    simpa only [Ival.mem_mk, Ival.loLe_some, Ival.leHi_some, Dy.toReal_def,
      Dy.toRat_mk, Rat.cast_mul, Rat.cast_intCast, Rat.cast_zpow, Rat.cast_ofNat] using h
  · exact ⟨by simpa [Dy.toReal_def] using (Real.exp_pos a.toReal).le, by simp⟩

def fastExpPt (w : Nat) (a : Dy) : Ival :=
  let s := expRed a
  sqIter (w+s) (fastExpSmall (w+s+8) (Dy.scale2 a (-(s : Int)))) s

theorem mem_fastExpPt (w : Nat) (a : Dy) : Real.exp a.toReal ∈ fastExpPt w a := by
  unfold fastExpPt
  set s := expRed a
  have ha : a.toReal = ((2^s : Nat) : ℝ) * (Dy.scale2 a (-(s : Int))).toReal := by
    simp only [Dy.toReal_def, Dy.toRat_scale2]
    push_cast
    rw [zpow_neg, zpow_natCast]
    field_simp
  rw [ha, Real.exp_nat_mul]
  exact mem_sqIter (mem_fastExpSmall _ _) s

def fastExpIval (c : Ctx) (X : Ival) : Ival :=
  let w := c.prec+8
  ⟨some (match X.lo with
      | some a => (fastExpPt w a).lo.getD Dy.zero
      | none => Dy.zero),
   match X.hi with
      | some b => (fastExpPt w b).hi
      | none => none⟩

theorem mem_fastExpIval (c : Ctx) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    Real.exp x ∈ fastExpIval c X := by
  obtain ⟨hx1,hx2⟩ := hx
  refine ⟨?_,?_⟩
  · simp only [fastExpIval, Ival.loLe_some]
    split
    · rename_i a ha
      have hm := mem_fastExpPt (c.prec+8) a
      cases hl : (fastExpPt (c.prec+8) a).lo with
      | none => simpa [Dy.toReal_def] using (Real.exp_pos x).le
      | some l =>
        simp only [Option.getD_some]
        exact (hm.1 l hl).trans (Real.exp_le_exp.mpr (hx1 a ha))
    · simpa [Dy.toReal_def] using (Real.exp_pos x).le
  · simp only [fastExpIval]
    split
    · rename_i b hb
      exact fun h hh => (Real.exp_le_exp.mpr (hx2 b hb)).trans
        ((mem_fastExpPt (c.prec+8) b).2 h hh)
    · simp

end Lynth.Interval.Integral
