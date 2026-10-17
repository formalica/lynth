import Lynth.Interval.Integral.Eval
import Lynth.Interval.Integral.Math.Oscillatory

namespace Lynth.Interval.Integral

open Intgrl

def reciprocalSine (e : Term) : Option {ω : ℚ //
    ∀ x : ℝ, e.real x = Real.sin ((ω : ℝ)/x)} :=
  match e with
  | .unary .sin (.unary .inv .var) =>
    some ⟨1, by intro x; simp [Term.real, Unary.real, one_div]⟩
  | .unary .sin (.binary .div (.rat ω) .var) =>
    some ⟨ω, by intro x; rfl⟩
  | _ => none

structure OscillatoryModel (e : Term) where
  degree : ℕ
  frequency : ℚ
  agrees : ∀ x : ℝ, e.real x = x^degree * Real.sin ((frequency : ℝ)/x)

def oscillatoryModel (e : Term) : Option (OscillatoryModel e) := do
  match he : e with
  | .binary .mul .var s =>
    let ⟨ω,hω⟩ ← reciprocalSine s
    return ⟨1,ω,by
      intro x
      rw [he]
      change x*s.real x = x^1 * Real.sin ((ω : ℝ)/x)
      rw [hω x, pow_one]⟩
  | .binary .mul (.pow .var n) s =>
    let ⟨ω,hω⟩ ← reciprocalSine s
    return ⟨n,ω,by
      intro x
      rw [he]
      exact congrArg (x^n * ·) (hω x)⟩
  | _ =>
    let ⟨ω,hω⟩ ← reciprocalSine e
    return ⟨0,ω,by intro x; simpa using hω x⟩

/-- A genuine integral enclosure, using cancellation rather than a
pointwise enclosure. Only used on a panel whose left endpoint is zero. -/
def oscillatoryPanel (c : Ctx) (e : Term) (a b : Dy) : Option Ival := do
  if !a.isZero || !b.isNonneg then none else do
    let m ← oscillatoryModel e
    if m.frequency == 0 || m.degree > 256 then none else do
      let bound := Ival.div c.prec
        (Ival.mul c.prec (Ival.ofRat c.prec 2) (Ival.npow c.prec (Ival.pt b) (m.degree+2)))
        (Ival.ofRat c.prec |m.frequency|)
      let err ← bound.hi
      return ⟨some err.neg, some err⟩

theorem oscillatoryPanel_sound {c : Ctx} {e : Term} {a b : Dy} {I : Ival}
    (h : oscillatoryPanel c e a b = some I) :
    IntervalIntegrable e.real MeasureTheory.volume a.toReal b.toReal ∧
      (∫ x in a.toReal..b.toReal, e.real x) ∈ I := by
  unfold oscillatoryPanel at h
  split at h
  · simp at h
  · rename_i hab
    have hs : a.isZero = true ∧ b.isNonneg = true := by
      cases ha : a.isZero <;> cases hb : b.isNonneg <;> simp_all
    have ha : a.toReal = 0 := by
      have hz : a.mantissa = 0 := by simpa [Dy.isZero] using hs.1
      rw [Dy.toReal_def, Vendor.Dyadic.toRat_eq, hz]
      simp
    have hb : 0 ≤ b.toReal := by
      exact Rat.cast_nonneg.mpr ((Dy.isNonneg_iff b).mp hs.2)
    cases hm : oscillatoryModel e with
    | none => simp [hm] at h
    | some m =>
      simp only [hm, bind, Option.bind] at h
      split at h
      · simp at h
      · rename_i hgood
        have hω : m.frequency ≠ 0 := by
          intro hz
          simp [hz] at hgood
        have hh := reciprocal_sin_endpoint m.degree
          (ω := (m.frequency : ℝ)) (δ := b.toReal) (by exact_mod_cast hω) hb
        have hf : e.real = fun x : ℝ => x^m.degree * Real.sin ((m.frequency : ℝ)/x) :=
          funext m.agrees
        rw [← hf] at hh
        let bound := Ival.div c.prec
          (Ival.mul c.prec (Ival.ofRat c.prec 2)
            (Ival.npow c.prec (Ival.pt b) (m.degree+2)))
          (Ival.ofRat c.prec |m.frequency|)
        have hv : 2*b.toReal^(m.degree+2)/|(m.frequency : ℝ)| ∈ bound := by
          apply Ival.mem_div
          · exact Ival.mem_mul (Ival.mem_ofRat _ _) (Ival.mem_npow (Ival.mem_pt b) _)
          · simpa using Ival.mem_ofRat c.prec |m.frequency|
        cases he : bound.hi with
        | none => simp [bound, he] at h
        | some err =>
          have hi : I = ⟨some err.neg, some err⟩ := by
            simpa only [bound, he, Option.bind_some, pure, Option.some.injEq] using h.symm
          refine ⟨by simpa [ha] using hh.1, ?_⟩
          rw [hi, ha]
          have hn := abs_le.mp (hh.2.trans (hv.2 err he))
          simpa [Ival.mem_mk, Dy.toReal_def] using hn

end Lynth.Interval.Integral
