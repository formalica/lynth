import Lynth.Interval.Integral.SpecialMagnitude
import Lynth.Interval.Integral.Math.ComplexMagnitude

/-! Direct complex modulus bounds for an outer sine or cosine. -/

namespace Lynth.Interval.Integral

open Intgrl Fns

def trigMagnitude (c : Ctx) (Z : CBox) : Option Dy := do
  let m ← (Ival.abs Z.im).hi
  if !Dy.leB m (Dy.ofNat 16384) then none else (fastExpPt (c.prec+8) m).hi

theorem trigMagnitude_sound {c : Ctx} {Z : CBox} {z : ℂ} {M : Dy}
    (hz : z ∈ Z) (h : trigMagnitude c Z = some M) : Real.exp |z.im| ≤ M.toReal := by
  unfold trigMagnitude at h
  cases hm : (Ival.abs Z.im).hi with
  | none => simp [hm] at h
  | some m =>
    simp only [hm, bind, Option.bind] at h
    change (if !Dy.leB m (Dy.ofNat 16384) then none else
      (fastExpPt (c.prec+8) m).hi) = some M at h
    split at h
    · simp at h
    · exact (Real.exp_le_exp.mpr ((Ival.mem_abs hz.2).2 m hm)).trans
        ((mem_fastExpPt (c.prec+8) m).2 M h)

def expMagnitude (c : Ctx) (Z : CBox) : Option Dy := do
  let m ← Z.re.hi
  if !Dy.leB m (Dy.ofNat 16384) then none else (fastExpPt (c.prec+8) m).hi

theorem expMagnitude_sound {c : Ctx} {Z : CBox} {z : ℂ} {M : Dy}
    (hz : z ∈ Z) (h : expMagnitude c Z = some M) : ‖Complex.exp z‖ ≤ M.toReal := by
  unfold expMagnitude at h
  cases hm : Z.re.hi with
  | none => simp [hm] at h
  | some m =>
    simp only [hm, bind, Option.bind] at h
    split at h
    · simp at h
    · rw [Complex.norm_exp]
      exact (Real.exp_le_exp.mpr (hz.1.2 m hm)).trans
        ((mem_fastExpPt (c.prec+8) m).2 M h)

def analyticMagnitude (c : Ctx) (e : Term) (Z : CBox) : Option Dy :=
  match e with
  | .unary .sin a | .unary .cos a => trigMagnitude c (evalC c a Z)
  | .unary .exp a => expMagnitude c (evalC c a Z)
  | .unary .erf a => specialMagnitude c .erf (evalC c a Z)
  | .unary .si a => specialMagnitude c .si (evalC c a Z)
  | .unary .eta a => specialMagnitude c .eta (evalC c a Z)
  | .unary .airyAi a => specialMagnitude c .airyAi (evalC c a Z)
  | .unary .neg a => analyticMagnitude c a Z
  | .binary .mul a b => do
    let A ← analyticMagnitude c a Z
    let B ← analyticMagnitude c b Z
    return Dy.mulU c.prec A B
  | _ => (CBox.norm c.prec (evalC c e Z)).hi

theorem analyticMagnitude_sound {c : Ctx} (hc : c.Valid) {e : Term} {Z : CBox}
    {z : ℂ} {M : Dy} (hr : regularCheck c e Z = true) (hz : z ∈ Z)
    (h : analyticMagnitude c e Z = some M) : ‖e.complex z‖ ≤ M.toReal := by
  induction e generalizing M with
  | unary op a ih =>
    cases op with
    | sin =>
      exact (norm_sin_le_exp_abs_im _).trans
        (trigMagnitude_sound (evalC_sound hc a (Bool.and_eq_true_iff.mp hr).1 hz) h)
    | cos =>
      exact (norm_cos_le_exp_abs_im _).trans
        (trigMagnitude_sound (evalC_sound hc a (Bool.and_eq_true_iff.mp hr).1 hz) h)
    | exp =>
      exact expMagnitude_sound
        (evalC_sound hc a (Bool.and_eq_true_iff.mp hr).1 hz) h
    | erf | si | eta | airyAi =>
      exact specialMagnitude_sound hc _
        (evalC_sound hc a (Bool.and_eq_true_iff.mp hr).1 hz) h
    | neg =>
      simpa only [Term.complex, Unary.complex, norm_neg] using
        ih (Bool.and_eq_true_iff.mp hr).1 h
    | _ => exact (CBox.mem_norm (p := c.prec) (evalC_sound hc _ hr hz)).2 M h
  | binary op a b ha hb =>
    cases op with
    | mul =>
      obtain ⟨hab,_⟩ := Bool.and_eq_true_iff.mp hr
      obtain ⟨hra,hrb⟩ := Bool.and_eq_true_iff.mp hab
      unfold analyticMagnitude at h
      cases hA : analyticMagnitude c a Z with
      | none => simp [hA] at h
      | some A =>
        cases hB : analyticMagnitude c b Z with
        | none => simp [hA,hB] at h
        | some B =>
          simp only [hA,hB,bind,Option.bind,pure,Option.some.injEq] at h
          subst M
          have h1 := ha hra hA
          have h2 := hb hrb hB
          change ‖a.complex z * b.complex z‖ ≤ _
          rw [norm_mul]
          refine (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)).trans ?_
          simpa only [Dy.toReal_def, Rat.cast_mul] using
            (show ((A.toRat*B.toRat : ℚ) : ℝ) ≤ ((Dy.mulU c.prec A B).toRat : ℝ) from
              Rat.cast_le.mpr (Dy.le_mulU c.prec A B))
    | _ => exact (CBox.mem_norm (p := c.prec) (evalC_sound hc _ hr hz)).2 M h
  | _ => exact (CBox.mem_norm (p := c.prec) (evalC_sound hc _ hr hz)).2 M h

end Lynth.Interval.Integral
