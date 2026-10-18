import Lynth.Interval.Integral.NestedBounds
import Lynth.Interval.Integral.Math.NestedAnalysis

/-! Real and complex arithmetic correctness for recursive range bounds. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl Fns

theorem safeExp_sound {c : Ctx} {X : Ival} {x : ℝ} (hx : x ∈ X) :
    Real.exp x ∈ safeExp c X := by
  have hzero : Dy.zero.toReal ≤ Real.exp x := by
    simpa [Dy.toReal_def] using (Real.exp_pos x).le
  cases hhi : X.hi with
  | none => simpa only [safeExp, hhi, Ival.mem_mk, Ival.loLe_some,
      Ival.leHi_none, and_true, Id.run, pure] using hzero
  | some hi =>
    by_cases hcap : Dy.leB hi (Dy.ofNat 16384) = true
    · by_cases htiny : Dy.leB hi (Dy.ofNat (16*c.prec+1024)).neg = true
      · have hle : x ≤ -((16*c.prec+1024 : ℕ) : ℝ) := by
          have hh := (hx.2 hi hhi).trans (Dy.toReal_le_of_leB htiny)
          simpa [Dy.toReal_def] using hh
        have hupper := (Real.exp_le_exp.mpr hle).trans (exp_negative_nat (16*c.prec+1024))
        have heq : safeExp c X = ⟨some Dy.zero,some ⟨1,-(16*c.prec+1024 : ℕ)⟩⟩ := by
          simp only [safeExp, hhi, hcap, htiny, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, Id.run, pure]
        rw [heq]
        exact ⟨fun _ ha => by cases Option.some.inj ha; exact hzero,
          fun _ ha => by cases Option.some.inj ha; simpa [Dy.toReal_def] using hupper⟩
      · have heq : safeExp c X =
            ⟨(match X.lo with
              | none => some Dy.zero
              | some a => if Dy.leB (Dy.ofNat (16*c.prec+1024)).neg a then
                  (expPt (c.prec+8) a).lo else some Dy.zero),
              (expPt (c.prec+8) hi).hi⟩ := by
          simp only [safeExp, hhi, hcap, htiny, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, Id.run, pure]
          cases X.lo <;> rfl
        rw [heq]
        constructor
        · intro l hl
          cases hlo : X.lo with
          | none =>
            have hh : Dy.zero = l := Option.some.inj (by simpa only [hlo] using hl)
            exact hh ▸ hzero
          | some lo =>
            by_cases hlow : Dy.leB (Dy.ofNat (16*c.prec+1024)).neg lo = true
            · have hh : (expPt (c.prec+8) lo).lo = some l := by
                simpa only [hlo, hlow, Bool.false_eq_true, ↓reduceIte] using hl
              exact ((mem_expPt (c.prec+8) lo).1 l hh).trans
                (Real.exp_le_exp.mpr (hx.1 lo hlo))
            · have hh : Dy.zero = l := Option.some.inj (by
                simpa only [hlo, hlow, Bool.false_eq_true, ↓reduceIte] using hl)
              exact hh ▸ hzero
        · intro u hu
          exact (Real.exp_le_exp.mpr (hx.2 hi hhi)).trans
            ((mem_expPt (c.prec+8) hi).2 u hu)
    · simpa only [safeExp, hhi, hcap, Bool.not_false, ↓reduceIte,
        Ival.mem_mk, Ival.loLe_some, Ival.leHi_none, and_true, Id.run, pure] using hzero

theorem unaryR_sound {c : Ctx} (hc : c.Valid) (op : Unary)
    {x : ℝ} {X : Ival} (hx : x ∈ X) : op.real x ∈ unaryR c op X := by
  cases op <;> (try exact unary_evalR_sound hc _ hx)
  · exact safeExp_sound hx
  all_goals
    simp only [unaryR]
    split
    · exact unary_evalR_sound hc _ hx
    · exact Ival.mem_top _

private def unaryCRaw (c : Ctx) (op : Unary) (Z : CBox) : Option CBox := do
  match op with
  | .exp => do
    let E := safeExp c Z.re
    let r ← E.hi
    if exactPoint Z.im 0 then some (CBox.ofReal E) else
      some ⟨⟨some r.neg,some r⟩,⟨some r.neg,some r⟩⟩
  | .inv => if (CBox.normSq c.prec Z).pos then some (CBox.inv c.prec Z) else none
  | .log =>
    if Z.re.negv then some (logBox c (CBox.neg Z))
    else if Z.re.pos then some (logBox c Z) else none
  | .sqrt =>
    if Z.re.nonpos then some (CBox.ofReal Ival.zero)
    else if Z.re.pos then some (sqrtBox c Z) else none
  | .abs =>
    if Z.re.nonneg then some Z else if Z.re.nonpos then some (CBox.neg Z) else none
  | .floor =>
    let F := intFloorIval Z.re
    if let (some a,some b) := (F.lo,F.hi) then
      if dyEq a b then some (CBox.ofReal (Ival.pt a)) else none
    else none
  | .atan => none
  | _ => some (Unary.evalC c op Z)


private theorem unaryC_raw_result {c : Ctx} {op : Unary} {Z V : CBox}
    (h : unaryC c op Z = some V) : unaryCRaw c op Z = some V := by
  cases op <;> simp only [unaryC,unaryCRaw,bind,Option.bind] at h ⊢
  all_goals
    repeat' (split at h <;> simp_all only [reduceCtorEq])
    all_goals simp_all

private theorem unaryC_real_via_evalC {c : Ctx} (hc : c.Valid) {op : Unary}
    {x : ℝ} {Z V : CBox} (hx : (x : ℂ) ∈ Z)
    (hr : (Term.unary op .var).Regular {(x : ℂ)})
    (h : Unary.evalC c op Z = V) : (op.real x : ℂ) ∈ V := by
  have he := Term.agrees hr (Set.mem_singleton (x : ℂ))
  exact h ▸ he ▸ unary_evalC_sound hc op hx

/-- The complex fallback may choose a different analytic branch from the
principal complex function, but must still agree with the real primitive. -/
theorem unaryC_real_sound {c : Ctx} (hc : c.Valid) (op : Unary)
    {x : ℝ} {Z V : CBox} (hx : (x : ℂ) ∈ Z) (h : unaryC c op Z = some V) :
    (op.real x : ℂ) ∈ V := by
  have h' := unaryC_raw_result h
  unfold unaryCRaw at h'
  cases op
  case exp =>
    let E := safeExp c Z.re
    have he : Real.exp x ∈ E := safeExp_sound hx.1
    cases hh : E.hi with
    | none => simp only [show (safeExp c Z.re).hi = none from hh,bind,Option.bind_none,
        reduceCtorEq] at h'
    | some r =>
      change ((E.hi.bind fun r => if exactPoint Z.im 0 then
        some (CBox.ofReal E) else some (symmetricBox r))) = some V at h'
      rw [hh] at h'
      simp only [Option.bind_some] at h'
      split at h'
      · rw [← Option.some.inj h']
        exact CBox.mem_ofReal he
      · rw [← Option.some.inj h']
        have hu : Real.exp x ≤ r.toReal := he.2 r hh
        have hr : 0 ≤ r.toReal := (Real.exp_pos x).le.trans hu
        have hn : r.neg.toReal = -r.toReal := by simp [Dy.toReal_def]
        refine ⟨?_,?_⟩ <;>
          simp only [Unary.real,symmetricBox,Complex.ofReal_re,Complex.ofReal_im,
            Ival.mem_mk,Ival.loLe_some,Ival.leHi_some,hn]
        · exact ⟨by linarith [Real.exp_pos x],hu⟩
        · exact ⟨neg_nonpos.mpr hr,hr⟩
  case inv =>
    simp only at h'
    split at h'
    · rw [← Option.some.inj h']
      simpa only [Unary.real,Complex.ofReal_inv] using CBox.mem_inv (p := c.prec) hx
    · simp only [reduceCtorEq] at h'
  case log =>
    simp only at h'
    split at h'
    · rename_i hn
      rw [← Option.some.inj h']
      have hp : 0 < -x := neg_pos.mpr (Ival.neg_of hn hx.1)
      have hh := mem_logBox c hc (CBox.mem_neg hx)
      simpa only [Unary.real,← Complex.ofReal_neg,← Complex.ofReal_log hp.le,
        Real.log_neg_eq_log] using hh
    · split at h'
      · rename_i hp
        rw [← Option.some.inj h']
        have hxpos : 0 < x := Ival.pos_of hp hx.1
        simpa only [Unary.real,← Complex.ofReal_log hxpos.le] using mem_logBox c hc hx
      · simp only [reduceCtorEq] at h'
  case sqrt =>
    simp only at h'
    split at h'
    · rename_i hn
      rw [← Option.some.inj h']
      have hxnonpos : x ≤ 0 := by
        have hh : 0 ≤ -x := Ival.nonneg_of (Ival.neg_nonneg_of_nonpos hn) (Ival.mem_neg hx.1)
        linarith
      simpa only [Unary.real,Real.sqrt_eq_zero_of_nonpos hxnonpos] using
        CBox.mem_ofReal Ival.mem_zero
    · split at h'
      · rename_i hp
        rw [← Option.some.inj h']
        have he := Term.agrees (e := .unary .sqrt .var) (s := {(x : ℂ)})
          ⟨trivial,by intro z hz; rcases Set.mem_singleton_iff.mp hz with rfl
                      exact Ival.pos_of hp hx.1⟩ (Set.mem_singleton (x : ℂ))
        exact he ▸ mem_sqrtBox c hc hx
      · simp only [reduceCtorEq] at h'
  case abs =>
    simp only at h'
    split at h'
    · rename_i hp
      rw [← Option.some.inj h']
      have hxnonneg : 0 ≤ x := Ival.nonneg_of hp hx.1
      simpa only [Unary.real,abs_of_nonneg hxnonneg] using hx
    · split at h'
      · rename_i hn
        rw [← Option.some.inj h']
        have hxnonpos : x ≤ 0 := by
          have hh : 0 ≤ -x := Ival.nonneg_of (Ival.neg_nonneg_of_nonpos hn) (Ival.mem_neg hx.1)
          linarith
        simpa only [Unary.real,abs_of_nonpos hxnonpos,Complex.ofReal_neg] using CBox.mem_neg hx
      · simp only [reduceCtorEq] at h'
  case floor =>
    simp only at h'
    cases hlo : (intFloorIval Z.re).lo with
    | none => simp only [hlo,reduceCtorEq] at h'
    | some a =>
      cases hhi : (intFloorIval Z.re).hi with
      | none => simp only [hlo,hhi,reduceCtorEq] at h'
      | some b =>
        simp only [hlo,hhi] at h'
        split at h'
        · rename_i hab
          rw [← Option.some.inj h']
          have he : a.toReal = b.toReal := by
            have hh : a.toRat = b.toRat := by simpa [dyEq] using hab
            exact congrArg (fun q : ℚ => (q : ℝ)) hh
          have hf := mem_intFloor hx.1
          have hv : (⌊x⌋ : ℝ) = a.toReal := le_antisymm
            (he ▸ hf.2 b hhi) (hf.1 a hlo)
          rw [show Unary.real .floor x = a.toReal from hv]
          exact CBox.mem_ofReal (Ival.mem_pt a)
        · simp only [reduceCtorEq] at h'
  case atan => simp only [reduceCtorEq] at h'
  all_goals exact unaryC_real_via_evalC hc hx ⟨trivial,trivial⟩ (Option.some.inj h')

private theorem finite_value_eq {W V : CBox}
    (h : (if W.isFinite then some W else none) = some V) : W = V := by
  split at h
  · exact Option.some.inj h
  · contradiction

theorem binaryC_real_sound {c : Ctx} (_hc : c.Valid) (op : Binary)
    {x y : ℝ} {A B V : CBox} (hx : (x : ℂ) ∈ A) (hy : (y : ℂ) ∈ B)
    (h : binaryC c op A B = some V) : (op.real x y : ℂ) ∈ V := by
  cases op with
  | add =>
    have he := finite_value_eq (by simpa [binaryC,Binary.evalC] using h)
    rw [← he]
    simpa only [Binary.real,Complex.ofReal_add] using CBox.mem_add (p := c.prec) hx hy
  | sub =>
    have he := finite_value_eq (by simpa [binaryC,Binary.evalC] using h)
    rw [← he]
    simpa only [Binary.real,Complex.ofReal_sub] using CBox.mem_sub (p := c.prec) hx hy
  | mul =>
    have he := finite_value_eq (by simpa [binaryC,Binary.evalC] using h)
    rw [← he]
    simpa only [Binary.real,Complex.ofReal_mul] using CBox.mem_mul (p := c.prec) hx hy
  | div =>
    by_cases hn : (CBox.normSq c.prec B).pos = true
    · have he := finite_value_eq (by simpa [binaryC,hn] using h)
      rw [← he]
      simpa only [Binary.real,Complex.ofReal_div] using CBox.mem_div (p := c.prec) hx hy
    · simp [binaryC,hn] at h
  | max =>
    by_cases hab : Ival.leB A.re B.re = true
    · have he := finite_value_eq (by simpa [binaryC,hab] using h)
      have hle : x ≤ y := Ival.le_of_leB hx.1 hy.1 hab
      simpa only [Binary.real,max_eq_right hle,← he] using hy
    · by_cases hba : Ival.leB B.re A.re = true
      · have he := finite_value_eq (by simpa [binaryC,hab,hba] using h)
        have hle : y ≤ x := Ival.le_of_leB hy.1 hx.1 hba
        simpa only [Binary.real,max_eq_left hle,← he] using hx
      · simp [binaryC,hab,hba] at h
  | min =>
    by_cases hab : Ival.leB A.re B.re = true
    · have he := finite_value_eq (by simpa [binaryC,hab] using h)
      have hle : x ≤ y := Ival.le_of_leB hx.1 hy.1 hab
      simpa only [Binary.real,min_eq_left hle,← he] using hx
    · by_cases hba : Ival.leB B.re A.re = true
      · have he := finite_value_eq (by simpa [binaryC,hab,hba] using h)
        have hle : y ≤ x := Ival.le_of_leB hy.1 hx.1 hba
        simpa only [Binary.real,min_eq_right hle,← he] using hy
      · simp [binaryC,hab,hba] at h

theorem squareC_sound {p : Nat} {z : ℂ} {Z : CBox} (hz : z ∈ Z) :
    z^2 ∈ squareC p Z := by
  constructor
  · change (z^2).re ∈ Ival.sub p (Ival.sq p Z.re) (Ival.sq p Z.im)
    simpa only [pow_two,Complex.mul_re] using
      Ival.mem_sub (p := p) (Ival.mem_sq hz.1) (Ival.mem_sq hz.2)
  · change (z^2).im ∈ Ival.mul p (Ival.ofRat p 2) (Ival.mul p Z.re Z.im)
    have he : (z^2).im = 2*(z.re*z.im) := by simp only [pow_two,Complex.mul_im]; ring
    rw [he]
    exact Ival.mem_mul (p := p) (Ival.mem_ofRat p 2) (Ival.mem_mul (p := p) hz.1 hz.2)

theorem powC_sound {p : Nat} {z : ℂ} {Z : CBox} (hz : z ∈ Z) (n : Nat) :
    z^n ∈ powC p Z n := by
  unfold powC
  split
  · rename_i hn
    have he : n = 2 := by simpa using hn
    simpa only [he] using squareC_sound hz
  · exact CBox.mem_npow hz n

theorem rationalPowerC_real_sound {c : Ctx} (hc : c.Valid) {q : ℚ}
    {x : ℝ} {Z V : CBox} (hx : (x : ℂ) ∈ Z)
    (h : rationalPowerC c Z q = some V) : ((x^(q:ℝ) : ℝ) : ℂ) ∈ V := by
  unfold rationalPowerC at h
  split at h
  · contradiction
  · rename_i hp
    have hzpos : Z.re.pos = true := by simpa using hp
    have hxpos : 0 < x := Ival.pos_of hzpos hx.1
    have hlog : (Real.log x : ℂ) ∈ logBox c Z := by
      simpa only [← Complex.ofReal_log hxpos.le] using mem_logBox c hc hx
    have harg : ((Real.log x*(q:ℝ) : ℝ) : ℂ) ∈
        CBox.mul c.prec (logBox c Z) (CBox.ofReal (Ival.ofRat c.prec q)) := by
      simpa only [Complex.ofReal_mul] using CBox.mem_mul hlog
        (CBox.mem_ofReal (Ival.mem_ofRat c.prec q))
    cases he : unaryC c .exp
        (CBox.mul c.prec (logBox c Z) (CBox.ofReal (Ival.ofRat c.prec q))) with
    | none => simp [he] at h
    | some U =>
      have hU : U = V := finite_value_eq (by simpa [he] using h)
      rw [← hU]
      simpa only [Real.rpow_def_of_pos hxpos,Unary.real] using
        unaryC_real_sound hc .exp harg he

end Lynth.Interval.Integral.Nested
