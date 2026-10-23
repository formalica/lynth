module

import all Lynth.Interval.Integral.NestedPrimitiveProof
import all Lynth.Interval.Integral.Math.NestedEnvelope

/-! Analytic branches for the guarded complex arithmetic primitives. -/

namespace Lynth.Interval.Integral.Nested
open Intgrl Fns MeasureTheory Set
open scoped Topology

lemma analyticAt_arctan_strip {z : ℂ} (hz : |z.im| < 1) : AnalyticAt ℂ Complex.arctan z := by
  let N : ℂ := 1+z*Complex.I
  let D : ℂ := 1-z*Complex.I
  have hr : 0 < D.re := by
    dsimp [D]
    simp only [Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      mul_zero,mul_one,zero_sub,sub_neg_eq_add]
    linarith [(abs_lt.mp hz).1]
  have hD : D ≠ 0 := by intro he; rw [he,Complex.zero_re] at hr; exact (lt_irrefl _ hr)
  have hd : 0 < Complex.normSq D := Complex.normSq_pos.mpr hD
  have hslit : N/D ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    by_cases hre : z.re = 0
    · left
      have he : (N/D).re = ((1-z.im)*(1+z.im)-z.re^2)/Complex.normSq D := by
        simp only [N,D,Complex.div_re,Complex.add_re,Complex.one_re,Complex.mul_re,
          Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_sub,Complex.sub_re,
          Complex.add_im,Complex.one_im,Complex.mul_im,zero_add,add_zero,Complex.sub_im]
        ring
      rw [he,hre,zero_pow (by decide : 2 ≠ 0),sub_zero]
      exact div_pos (mul_pos (by linarith [(abs_lt.mp hz).2]) (by linarith [(abs_lt.mp hz).1])) hd
    · right
      have he : (N/D).im = 2*z.re/Complex.normSq D := by
        simp only [N,D,Complex.div_im,Complex.add_re,Complex.one_re,Complex.mul_re,
          Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_sub,Complex.sub_re,
          Complex.add_im,Complex.one_im,Complex.mul_im,zero_add,add_zero,Complex.sub_im]
        ring
      rw [he]
      exact div_ne_zero (mul_ne_zero (by norm_num) hre) hd.ne'
  have hratio : AnalyticAt ℂ (fun w : ℂ => (1+w*Complex.I)/(1-w*Complex.I)) z :=
    (analyticAt_const.add (analyticAt_id.mul analyticAt_const)).div
      (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)) hD
  have hlog : AnalyticAt ℂ (fun w : ℂ => Complex.log ((1+w*Complex.I)/(1-w*Complex.I))) z :=
    (analyticAt_clog hslit).comp (f := fun w : ℂ => (1+w*Complex.I)/(1-w*Complex.I)) hratio
  have hc : AnalyticAt ℂ (fun _ : ℂ => -Complex.I/2) z := analyticAt_const
  change AnalyticAt ℂ (fun w : ℂ => (-Complex.I/2)*Complex.log ((1+w*Complex.I)/(1-w*Complex.I))) z
  simpa only [Pi.mul_def] using hc.mul hlog



lemma symmetricBox_complex_mem {r : Dy} {z : ℂ} (h : ‖z‖ ≤ r.toReal) : z ∈ symmetricBox r := by
  have hn : r.neg.toReal = -r.toReal := by simp [Dy.toReal_def]
  have hre := abs_le.mp ((Complex.abs_re_le_norm z).trans h)
  have him := abs_le.mp ((Complex.abs_im_le_norm z).trans h)
  constructor <;> simp only [symmetricBox,Ival.mem_mk,Ival.loLe_some,Ival.leHi_some,hn]
  · exact hre
  · exact him

open private unaryCRaw unaryC_raw_result from Lynth.Interval.Integral.NestedPrimitiveProof

lemma unaryC_analytic_witness {c : Ctx} (hc : c.Valid) (op : Unary) {A B : CBox}
    (h : unaryC c op A = some B) :
    ∃ φ : ℂ → ℂ, AnalyticOnNhd ℂ φ {z | z ∈ A} ∧
      (∀ z ∈ A, φ z ∈ B) ∧
      (∀ x : ℝ, (x:ℂ) ∈ A → φ (x:ℂ) = (op.real x:ℂ)) := by
  have standard (op : Unary) (hr : (Term.unary op .var).Regular {z | z ∈ A})
      (he : Unary.evalC c op A = B) :
      ∃ φ : ℂ → ℂ, AnalyticOnNhd ℂ φ {z | z ∈ A} ∧
        (∀ z ∈ A, φ z ∈ B) ∧
        (∀ x : ℝ, (x:ℂ) ∈ A → φ (x:ℂ) = (op.real x:ℂ)) := by
    refine ⟨op.complex,Term.analytic hr,?_,?_⟩
    · intro z hz
      exact he ▸ unary_evalC_sound hc op hz
    · intro x hx
      exact Term.agrees hr hx
  have hr := unaryC_raw_result h
  unfold unaryCRaw at hr
  cases op <;> simp only at hr
  case exp =>
    cases hh : (safeExp c A.re).hi with
    | none => simp only [hh,Bind.bind,Option.bind_none,reduceCtorEq] at hr
    | some r =>
      simp only [hh,Bind.bind,Option.bind_some] at hr
      split at hr
      · rename_i him
        have he : CBox.ofReal (safeExp c A.re) = B := Option.some.inj hr
        subst B
        refine ⟨Complex.exp,fun z hz => analyticAt_cexp,?_,?_⟩
        · intro z hz
          have hzIm : z.im = 0 := by simpa using exactPoint_sound hz.2 him
          have hzre : z = (z.re:ℂ) := Complex.ext rfl (by simp [hzIm])
          rw [hzre]
          simpa only [← Complex.ofReal_exp] using CBox.mem_ofReal (safeExp_sound hz.1)
        · intro x hx
          exact Complex.ofReal_exp x |>.symm
      · have he : symmetricBox r = B := Option.some.inj hr
        subst B
        refine ⟨Complex.exp,fun z hz => analyticAt_cexp,?_,?_⟩
        · intro z hz
          apply symmetricBox_complex_mem
          rw [Complex.norm_exp]
          exact (safeExp_sound hz.1).2 r hh
        · intro x hx
          exact Complex.ofReal_exp x |>.symm
  case inv =>
    split at hr
    · rename_i hp
      apply standard .inv ⟨trivial,?_⟩ (Option.some.inj hr)
      intro z hz
      exact Complex.normSq_pos.mp (Ival.pos_of hp (CBox.mem_normSq (p := c.prec) hz))
    · simp at hr
  case log =>
    split at hr
    · rename_i hn
      have he : logBox c (CBox.neg A) = B := Option.some.inj hr
      subst B
      refine ⟨fun z => Complex.log (-z),?_,fun z hz => mem_logBox c hc (CBox.mem_neg hz),?_⟩
      · intro z hz
        have hzpos : 0 < (-z).re := by simpa using neg_pos.mpr (Ival.neg_of hn hz.1)
        exact (analyticAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl hzpos))).comp
          (f := fun z : ℂ => -z) analyticAt_id.neg
      · intro x hx
        have hxpos : 0 < -x := neg_pos.mpr (Ival.neg_of hn hx.1)
        simp only [Unary.real,← Complex.ofReal_neg,← Complex.ofReal_log hxpos.le,Real.log_neg_eq_log]
    · split at hr
      · rename_i hp
        apply standard .log ⟨trivial,?_⟩ (Option.some.inj hr)
        exact fun z hz => Ival.pos_of hp hz.1
      · simp at hr
  case sqrt =>
    split at hr
    · rename_i hn
      have he : CBox.ofReal Ival.zero = B := Option.some.inj hr
      subst B
      refine ⟨fun _ => 0,fun _ _ => analyticAt_const,fun z hz => CBox.mem_ofReal Ival.mem_zero,?_⟩
      intro x hx
      have hxnonpos : x ≤ 0 := by
        have hh : 0 ≤ -x := Ival.nonneg_of (Ival.neg_nonneg_of_nonpos hn) (Ival.mem_neg hx.1)
        linarith
      simp [Unary.real,Real.sqrt_eq_zero_of_nonpos hxnonpos]
    · split at hr
      · rename_i hp
        apply standard .sqrt ⟨trivial,?_⟩ (Option.some.inj hr)
        exact fun z hz => Ival.pos_of hp hz.1
      · simp at hr
  case abs =>
    split at hr
    · rename_i hp
      have he : A = B := Option.some.inj hr
      subst B
      refine ⟨id,fun _ _ => analyticAt_id,fun z hz => hz,?_⟩
      intro x hx
      have hxnonneg : 0 ≤ x := Ival.nonneg_of hp hx.1
      simp only [id_eq,Unary.real,abs_of_nonneg hxnonneg]
    · split at hr
      · rename_i hn
        have he : CBox.neg A = B := Option.some.inj hr
        subst B
        refine ⟨fun z => -z,fun _ _ => analyticAt_id.neg,fun z hz => CBox.mem_neg hz,?_⟩
        intro x hx
        have hxnonpos : x ≤ 0 := by
          have hh : 0 ≤ -x := Ival.nonneg_of (Ival.neg_nonneg_of_nonpos hn) (Ival.mem_neg hx.1)
          linarith
        simp only [Unary.real,abs_of_nonpos hxnonpos,Complex.ofReal_neg]
      · simp at hr
  case floor =>
    cases hlo : (intFloorIval A.re).lo with
    | none => simp only [hlo,reduceCtorEq] at hr
    | some a =>
      cases hhi : (intFloorIval A.re).hi with
      | none => simp only [hlo,hhi,reduceCtorEq] at hr
      | some b =>
        simp only [hlo,hhi] at hr
        split at hr
        · have he : CBox.ofReal (Ival.pt a) = B := Option.some.inj hr
          subst B
          refine ⟨fun _ => (a.toReal:ℂ),fun _ _ => analyticAt_const,
            fun z hz => CBox.mem_ofReal (Ival.mem_pt a),?_⟩
          intro x hx
          have hh := unaryC_real_sound hc .floor hx h
          have heq : Unary.real .floor x = a.toReal := le_antisymm (hh.1.2 a rfl) (hh.1.1 a rfl)
          rw [heq]
        · simp at hr
  case atan =>
    split at hr
    · rename_i him
      have he : Unary.evalC c .atan A = B := Option.some.inj hr
      refine ⟨Complex.arctan,?_,fun z hz => he ▸ unary_evalC_sound hc .atan hz,?_⟩
      · intro z hz
        apply analyticAt_arctan_strip
        exact Ival.lt_of_ltB (Ival.mem_abs hz.2) Ival.mem_one him
      · intro x hx
        exact (Complex.ofReal_arctan x).symm
    · simp at hr
  all_goals exact standard _ ⟨trivial,trivial⟩ (Option.some.inj hr)

lemma unaryC_log_real_ne_zero {c : Ctx} {A B : CBox} {x : ℝ}
    (h : unaryC c .log A = some B) (hx : (x:ℂ) ∈ A) : x ≠ 0 := by
  by_cases hn : A.re.negv = true
  · exact (show x < 0 from Ival.neg_of hn hx.1).ne
  by_cases hp : A.re.pos = true
  · exact (show 0 < x from Ival.pos_of hp hx.1).ne'
  simp [unaryC,hn,hp] at h

lemma rationalPowerC_analytic_witness {c : Ctx} (hc : c.Valid) {A B : CBox} {q : ℚ}
    (h : rationalPowerC c A q = some B) :
    ∃ φ : ℂ → ℂ, AnalyticOnNhd ℂ φ {z | z ∈ A} ∧
      (∀ z ∈ A, φ z ∈ B) ∧
      (∀ x : ℝ, (x:ℂ) ∈ A → φ (x:ℂ) = ((x^(q:ℝ):ℝ):ℂ)) := by
  unfold rationalPowerC at h
  split at h
  · contradiction
  · rename_i hpos
    have hp : A.re.pos = true := by simpa using hpos
    simp only [Bind.bind,Option.bind_eq_some_iff] at h
    obtain ⟨U,hU,h⟩ := h
    split at h
    · have he : U = B := Option.some.inj h
      subst B
      obtain ⟨ψ,hψ,hψmem,hψreal⟩ := unaryC_analytic_witness hc .exp hU
      let arg : ℂ → ℂ := fun z => Complex.log z*(q:ℂ)
      let ArgBox := CBox.mul c.prec (logBox c A) (CBox.ofReal (Ival.ofRat c.prec q))
      have harg : ∀ z ∈ A, arg z ∈ ArgBox := fun z hz =>
        CBox.mem_mul (p := c.prec) (mem_logBox c hc hz) (CBox.mem_ofReal (Ival.mem_ofRat c.prec q))
      refine ⟨fun z => ψ (arg z),?_,fun z hz => hψmem _ (harg z hz),?_⟩
      · intro z hz
        have hl : AnalyticAt ℂ Complex.log z := analyticAt_clog
          (Complex.mem_slitPlane_iff.mpr (Or.inl (Ival.pos_of hp hz.1)))
        exact (hψ _ (harg z hz)).comp (f := arg) (hl.mul analyticAt_const)
      · intro x hx
        have hxpos : 0 < x := Ival.pos_of hp hx.1
        have he : arg (x:ℂ) = ((Real.log x*(q:ℝ):ℝ):ℂ) := by
          dsimp only [arg]
          rw [← Complex.ofReal_log hxpos.le]
          push_cast
          rfl
        change ψ (arg (x:ℂ)) = ((x^(q:ℝ):ℝ):ℂ)
        rw [he,hψreal _ (he ▸ harg (x:ℂ) hx)]
        simp only [Unary.real,Real.rpow_def_of_pos hxpos]
    · contradiction

end Lynth.Interval.Integral.Nested
