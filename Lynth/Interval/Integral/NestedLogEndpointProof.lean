import Lynth.Interval.Integral.NestedScaledRealProof

/-! Interval adapters for logarithmic endpoint models. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl

theorem endpointVar_sound {A : Scale} {t : ℝ} {z : ℂ}
    (h : endpointVar A = true) (hm : A.Mem t z) : z = (t:ℂ) := by
  have hs : A.power = 1 ∧ A.logs = 0 ∧ exactPoint A.coeff.re 1 = true ∧
      exactPoint A.coeff.im 0 = true := by simpa [endpointVar,and_assoc] using h
  obtain ⟨w,hw,he⟩ := hm
  have hr := exactPoint_sound hw.1 hs.2.2.1
  have hi := exactPoint_sound hw.2 hs.2.2.2
  have hw1 : w = 1 := Complex.ext (by simpa using hr) (by simpa using hi)
  simpa only [hs.1,hs.2.1,hw1,Rat.cast_one,Real.rpow_one,pow_zero,mul_one] using he

theorem logEndpointScale_real_sound {c : Ctx} (hc : c.Valid) {δ : Dy} {V : Scale}
    {t : ℝ} (ht : 0 < t) (htδ : t ≤ δ.toReal) (hd : δ.toReal ≤ 1/2)
    (h : logEndpointScale c δ = some V) : V.Mem t (Real.log t:ℂ) := by
  unfold logEndpointScale at h
  split at h
  · simp at h
  · let D := Ival.sub c.prec Ival.one (unaryR c .log (Ival.pt δ))
    cases hh : (Ival.inv c.prec D).hi with
    | none => simp only [show (Ival.inv c.prec
          (Ival.sub c.prec Ival.one (unaryR c .log (Ival.pt δ)))).hi = none from hh,
          bind,Option.bind_none,reduceCtorEq] at h
    | some R =>
      dsimp only [D] at hh
      have he : Scale.mk 0 1 (CBox.ofReal (Ival.add c.prec (Ival.ofRat c.prec (-1))
          ⟨some Dy.zero,some R⟩)) = V := by simpa only [hh,bind,pure,Option.bind_some,Option.some.injEq] using h
      rw [← he]
      have hd0 : 0 < δ.toReal := ht.trans_le htδ
      have hd1 : δ.toReal ≤ 1 := by linarith
      have ht1 : t ≤ 1 := htδ.trans hd1
      let L := 1-Real.log t
      let Ld := 1-Real.log δ.toReal
      have hLp : 0 < L := by dsimp [L]; linarith [Real.log_nonpos ht.le ht1]
      have hLdp : 0 < Ld := by dsimp [Ld]; linarith [Real.log_nonpos hd0.le hd1]
      have hLmem : Ld ∈ D := Ival.mem_sub Ival.mem_one
        (unaryR_sound hc .log (Ival.mem_pt δ))
      have hR : 1/Ld ≤ R.toReal := by
        simpa only [one_div] using (Ival.mem_inv (p := c.prec) hLmem).2 R hh
      have huR : 1/L ≤ R.toReal :=
        (one_div_le_one_div_of_le hLdp (by dsimp [L,Ld]; linarith [Real.log_le_log ht htδ])).trans hR
      have hu : 1/L ∈ (⟨some Dy.zero,some R⟩ : Ival) := by
        refine ⟨?_,?_⟩
        · intro a ha; cases Option.some.inj ha
          simpa [Dy.toReal_def] using (one_div_pos.mpr hLp).le
        · intro b hb; cases Option.some.inj hb; exact huR
      have hcoef := Ival.mem_add (p := c.prec) (Ival.mem_ofRat c.prec (-1)) hu
      refine ⟨((-1+1/L:ℝ):ℂ),CBox.mem_ofReal (by simpa using hcoef),?_⟩
      simp only [Rat.cast_zero,Real.rpow_zero,pow_one,one_mul]
      change (Real.log t:ℂ) = (L:ℂ)*((-1+1/L:ℝ):ℂ)
      rw [← Complex.ofReal_mul]
      congr 1
      change Real.log t = L*(-1+1/L)
      field_simp [hLp.ne']
      dsimp only [L]
      ring

theorem logOneMinusEndpointScale_real_sound {c : Ctx} {δ : Dy} {V : Scale}
    {t : ℝ} (ht : 0 < t) (htδ : t ≤ δ.toReal) (hd : δ.toReal ≤ 1/2)
    (h : logOneMinusEndpointScale c δ = some V) : V.Mem t (Real.log (1-t):ℂ) := by
  unfold logOneMinusEndpointScale at h
  split at h
  · simp at h
  · let D := Ival.sub c.prec Ival.one (Ival.pt δ)
    cases hh : (Ival.inv c.prec D).hi with
    | none => simp only [show (Ival.inv c.prec
          (Ival.sub c.prec Ival.one (Ival.pt δ))).hi = none from hh,
          bind,Option.bind_none,reduceCtorEq] at h
    | some R =>
      dsimp only [D] at hh
      have he : Scale.mk 1 0 (CBox.ofReal ⟨some R.neg,some Dy.one.neg⟩) = V := by
        simpa only [hh,bind,pure,Option.bind_some,Option.some.injEq] using h
      rw [← he]
      have hR : 1/(1-δ.toReal) ≤ R.toReal := by
        simpa only [one_div] using (Ival.mem_inv (p := c.prec)
          (Ival.mem_sub Ival.mem_one (Ival.mem_pt δ))).2 R hh
      have hb := real_log_one_sub_div_bounds ht htδ hd
      have hcoef : Real.log (1-t)/t ∈ (⟨some R.neg,some Dy.one.neg⟩ : Ival) := by
        refine ⟨?_,?_⟩
        · intro a ha; cases Option.some.inj ha
          have hn : R.neg.toReal = -R.toReal := by simp [Dy.toReal_def]
          rw [hn]
          have hlo : -(1/(1-δ.toReal)) ≤ Real.log (1-t)/t := by
            simpa only [neg_div] using hb.1
          linarith
        · intro b hb'; cases Option.some.inj hb'
          simpa [Dy.toReal_def] using hb.2
      refine ⟨((Real.log (1-t)/t:ℝ):ℂ),CBox.mem_ofReal hcoef,?_⟩
      simp only [Rat.cast_one,Real.rpow_one,pow_zero,mul_one]
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp [ht.ne']
end Lynth.Interval.Integral.Nested
