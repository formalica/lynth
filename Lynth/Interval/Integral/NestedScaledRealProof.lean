import Lynth.Interval.Integral.NestedScaleProof

/-! The real branch of scaled endpoint evaluation. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl Fns

theorem Scale.weight_pos (A : Scale) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    0 < t^(A.power:ℝ)*(1-Real.log t)^A.logs := by
  have hlog : 0 < 1-Real.log t := by linarith [Real.log_nonpos ht.le ht1]
  exact mul_pos (Real.rpow_pos_of_pos ht _) (pow_pos hlog _)

theorem Scale.real_coeff {A : Scale} {t x : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (h : A.Mem t (x : ℂ)) : ∃ y : ℝ, (y : ℂ) ∈ A.coeff ∧
      x = (t^(A.power:ℝ)*(1-Real.log t)^A.logs)*y := by
  obtain ⟨w,hw,he⟩ := h
  have hp := A.weight_pos ht ht1
  have him : w.im = 0 := by
    have hh := congrArg Complex.im he
    simp only [Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,zero_mul,add_zero] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hp.ne'
  have hw' : (w.re : ℂ) = w := Complex.ext (by simp) (by simpa using him.symm)
  refine ⟨w.re,hw'.symm ▸ hw,?_⟩
  have hh := congrArg Complex.re he
  simpa only [Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero] using hh

theorem symmetricBox_real_mem {r : Dy} {x : ℝ} (h : |x| ≤ r.toReal) :
    (x : ℂ) ∈ symmetricBox r := by
  have hr : 0 ≤ r.toReal := (abs_nonneg x).trans h
  have hn : r.neg.toReal = -r.toReal := by simp [Dy.toReal_def]
  refine ⟨?_,?_⟩ <;>
    simp only [symmetricBox,Complex.ofReal_re,Complex.ofReal_im,
      Ival.mem_mk,Ival.loLe_some,Ival.leHi_some,hn]
  · exact abs_le.mp h
  · exact ⟨neg_nonpos.mpr hr,hr⟩

theorem scaleRpow_real_sound {c : Ctx} (hc : c.Valid) {A : Scale} {q : ℚ}
    {t x : ℝ} {V : CBox} (ht : 0 < t) (ht1 : t ≤ 1) (hA : A.Mem t (x : ℂ))
    (hlogs : A.logs = 0) (h : rationalPowerC c A.coeff q = some V) :
    (Scale.mk (A.power*q) 0 V).Mem t ((x^(q:ℝ):ℝ):ℂ) := by
  obtain ⟨y,hy,hx⟩ := A.real_coeff ht ht1 hA
  have hpos : A.coeff.re.pos = true := by
    by_contra hn
    simp [rationalPowerC,hn] at h
  have hypos : 0 < y := Ival.pos_of hpos hy.1
  refine ⟨_,rationalPowerC_real_sound hc hy h,?_⟩
  simp only [hlogs,pow_zero,mul_one] at hx
  rw [hx]
  have he := real_rpow_scaled (p := (A.power:ℝ)) (q := (q:ℝ)) ht hypos
  simp only [Rat.cast_mul,pow_zero,mul_one]
  rw [he,Complex.ofReal_mul]

private theorem collapsedUnary_real_sound {c : Ctx} (hc : c.Valid) {δ : Dy}
    {A V : Scale} {op : Unary} {t x : ℝ} (ht : 0 < t)
    (htδ : t ≤ δ.toReal) (ht1 : t ≤ 1) (hA : A.Mem t (x : ℂ))
    (h : (do return scaleConst (← unaryC c op (← collapse c δ A))) = some V) :
    V.Mem t (op.real x : ℂ) := by
  cases hZ : collapse c δ A with
  | none => simp [hZ] at h
  | some Z =>
    cases hU : unaryC c op Z with
    | none => simp [hZ,hU] at h
    | some U =>
      have he : scaleConst U = V := by simpa [hZ,hU] using h
      rw [← he]
      exact scaleConst_sound (unaryC_real_sound hc op
        (collapse_sound hc ht htδ ht1 hA hZ) hU) t

theorem scaleSqrt_real_sound {c : Ctx} (hc : c.Valid) {A : Scale} {V : CBox}
    {t x : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hA : A.Mem t (x : ℂ))
    (hlogs : A.logs = 0) (h : unaryC c .sqrt A.coeff = some V) :
    (Scale.mk (A.power/2) 0 V).Mem t (Real.sqrt x : ℂ) := by
  obtain ⟨y,hy,hx⟩ := A.real_coeff ht ht1 hA
  have hyS := unaryC_real_sound hc .sqrt hy h
  simp only [Unary.real] at hyS
  refine ⟨_,hyS,?_⟩
  simp only [hlogs,pow_zero,mul_one] at hx
  simp only [Rat.cast_div,Rat.cast_ofNat,pow_zero,mul_one]
  rw [hx,sqrt_power_factor ht,Complex.ofReal_mul]

theorem scaleLog_real_sound {c : Ctx} (hc : c.Valid) {A : Scale} {V : CBox} {r R : Dy}
    {t x : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hA : A.Mem t (x : ℂ))
    (hlogs : A.logs = 0) (hV : unaryC c .log A.coeff = some V)
    (hr : boxRadius c V = some r)
    (hR : (Ival.add c.prec (Ival.ofRat c.prec |A.power|) (Ival.pt r)).hi = some R) :
    (Scale.mk 0 1 (symmetricBox R)).Mem t (Real.log x : ℂ) := by
  obtain ⟨y,hy,hx⟩ := A.real_coeff ht ht1 hA
  have hyL := unaryC_real_sound hc .log hy hV
  have hybound : |Real.log y| ≤ r.toReal := by
    have hh := (CBox.mem_norm (p := c.prec) hyL).2 r hr
    simpa only [Unary.real,Complex.norm_real,Real.norm_eq_abs] using hh
  have hpow : |(A.power:ℝ)| ∈ Ival.ofRat c.prec |A.power| := by
    simpa only [Rat.cast_abs] using Ival.mem_ofRat c.prec |A.power|
  have hupper : |(A.power:ℝ)|+r.toReal ≤ R.toReal :=
    (Ival.mem_add (p := c.prec) hpow (Ival.mem_pt r)).2 R hR
  let L := 1-Real.log t
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_nonpos ht.le ht1]
  have hlog : |Real.log x| ≤ (|(A.power:ℝ)|+|Real.log y|)*L := by
    simp only [hlogs,pow_zero,mul_one] at hx
    rw [hx]
    exact real_log_scaled_bound ht ht1
  have hcoef : |Real.log x/L| ≤ R.toReal := by
    rw [abs_div,abs_of_pos hL]
    apply (div_le_iff₀ hL).mpr
    have hs : |(A.power:ℝ)|+|Real.log y| ≤ R.toReal := by linarith
    exact hlog.trans (mul_le_mul_of_nonneg_right hs hL.le)
  refine ⟨((Real.log x/L : ℝ):ℂ),symmetricBox_real_mem hcoef,?_⟩
  simp only [Rat.cast_zero,Real.rpow_zero,pow_one,one_mul]
  change (Real.log x : ℂ) = (L:ℂ)*((Real.log x/L : ℝ):ℂ)
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp

theorem scaleUnary_real_sound {c : Ctx} (hc : c.Valid) {δ : Dy} {decay : Nat}
    {A V : Scale} {op : Unary} {t x : ℝ} (ht : 0 < t)
    (htδ : t ≤ δ.toReal) (ht1 : t ≤ 1) (hA : A.Mem t (x : ℂ))
    (h : scaleUnary c δ decay op A = some V) : V.Mem t (op.real x : ℂ) := by
  cases op <;> simp only [scaleUnary] at h
  case neg =>
    rw [← Option.some.inj h]
    simpa only [Unary.real,Complex.ofReal_neg] using scaleNeg_sound hA
  case inv =>
    simpa only [Unary.real,Complex.ofReal_inv,Complex.ofReal_one,one_div] using
      scaleDiv_sound ht (scaleConst_sound (CBox.mem_ofReal Ival.mem_one) t) hA h
  case sqrt =>
    by_cases hl : A.logs = 0
    · cases hU : unaryC c .sqrt A.coeff with
      | none => simp [hl,hU] at h
      | some U =>
        have he : Scale.mk (A.power/2) 0 U = V := by simpa [hl,hU] using h
        rw [← he]
        exact scaleSqrt_real_sound hc ht ht1 hA hl hU
    · simp [hl] at h
  case log =>
    by_cases hl : A.logs = 0
    · cases hU : unaryC c .log A.coeff with
      | none => simp [hl,hU] at h
      | some U =>
        cases hr : boxRadius c U with
        | none => simp [hl,hU,hr] at h
        | some r =>
          cases hR : (Ival.add c.prec (Ival.ofRat c.prec |A.power|) (Ival.pt r)).hi with
          | none => simp [hl,hU,hr,hR] at h
          | some R =>
            have he : Scale.mk 0 1 (symmetricBox R) = V := by simpa [hl,hU,hr,hR] using h
            rw [← he]
            exact scaleLog_real_sound hc ht ht1 hA hl hU hr hR
    · simp [hl] at h
  case abs =>
    obtain ⟨y,hy,hx⟩ := A.real_coeff ht ht1 hA
    split at h
    · rename_i hpos
      rw [← Option.some.inj h]
      have hx0 : 0 ≤ x := hx ▸ mul_nonneg (A.weight_pos ht ht1).le (Ival.nonneg_of hpos hy.1)
      simpa only [Unary.real,abs_of_nonneg hx0] using hA
    · split at h
      · rename_i hneg
        rw [← Option.some.inj h]
        have hy0 : y ≤ 0 := by
          have hh : 0 ≤ -y := Ival.nonneg_of (Ival.neg_nonneg_of_nonpos hneg) (Ival.mem_neg hy.1)
          linarith
        have hx0 : x ≤ 0 := hx ▸ mul_nonpos_of_nonneg_of_nonpos (A.weight_pos ht ht1).le hy0
        simpa only [Unary.real,abs_of_nonpos hx0,Complex.ofReal_neg] using scaleNeg_sound hA
      · contradiction
  case sin =>
    split at h
    · rw [← Option.some.inj h]
      exact scaleConst_sound (CBox.mem_ofReal (Ival.mem_ofRats
        (by simpa [Unary.real] using Real.neg_one_le_sin x)
        (by simpa [Unary.real] using Real.sin_le_one x))) t
    · exact collapsedUnary_real_sound hc ht htδ ht1 hA h
  case cos =>
    split at h
    · rw [← Option.some.inj h]
      exact scaleConst_sound (CBox.mem_ofReal (Ival.mem_ofRats
        (by simpa [Unary.real] using Real.neg_one_le_cos x)
        (by simpa [Unary.real] using Real.cos_le_one x))) t
    · exact collapsedUnary_real_sound hc ht htδ ht1 hA h
  case exp =>
    by_cases hl : A.logs = 0
    · simp only [hl,bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at h
      split at h
      · rename_i hp
        cases hhi : A.coeff.re.hi with
        | none => simp [hhi] at h
        | some hi =>
          simp only [hhi] at h
          split at h
          · contradiction
          · rename_i hguard
            have hpos : Dy.isPos hi.neg = true := by simpa using (Bool.or_eq_false_iff.mp
              (Bool.eq_false_iff.mpr hguard)).1
            have hC : 0 < hi.neg.toReal := by
              have hh := Dy.isPos_iff hi.neg |>.mp hpos
              change (0:ℝ) < (hi.neg.toRat:ℝ)
              exact_mod_cast hh
            cases hR : (Ival.div c.prec (Ival.ofRat c.prec decay.factorial)
                (Ival.npow c.prec (Ival.pt hi.neg) decay)).hi with
            | none => simp [hR] at h
            | some R =>
              obtain ⟨y,hy,hx⟩ := A.real_coeff ht ht1 hA
              simp only [hl,pow_zero,mul_one] at hx
              have hyhi : y ≤ -hi.neg.toReal := by
                have hh := hy.1.2 hi hhi
                simpa [Dy.toReal_def] using hh
              have he := complex_exp_scaled_bound (p := (A.power:ℝ)) (z := (y:ℂ)) ht hC hyhi decay
              have hExp : Real.exp x ≤ ((decay.factorial:ℝ)/hi.neg.toReal^decay) *
                  t^((-(A.power:ℝ))*(decay:ℝ)) := by
                simpa only [← Complex.ofReal_mul,← Complex.ofReal_exp,Complex.norm_real,
                  Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← hx] using he
              have hupper : (decay.factorial:ℝ)/hi.neg.toReal^decay ≤ R.toReal := by
                exact (Ival.mem_div (p := c.prec) (Ival.mem_ofRat c.prec decay.factorial)
                  (Ival.mem_npow (Ival.mem_pt hi.neg) decay)).2 R hR
              let W := t^((-(A.power:ℝ))*(decay:ℝ))
              have hW : 0 < W := Real.rpow_pos_of_pos ht _
              have hcoef : 0 ≤ Real.exp x/W ∧ Real.exp x/W ≤ R.toReal := by
                refine ⟨(div_pos (Real.exp_pos x) hW).le,?_⟩
                apply (div_le_iff₀ hW).mpr
                exact hExp.trans (mul_le_mul_of_nonneg_right hupper hW.le)
              have hmem : ((Real.exp x/W:ℝ):ℂ) ∈
                  (if exactPoint A.coeff.im 0 then
                    CBox.ofReal ⟨some Dy.zero,some R⟩ else symmetricBox R) := by
                split
                · exact CBox.mem_ofReal ⟨fun _ hh => by
                    cases Option.some.inj hh; simpa [Dy.toReal_def] using hcoef.1,
                    fun _ hh => by cases Option.some.inj hh; exact hcoef.2⟩
                · exact symmetricBox_real_mem (by simpa only [abs_of_nonneg hcoef.1] using hcoef.2)
              have hout : (Scale.mk ((-A.power)*decay) 0
                  (if exactPoint A.coeff.im 0 then
                    CBox.ofReal ⟨some Dy.zero,some R⟩ else symmetricBox R)) = V := by
                simpa [hR] using h
              rw [← hout]
              refine ⟨_,hmem,?_⟩
              simp only [Rat.cast_mul,Rat.cast_neg,Rat.cast_natCast,pow_zero,mul_one]
              change (Real.exp x:ℂ) = (W:ℂ)*((Real.exp x/W:ℝ):ℂ)
              rw [← Complex.ofReal_mul]
              congr 1
              field_simp
      · exact collapsedUnary_real_sound hc ht htδ ht1 hA h
    · simp [hl] at h
  all_goals exact collapsedUnary_real_sound hc ht htδ ht1 hA h

end Lynth.Interval.Integral.Nested
