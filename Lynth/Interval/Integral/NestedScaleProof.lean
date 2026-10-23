module

import all Lynth.Interval.Integral.NestedEndpointProof
import all Lynth.Interval.Integral.Math.NestedEnvelope

/-! Exact arithmetic for the nested endpoint scale representation. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl Fns

theorem scaleConst_sound {Z : CBox} {z : ℂ} (hz : z ∈ Z) (t : ℝ) :
    (scaleConst Z).Mem t z := by
  refine ⟨z,hz,?_⟩
  simp [scaleConst]

theorem scaleZero_sound (t : ℝ) : scaleZero.Mem t 0 :=
  scaleConst_sound (CBox.mem_ofReal Ival.mem_zero) t

theorem scaleVariable_sound (t : ℝ) :
    (Scale.mk 1 0 (CBox.ofReal Ival.one)).Mem t (t : ℂ) := by
  refine ⟨1,by simpa using CBox.mem_ofReal Ival.mem_one,?_⟩
  simp

theorem boxZero_sound {Z : CBox} {z : ℂ} (hz : z ∈ Z) (h : boxZero Z = true) : z = 0 := by
  obtain ⟨hr,hi⟩ := Bool.and_eq_true_iff.mp h
  apply Complex.ext
  · simpa using exactPoint_sound hz.1 hr
  · simpa using exactPoint_sound hz.2 hi

theorem Scale.Mem.eq_zero {A : Scale} {t : ℝ} {z : ℂ}
    (h : A.Mem t z) (hzero : boxZero A.coeff = true) : z = 0 := by
  obtain ⟨w,hw,hz⟩ := h
  rw [hz,boxZero_sound hw hzero,mul_zero]

theorem scaleMul_sound {c : Ctx} {A B : Scale} {a b : ℂ} {t : ℝ}
    (ht : 0 < t) (ha : A.Mem t a) (hb : B.Mem t b) :
    (scaleMul c A B).Mem t (a*b) := by
  obtain ⟨u,hu,ha⟩ := ha
  obtain ⟨v,hv,hb⟩ := hb
  refine ⟨u*v,CBox.mem_mul (p := c.prec) hu hv,?_⟩
  simp only [scaleMul,Rat.cast_add,Real.rpow_add ht,pow_add]
  rw [ha,hb]
  push_cast
  ring

theorem scalePow_sound {c : Ctx} {A : Scale} {a : ℂ} {t : ℝ}
    (ht : 0 < t) (ha : A.Mem t a) (n : Nat) : (scalePow c A n).Mem t (a^n) := by
  obtain ⟨u,hu,ha⟩ := ha
  refine ⟨u^n,powC_sound (p := c.prec) hu n,?_⟩
  have he : t^(((A.power*(n:ℚ):ℚ):ℝ))*(1-Real.log t)^(A.logs*n) =
      (t^(A.power:ℝ)*(1-Real.log t)^A.logs)^n := by
    simp only [Rat.cast_mul,Rat.cast_natCast,Real.rpow_mul ht.le,Real.rpow_natCast,
      pow_mul,mul_pow]
  change a^n = ((t^(((A.power*(n:ℚ):ℚ):ℝ))*(1-Real.log t)^(A.logs*n):ℝ):ℂ)*u^n
  rw [he,ha,mul_pow]
  push_cast
  rfl

theorem scaleNeg_sound {A : Scale} {a : ℂ} {t : ℝ} (ha : A.Mem t a) :
    ({A with coeff := CBox.neg A.coeff} : Scale).Mem t (-a) := by
  obtain ⟨u,hu,ha⟩ := ha
  refine ⟨-u,CBox.mem_neg hu,?_⟩
  simp only
  rw [ha,mul_neg]

theorem scaleDiv_sound {c : Ctx} {A B V : Scale} {a b : ℂ} {t : ℝ}
    (ht : 0 < t) (ha : A.Mem t a) (hb : B.Mem t b)
    (h : scaleDiv c A B = some V) : V.Mem t (a/b) := by
  have hlogs : B.logs = 0 := by
    by_contra hl
    simp [scaleDiv,hl] at h
  unfold scaleDiv at h
  split at h
  · contradiction
  · have he := Option.some.inj h
    rw [← he]
    obtain ⟨u,hu,ha⟩ := ha
    obtain ⟨v,hv,hb⟩ := hb
    refine ⟨u/v,CBox.mem_div (p := c.prec) hu hv,?_⟩
    simp only [Rat.cast_sub,Real.rpow_sub ht]
    rw [ha,hb]
    simp only [hlogs,pow_zero,mul_one]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

theorem factor_sound {c : Ctx} (hc : c.Valid) {δ : Dy} {q : ℚ} {V : CBox}
    {t : ℝ} (ht : 0 < t) (htδ : t ≤ δ.toReal)
    (h : factor c δ q = some V) : ((t^(q:ℝ) : ℝ) : ℂ) ∈ V := by
  unfold factor at h
  split at h
  · rename_i hq
    have hq' : q = 0 := by simpa using hq
    have he := Option.some.inj h
    rw [← he,hq']
    simpa using CBox.mem_ofReal Ival.mem_one
  · split at h
    · contradiction
    · rename_i hq
      have hq' : (0:ℝ) ≤ (q:ℝ) := by exact_mod_cast le_of_not_gt hq
      cases hh : (rpowIval c (Ival.pt δ) (Ival.ofRat c.prec q)).hi with
      | none => simp [hh] at h
      | some r =>
        have he : CBox.ofReal ⟨some Dy.zero,some r⟩ = V := by simpa [hh] using h
        rw [← he]
        apply CBox.mem_ofReal
        have hr := (mem_rpowIval hc (Ival.mem_pt δ) (Ival.mem_ofRat c.prec q)).2 r hh
        exact ⟨fun _ hl => by
          cases Option.some.inj hl
          simpa [Dy.toReal_def] using Real.rpow_nonneg ht.le (q:ℝ),
          fun _ hu => by
            cases Option.some.inj hu
            exact (Real.rpow_le_rpow ht.le htδ hq').trans hr⟩

theorem scaleFactor_sound {c : Ctx} (hc : c.Valid) {δ : Dy} {p q : ℚ}
    {n m : Nat} {F : CBox} {t : ℝ} (ht : 0 < t) (htδ : t ≤ δ.toReal) (ht1 : t ≤ 1)
    (hnm : n ≤ m) (hF : factor c δ (p-q) = some F) :
    (((t^((p-q:ℚ):ℝ)*((1-Real.log t)^n/(1-Real.log t)^m) : ℝ) : ℂ)) ∈
      (if n < m then CBox.mul c.prec F (CBox.ofReal unit) else F) := by
  have hlog : 1 ≤ 1-Real.log t := by linarith [Real.log_nonpos ht.le ht1]
  have hlogpos : 0 < 1-Real.log t := lt_of_lt_of_le zero_lt_one hlog
  have hmpos : 0 < (1-Real.log t)^m := pow_pos hlogpos m
  have hfactor := factor_sound hc ht htδ hF
  split
  · have hratio : (1-Real.log t)^n/(1-Real.log t)^m ∈ unit := by
      apply Ival.mem_ofRats
      · simpa using div_nonneg (pow_nonneg hlogpos.le n) hmpos.le
      · simpa using (div_le_one hmpos).mpr (pow_le_pow_right₀ hlog hnm)
    simpa only [Complex.ofReal_mul] using
      CBox.mem_mul (p := c.prec) hfactor (CBox.mem_ofReal hratio)
  · rename_i hn
    have he : n = m := by omega
    simpa only [he,div_self hmpos.ne',mul_one] using hfactor

theorem scaleAdd_sound {c : Ctx} (hc : c.Valid) {δ : Dy} {A B V : Scale} {a b : ℂ} {t : ℝ}
    (ht : 0 < t) (htδ : t ≤ δ.toReal) (ht1 : t ≤ 1)
    (ha : A.Mem t a) (hb : B.Mem t b) (h : scaleAdd c δ A B = some V) :
    V.Mem t (a+b) := by
  simp only [scaleAdd,Bool.false_eq_true,↓reduceIte] at h
  split at h
  · rename_i hzero
    rw [← Option.some.inj h]
    simpa only [ha.eq_zero hzero,zero_add] using hb
  · split at h
    · rename_i hzero
      rw [← Option.some.inj h]
      simpa only [hb.eq_zero hzero,add_zero] using ha
    · let q := min A.power B.power
      let m := max A.logs B.logs
      cases hfa : factor c δ (A.power-q) with
      | none => simp [q,hfa] at h
      | some fa =>
        cases hfb : factor c δ (B.power-q) with
        | none => simp [q,hfa,hfb] at h
        | some fb =>
          let FA := if A.logs < m then CBox.mul c.prec fa (CBox.ofReal unit) else fa
          let FB := if B.logs < m then CBox.mul c.prec fb (CBox.ofReal unit) else fb
          have he : (Scale.mk q m (CBox.add c.prec (CBox.mul c.prec FA A.coeff)
              (CBox.mul c.prec FB B.coeff))) = V := by
            simpa [q,m,FA,FB,hfa,hfb] using h
          rw [← he]
          obtain ⟨u,hu,ha⟩ := ha
          obtain ⟨v,hv,hb⟩ := hb
          have hFA := scaleFactor_sound hc ht htδ ht1 (Nat.le_max_left A.logs B.logs) hfa
          have hFB := scaleFactor_sound hc ht htδ ht1 (Nat.le_max_right A.logs B.logs) hfb
          refine ⟨_,CBox.mem_add (p := c.prec) (CBox.mem_mul hFA hu) (CBox.mem_mul hFB hv),?_⟩
          simp only [Rat.cast_sub,Real.rpow_sub ht]
          rw [ha,hb]
          have hq : (t^(q:ℝ) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
          have hlog : 0 < 1-Real.log t := by linarith [Real.log_nonpos ht.le ht1]
          have hM : (1-Real.log t)^m ≠ 0 := (pow_pos hlog m).ne'
          have hqC : ((t^(q:ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq
          have hMC : (((1-Real.log t)^m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hM
          dsimp only [m] at hMC ⊢
          push_cast at hMC ⊢
          field_simp [hqC,hMC]

theorem scaleSub_sound {c : Ctx} (hc : c.Valid) {δ : Dy} {A B V : Scale} {a b : ℂ} {t : ℝ}
    (ht : 0 < t) (htδ : t ≤ δ.toReal) (ht1 : t ≤ 1)
    (ha : A.Mem t a) (hb : B.Mem t b) (h : scaleAdd c δ A B true = some V) :
    V.Mem t (a-b) := by
  change scaleAdd c δ A {B with coeff := CBox.neg B.coeff} false = some V at h
  simpa only [sub_eq_add_neg] using scaleAdd_sound hc ht htδ ht1 ha (scaleNeg_sound hb) h

theorem factor_range_sound {c : Ctx} (hc : c.Valid) {δ : Dy} {q : ℚ} {V : CBox}
    (hq : 0 < q) (h : factor c δ q = some V) {u : ℝ}
    (hu : 0 ≤ u) (huδ : u ≤ δ.toReal^(q:ℝ)) : (u : ℂ) ∈ V := by
  unfold factor at h
  have hq0 : ¬ q == 0 := by simpa using hq.ne'
  simp only [hq0,↓reduceIte,not_lt.mpr hq.le] at h
  cases hh : (rpowIval c (Ival.pt δ) (Ival.ofRat c.prec q)).hi with
  | none => simp [hh] at h
  | some r =>
    have he : CBox.ofReal ⟨some Dy.zero,some r⟩ = V := by simpa [hh] using h
    rw [← he]
    apply CBox.mem_ofReal
    have hr := (mem_rpowIval hc (Ival.mem_pt δ) (Ival.mem_ofRat c.prec q)).2 r hh
    exact ⟨fun _ hl => by cases Option.some.inj hl; simpa [Dy.toReal_def] using hu,
      fun _ hh => by cases Option.some.inj hh; exact huδ.trans hr⟩

theorem collapse_sound {c : Ctx} (hc : c.Valid) {δ : Dy} {A : Scale} {V : CBox}
    {t : ℝ} {z : ℂ} (ht : 0 < t) (htδ : t ≤ δ.toReal) (ht1 : t ≤ 1)
    (hz : A.Mem t z) (h : collapse c δ A = some V) : z ∈ V := by
  unfold collapse at h
  split at h
  · rename_i hzero
    rw [← Option.some.inj h,hz.eq_zero hzero]
    exact CBox.mem_ofReal Ival.mem_zero
  · split at h
    · contradiction
    · rename_i hguard
      split at h
      · rename_i hlogs
        have hl : A.logs = 0 := by simpa using hlogs
        cases hF : factor c δ A.power with
        | none => simp [hF] at h
        | some F =>
          have he : CBox.mul c.prec A.coeff F = V := by simpa [hF] using h
          rw [← he]
          obtain ⟨w,hw,hz⟩ := hz
          have hmem := CBox.mem_mul (p := c.prec) hw (factor_sound hc ht htδ hF)
          rw [hz]
          simpa only [hl,pow_zero,mul_one,one_mul,mul_comm] using hmem
      · rename_i hlogs
        have hl : A.logs ≠ 0 := by simpa using hlogs
        have hp : 0 < A.power := by
          by_contra hn
          rcases lt_or_eq_of_le (le_of_not_gt hn) with hn | hn
          · simp [hn] at hguard
          · simp [hn,hl] at hguard
        let ε : ℚ := A.power/2
        let C : ℚ := (2:ℚ)^A.logs * (1+(A.logs.factorial:ℚ)/ε^A.logs)
        have hε : 0 < ε := by dsimp [ε]; positivity
        have hC : 0 < C := by dsimp [C]; positivity
        have hCR : (0:ℝ) < (C:ℝ) := by exact_mod_cast hC
        cases hF : factor c δ ε with
        | none => simp [ε,hF] at h
        | some F =>
          have he : CBox.mul c.prec A.coeff
              (CBox.mul c.prec (CBox.ofReal (Ival.ofRat c.prec C)) F) = V := by
            simpa [ε,C,hF] using h
          rw [← he]
          obtain ⟨w,hw,hz⟩ := hz
          let weight := t^(A.power:ℝ)*(1-Real.log t)^A.logs
          let u := weight/(C:ℝ)
          have hweight : 0 ≤ weight := A.weight_nonneg ht ht1
          have hbound : weight ≤ (C:ℝ)*t^(ε:ℝ) := by
            have hpR : (0:ℝ) < (A.power:ℝ) := by exact_mod_cast hp
            simpa only [weight,C,ε,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
              Rat.cast_add,Rat.cast_one,Rat.cast_div,Rat.cast_natCast] using
              power_log_absorb ht ht1 hpR A.logs
          have hu : 0 ≤ u := div_nonneg hweight hCR.le
          have huδ : u ≤ δ.toReal^(ε:ℝ) := by
            apply (div_le_iff₀ hCR).mpr
            have hεR : (0:ℝ) ≤ (ε:ℝ) := by exact_mod_cast hε.le
            exact hbound.trans (by
              simpa only [mul_comm] using mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow ht.le htδ hεR) hCR.le)
          have hmem := CBox.mem_mul (p := c.prec) hw
            (CBox.mem_mul (p := c.prec) (CBox.mem_ofReal (Ival.mem_ofRat c.prec C))
              (factor_range_sound hc hε hF hu huδ))
          have hweight' : (C:ℝ)*u = weight := by dsimp [u]; field_simp
          have heq : z = w * (((C:ℝ):ℂ)*(u:ℂ)) := by
            rw [← Complex.ofReal_mul,hweight']
            simpa only [mul_comm] using hz
          exact heq.symm ▸ hmem

end Lynth.Interval.Integral.Nested
