module

import all Lynth.Interval.Integral.NestedScaledSound
import all Lynth.Interval.Integral.NestedHalflineProof
import all Lynth.Interval.Integral.NestedMemoProof
import all Lynth.Interval.Integral.NestedSemantics

namespace Lynth.Interval.Integral.Nested
open Intgrl Fns MeasureTheory Set Filter
open scoped Topology

lemma endpointExpr_scoped {n : Nat} {e : Expr} {right : Bool}
    (hs : e.scoped (n+1) = true) : (endpointExpr n right e).scoped (n+1) = true := by
  cases right
  · exact hs
  · exact simplify_scoped (replace_scoped n hs (sub_scoped rfl (by simp [NExpr.scoped])))

lemma endpointExpr_semantics (e : Expr) (xs : List ℝ) (right : Bool) (t : ℝ) :
    (endpointExpr xs.length right e).real (xs++[t]) =
        e.real (xs++[if right then 1-t else t]) ∧
      ((endpointExpr xs.length right e).Converges (xs++[t]) ↔
        e.Converges (xs++[if right then 1-t else t])) := by
  cases right
  · exact ⟨rfl,Iff.rfl⟩
  · exact mirror_semantics e xs t

lemma endpointBound_model {c : Ctx} (hc : c.Valid) {e : Expr} {env : Array CBox}
    (hs : e.scoped (env.size+1) = true) {δ : Dy} {right : Bool} {decay : Nat} {R : Dy}
    (h : endpointBound c e env δ right decay = some R)
    {X : Type} [TopologicalSpace X] [FirstCountableTopology X] {s : Set X}
    (p : ParameterPath X s env.size)
    (hm : ∀ x ∈ s, ∀ i < env.size, ((p.val x)[i]?.getD 0 : ℂ) ∈ env[i]!) :
    0 < δ.toReal ∧ δ.toReal ≤ 1/2 ∧ ∃ A : Scale,
      endpointErrorBound c δ A = some R ∧
      ∀ t ∈ Ioc (0:ℝ) δ.toReal,
        ContinuousOn (fun x => e.real (p.val x++[if right then 1-t else t])) s ∧
          ∀ x ∈ s, e.Converges (p.val x++[if right then 1-t else t]) ∧
            A.Mem t (e.real (p.val x++[if right then 1-t else t]):ℂ) := by
  unfold endpointBound at h
  split at h
  · simp at h
  · rename_i hguard
    have hg : δ.isPos = true ∧ Dy.leB δ (Dy.ofRatD 64 (1/2)) = true := by
      have hh := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hguard)
      exact ⟨by simpa using hh.1,by simpa using hh.2⟩
    have hd : 0 < δ.toReal := by
      dsimp only [Dy.toReal_def]
      exact Rat.cast_pos.mpr ((Dy.isPos_iff δ).mp hg.1)
    have hd1 : δ.toReal ≤ 1/2 := (Dy.toReal_le_of_leB hg.2).trans (by
      simpa only [Dy.toReal_def,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
        (Rat.cast_mono (K := ℝ) (Dy.ofRatD_le 64 (1/2))))
    let E := endpointExpr env.size right e
    let senv := (env.map scaleConst).push (Scale.mk 1 0 (CBox.ofReal Ival.one))
    cases hS : scaled (E.size+32) c δ decay E senv with
    | none => simp [E,senv,hS] at h
    | some A =>
      have hA : endpointErrorBound c δ A = some R := by
        simpa only [show endpointExpr env.size right e = E from rfl,
          show (env.map scaleConst).push (Scale.mk 1 0 (CBox.ofReal Ival.one)) = senv from rfl,
          hS,Bind.bind,Option.bind_some] using h
      refine ⟨hd,hd1,A,hA,?_⟩
      intro t ht
      let path := p.push (fun _ => t) continuousOn_const
      have hm' : ∀ x ∈ s, ∀ i < env.size+1,
          (senv[i]!).Mem t (((path.val x)[i]?.getD 0:ℝ):ℂ) := by
        apply ParameterPath.mem_push (R := fun i y => (senv[i]!).Mem t (y:ℂ)) p
        · intro x hx i hi
          have hip : i < senv.size := by simp [senv]; omega
          have hiMap : i < (env.map scaleConst).size := by simpa using hi
          rw [getElem!_pos senv i hip]
          change (((env.map scaleConst).push (Scale.mk 1 0 (CBox.ofReal Ival.one)))[i]).Mem t _
          rw [Array.getElem_push_lt hiMap,Array.getElem_map]
          simpa only [getElem!_pos env i hi] using scaleConst_sound (hm x hx i hi) t
        · intro x hx
          have hip : env.size < senv.size := by simp [senv]
          have hget : senv[env.size]! = Scale.mk 1 0 (CBox.ofReal Ival.one) := by
            rw [getElem!_pos senv env.size hip]
            dsimp only [senv]
            simpa only [Array.size_map] using
              (Array.getElem_push_eq (xs := env.map scaleConst)
                (x := Scale.mk 1 0 (CBox.ofReal Ival.one)))
          rw [hget]
          exact scaleVariable_sound t
      have hsc : E.scoped senv.size = true := by
        simpa only [senv,Array.size_push,Array.size_map] using endpointExpr_scoped (right := right) hs
      have hh := scaled_real_model hc ht.1 ht.2 (ht.2.trans (hd1.trans (by norm_num))) (E.size+32) E senv A hsc hS
        s (path.resize (by simp [senv])) (by simpa [senv,ParameterPath.resize] using hm')
      have he x (hx : x ∈ s) := endpointExpr_semantics e (p.val x) right t
      have he' : ∀ x ∈ s, E.real (path.val x) =
          e.real (p.val x++[if right then 1-t else t]) ∧
          (E.Converges (path.val x) ↔ e.Converges (p.val x++[if right then 1-t else t])) := by
        intro x hx
        simpa only [p.length x hx,E,path,ParameterPath.push] using he x hx
      exact ⟨hh.1.congr (fun x hx => (he' x hx).1.symm),fun x hx =>
        ⟨(he' x hx).2.mp (hh.2 x hx).1,(he' x hx).1 ▸ (hh.2 x hx).2⟩⟩



lemma endpointBound_real_sound {c : Ctx} (hc : c.Valid) {e : Expr} {env : Array CBox}
    (hs : e.scoped (env.size+1) = true) {δ : Dy} {right : Bool} {decay : Nat} {R : Dy}
    (h : endpointBound c e env δ right decay = some R)
    {X : Type} [TopologicalSpace X] [FirstCountableTopology X] {s : Set X}
    (p : ParameterPath X s env.size)
    (hm : ∀ x ∈ s, ∀ i < env.size, ((p.val x)[i]?.getD 0 : ℂ) ∈ env[i]!) :
    0 < δ.toReal ∧ δ.toReal ≤ 1/2 ∧
      ContinuousOn (fun x => ∫ u in (0:ℝ)..δ.toReal,
        e.real (p.val x++[if right then 1-u else u])) s ∧
      ∀ x ∈ s,
        IntervalIntegrable (fun u => e.real (p.val x++[if right then 1-u else u])) volume 0 δ.toReal ∧
        |∫ u in (0:ℝ)..δ.toReal, e.real (p.val x++[if right then 1-u else u])| ≤ R.toReal ∧
        ∀ u ∈ Ioc (0:ℝ) δ.toReal, e.Converges (p.val x++[if right then 1-u else u]) := by
  obtain ⟨hd,hd1,A,hA,hmodel⟩ := endpointBound_model hc hs h p hm
  obtain ⟨hp,r,hr,_⟩ := endpointErrorBound_value hc hA
  have hp' : (-1:ℝ) < (A.power:ℝ) := by exact_mod_cast hp
  let F : X → ℝ → ℝ := fun x u => e.real (p.val x++[if right then 1-u else u])
  have hmeas (x : X) : Measurable (F x) := by
    cases right
    · exact e.measurable_body (p.val x)
    · exact (e.measurable_body (p.val x)).comp (measurable_const.sub measurable_id)
  have hcoeff : ∀ z ∈ A.coeff, ‖z‖ ≤ r.toReal := by
    intro z hz
    exact (CBox.mem_norm (p := c.prec) hz).2 r hr
  let B : ℝ → ℝ := fun u => r.toReal*u^(A.power:ℝ)*(1-Real.log u)^A.logs
  have hdom : ∀ x ∈ s, ∀ u ∈ Ioo (0:ℝ) δ.toReal, ‖F x u‖ ≤ B u := by
    intro x hx u hu
    have hh := ((hmodel u ⟨hu.1,hu.2.le⟩).2 x hx).2.norm_le hu.1
      (hu.2.le.trans (hd1.trans (by norm_num))) hcoeff
    simpa only [F,B,Complex.norm_real,Real.norm_eq_abs] using hh
  have hB : IntegrableOn B (Ioo (0:ℝ) δ.toReal) := by
    have hh := (integrableOn_rpow_mul_one_sub_log_pow hp' A.logs).const_mul r.toReal
    apply IntegrableOn.mono_set (by simpa only [B,mul_assoc,IntegrableOn] using hh)
    exact Ioo_subset_Ioo le_rfl (hd1.trans (by norm_num))
  have hcont : ContinuousOn (fun x => ∫ u in Ioo (0:ℝ) δ.toReal, F x u) s := by
    apply MeasureTheory.continuousOn_of_dominated
      (fun x hx => (hmeas x).aestronglyMeasurable.restrict)
      (fun x hx => ae_restrict_of_forall_mem measurableSet_Ioo (fun u hu => hdom x hx u hu)) hB
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun u hu => (hmodel u ⟨hu.1,hu.2.le⟩).1)
  refine ⟨hd,hd1,hcont.congr (fun x hx => ?_),?_⟩
  · rw [intervalIntegral.integral_of_le hd.le,integral_Ioc_eq_integral_Ioo]
  · intro x hx
    have hpoint : ∀ u ∈ Ioo (0:ℝ) δ.toReal, A.Mem u (F x u:ℂ) :=
      fun u hu => ((hmodel u ⟨hu.1,hu.2.le⟩).2 x hx).2
    have hh := endpointErrorBound_sound hc hA hd (hd1.trans (by norm_num))
      (Complex.continuous_ofReal.measurable.comp (hmeas x)) hpoint
    have hiC : IntervalIntegrable (fun u => (F x u:ℂ)) volume 0 δ.toReal :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hd.le).mpr hh.1
    have hi : IntervalIntegrable (F x) volume 0 δ.toReal := ⟨hiC.1.re,hiC.2.re⟩
    have hcast : (∫ u in (0:ℝ)..δ.toReal, (F x u:ℂ)) =
        ((∫ u in (0:ℝ)..δ.toReal, F x u:ℝ):ℂ) :=
      Complex.ofRealCLM.intervalIntegral_comp_comm hi
    have hnorm := hh.2
    change ‖∫ u in (0:ℝ)..δ.toReal, (F x u:ℂ)‖ ≤ R.toReal at hnorm
    rw [hcast,Complex.norm_real,Real.norm_eq_abs] at hnorm
    exact ⟨hi,hnorm,fun u hu => ((hmodel u hu).2 x hx).1⟩



lemma zero_width_eq {I : Ival} {x y : ℝ}
    (hx : x ∈ I) (hy : y ∈ I)
    (h : (I.width.map (fun w => w.mantissa == 0)).getD false = true) : x = y := by
  cases hlo : I.lo with
  | none => simp [Ival.width,Ival.omap2,hlo] at h
  | some lo =>
    cases hhi : I.hi with
    | none => simp [Ival.width,Ival.omap2,hlo,hhi] at h
    | some hi =>
      have hm : (Dy.subU 64 hi lo).mantissa = 0 := by
        simpa only [Ival.width,Ival.omap2,hlo,hhi,Option.map_some,Option.getD_some,beq_iff_eq] using h
      have hw : (Dy.subU 64 hi lo).toRat = 0 := by
        simp only [Vendor.Dyadic.toRat_eq,hm,Int.cast_zero,zero_mul]
      have hle : hi.toReal ≤ lo.toReal := by
        have hh := Dy.le_subU 64 hi lo
        rw [hw] at hh
        have hh' : hi.toRat ≤ lo.toRat := sub_nonpos.mp hh
        exact Rat.cast_le.mpr hh'
      linarith [hx.1 lo hlo,hx.2 hi hhi,hy.1 lo hlo,hy.2 hi hhi]

lemma real_integral_widen {c : Ctx} {F : ℝ → ℝ} {a b : ℝ}
    {V : CBox} {L R : Dy}
    (hl : IntervalIntegrable F volume 0 a) (hm : IntervalIntegrable F volume a b)
    (hr : IntervalIntegrable F volume b 1)
    (hL : |∫ u in (0:ℝ)..a, F u| ≤ L.toReal)
    (hR : |∫ u in b..(1:ℝ), F u| ≤ R.toReal)
    (hV : ((∫ u in a..b, F u:ℝ):ℂ) ∈ V) :
    IntervalIntegrable F volume 0 1 ∧
      ((∫ u in (0:ℝ)..1, F u:ℝ):ℂ) ∈
        (⟨Ival.widen c.prec V.re (Dy.addU c.prec L R),
          Ival.widen c.prec V.im (Dy.addU c.prec L R)⟩ : CBox) := by
  have hi := hl.trans (hm.trans hr)
  have he : (∫ u in (0:ℝ)..1, F u) - (∫ u in a..b, F u) =
      (∫ u in (0:ℝ)..a, F u) + (∫ u in b..(1:ℝ), F u) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hl (hm.trans hr),
      ← intervalIntegral.integral_add_adjacent_intervals hm hr]
    ring
  have herr : |(∫ u in (0:ℝ)..1, F u)-(∫ u in a..b, F u)| ≤
      (Dy.addU c.prec L R).toReal := by
    rw [he]
    apply ((abs_add_le _ _).trans (add_le_add hL hR)).trans
    simpa only [Dy.toReal_def,Rat.cast_add] using (Rat.cast_mono (K := ℝ) (Dy.le_addU c.prec L R))
  have he0 : (0:ℝ) ≤ (Dy.addU c.prec L R).toReal := (abs_nonneg _).trans herr
  exact ⟨hi,⟨Ival.mem_widen hV.1 herr,Ival.mem_widen hV.2 (by simpa using he0)⟩⟩

end Lynth.Interval.Integral.Nested
