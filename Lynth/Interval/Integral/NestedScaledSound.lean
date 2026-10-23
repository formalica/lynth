module

import all Lynth.Interval.Integral.NestedRangeModel

/-! Soundness and continuous real parameter dependence of the endpoint evaluator. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl Fns MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1600000 in
theorem scaled_real_model {c : Ctx} (hc : c.Valid) {δ : Dy} {decay : Nat} {t : ℝ}
    (ht : 0 < t) (htδ : t ≤ δ.toReal) (ht1 : t ≤ 1) :
    ∀ fuel (e : Expr) (env : Array Scale) (V : Scale),
      e.scoped env.size = true → scaled fuel c δ decay e env = some V →
      ∀ {X : Type} [TopologicalSpace X] [FirstCountableTopology X] (s : Set X)
        (p : ParameterPath X s env.size),
        (∀ x ∈ s, ∀ i < env.size, (env[i]!).Mem t (((p.val x)[i]?.getD 0 : ℝ):ℂ)) →
        ContinuousOn (fun x => e.real (p.val x)) s ∧
          ∀ x ∈ s, e.Converges (p.val x) ∧ V.Mem t (e.real (p.val x) : ℂ) := by
  intro fuel
  induction fuel with
  | zero => intro e env V hs h; simp [scaled] at h
  | succ fuel ih =>
    intro e env V hs h X _ _ s p hm
    have unary_step (op : Unary) (a : Expr) (hsa : a.scoped env.size = true)
        (ha : (do let A ← scaled fuel c δ decay a env
                  scaleUnary c δ decay op A) = some V) :
        ContinuousOn (fun x => (NExpr.unary op a).real (p.val x)) s ∧
          ∀ x ∈ s, (NExpr.unary op a).Converges (p.val x) ∧
            V.Mem t ((NExpr.unary op a).real (p.val x) : ℂ) := by
      simp only [Bind.bind,Option.bind_eq_some_iff] at ha
      obtain ⟨A,hA,hU⟩ := ha
      have hh := ih a env A hsa hA s p hm
      exact ⟨scaleUnary_continuousOn hc ht htδ ht1 hh.1 (fun x hx => (hh.2 x hx).2) hU,
        fun x hx => ⟨(hh.2 x hx).1,scaleUnary_real_sound hc ht htδ ht1 (hh.2 x hx).2 hU⟩⟩
    cases e with
    | var i =>
      rw [scaled.eq_2] at h
      have hi : i < env.size := by simpa [NExpr.scoped] using hs
      have he : env[i]! = V := by
        simpa only [getElem!_pos env i hi, Array.getElem?_eq_getElem hi,Option.some.injEq] using h
      exact ⟨p.continuous i hi,fun x hx => ⟨trivial,he ▸ hm x hx i hi⟩⟩
    | rat q =>
      rw [scaled.eq_3] at h
      have he : scaleConst (CBox.ofReal (Ival.ofRat c.prec q)) = V := Option.some.inj h
      subst V
      exact ⟨continuousOn_const, fun x hx => ⟨trivial,
        scaleConst_sound (CBox.mem_ofReal (Ival.mem_ofRat c.prec q)) t⟩⟩
    | pi =>
      rw [scaled.eq_4] at h
      have he : scaleConst (CBox.ofReal c.pi) = V := Option.some.inj h
      subst V
      exact ⟨continuousOn_const,fun x hx => ⟨trivial,scaleConst_sound (CBox.mem_ofReal hc.pi_mem) t⟩⟩
    | unary op a =>
      by_cases hvar : ∃ i, op = .log ∧ a = .var i
      · obtain ⟨i,rfl,rfl⟩ := hvar
        rw [scaled.eq_5] at h
        have hi : i < env.size := by simpa [NExpr.scoped] using hs
        cases hA : env[i]? with
        | none => simp [hA] at h
        | some A =>
          have hmem : ∀ x ∈ s, A.Mem t (((p.val x)[i]?.getD 0 : ℝ):ℂ) := by
            have he : env[i]! = A := by
              simpa only [getElem!_pos env i hi,Array.getElem?_eq_getElem hi,Option.some.injEq] using hA
            simpa only [he] using fun x hx => hm x hx i hi
          simp only [hA,Bind.bind,Option.bind_some] at h
          split at h
          · rename_i hspecial
            have hd : δ.toReal ≤ 1/2 := by
              have hle : Dy.leB δ (Dy.ofRatD 64 (1/2)) = true := by
                have hg := h
                unfold logEndpointScale at hg
                split at hg
                · simp at hg
                · rename_i hguard
                  simpa using (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hguard)).2
              exact (Dy.toReal_le_of_leB hle).trans (by simpa only [Dy.toReal_def,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_mono (K := ℝ) (Dy.ofRatD_le 64 (1/2))))
            have he : ∀ x ∈ s, (p.val x)[i]?.getD 0 = t := by
              intro x hx
              exact_mod_cast endpointVar_sound hspecial (hmem x hx)
            refine ⟨(continuousOn_const (c := Real.log t)).congr (fun x hx => ?_),fun x hx => ⟨trivial,?_⟩⟩
            · simp [NExpr.real,Unary.real,he x hx]
            · simpa [NExpr.real,Unary.real,he x hx] using logEndpointScale_real_sound hc ht htδ hd h
          · exact ⟨scaleUnary_continuousOn hc ht htδ ht1 (p.continuous i hi) hmem h,
              fun x hx => ⟨trivial,scaleUnary_real_sound hc ht htδ ht1 (hmem x hx) h⟩⟩
      · by_cases hone : ∃ i, op = .log ∧ a = .binary .sub (.rat 1) (.var i)
        · obtain ⟨i,rfl,rfl⟩ := hone
          change (do
            let A ← env[i]?
            if endpointVar A then logOneMinusEndpointScale c δ else
              scaleUnary c δ decay .log (← scaled fuel c δ decay (.binary .sub (.rat 1) (.var i)) env)) = some V at h
          have hi : i < env.size := by simpa [NExpr.scoped] using hs
          cases hA : env[i]? with
          | none => simp [hA] at h
          | some A =>
            simp only [hA,Bind.bind,Option.bind_some] at h
            split at h
            · rename_i hspecial
              have hd : δ.toReal ≤ 1/2 := by
                have hle : Dy.leB δ (Dy.ofRatD 64 (1/2)) = true := by
                  have hg := h
                  unfold logOneMinusEndpointScale at hg
                  split at hg
                  · simp at hg
                  · rename_i hguard
                    simpa using (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hguard)).2
                exact (Dy.toReal_le_of_leB hle).trans (by simpa only [Dy.toReal_def,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_mono (K := ℝ) (Dy.ofRatD_le 64 (1/2))))
              have heA : env[i]! = A := by
                simpa only [getElem!_pos env i hi,Array.getElem?_eq_getElem hi,Option.some.injEq] using hA
              have he : ∀ x ∈ s, (p.val x)[i]?.getD 0 = t := by
                intro x hx
                exact_mod_cast endpointVar_sound hspecial (heA ▸ hm x hx i hi)
              refine ⟨(continuousOn_const (c := Real.log (1-t))).congr (fun x hx => ?_),fun x hx => ⟨⟨trivial,trivial⟩,?_⟩⟩
              · simp [NExpr.real,Unary.real,Binary.real,he x hx]
              · simpa [NExpr.real,Unary.real,Binary.real,he x hx] using
                  logOneMinusEndpointScale_real_sound ht htδ hd h
            · exact unary_step .log _ (by simpa [NExpr.scoped] using hs) h
        · by_cases hrat : ∃ q, op = .log ∧ a = .rat q
          · obtain ⟨q,rfl,rfl⟩ := hrat
            rw [scaled.eq_7] at h
            have he : scaleConst (CBox.ofReal (unaryR c .log (Ival.ofRat c.prec q))) = V := Option.some.inj h
            subst V
            exact ⟨by simpa only [NExpr.real] using (continuousOn_const : ContinuousOn (fun _ : X => Unary.real .log q) s),
              fun x hx => ⟨trivial,scaledLogRat_real_sound hc q t⟩⟩
          · rw [scaled.eq_8 c δ decay env fuel op a
                (fun i ho ha => hvar ⟨i,ho,ha⟩)
                (fun i ho ha => hone ⟨i,ho,ha⟩)
                (fun q ho ha => hrat ⟨q,ho,ha⟩)] at h
            exact unary_step op a hs h
    | binary op a b =>
      rw [scaled.eq_9] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,B,hB,h⟩ := h
      have hsc := Bool.and_eq_true_iff.mp hs
      have ha := ih a env A hsc.1 hA s p hm
      have hb := ih b env B hsc.2 hB s p hm
      have fallback (op : Binary)
          (hF : (do return scaleConst (← binaryC c op (← collapse c δ A) (← collapse c δ B))) = some V) :
          ContinuousOn (fun x => op.real (a.real (p.val x)) (b.real (p.val x))) s ∧
            ∀ x ∈ s, a.Converges (p.val x) ∧ b.Converges (p.val x) ∧
              V.Mem t (op.real (a.real (p.val x)) (b.real (p.val x)):ℂ) := by
        simp only [Bind.bind,Option.bind_eq_some_iff] at hF
        obtain ⟨ZA,hZA,ZB,hZB,U,hU,hF⟩ := hF
        have he : scaleConst U = V := Option.some.inj hF
        subst V
        have hmA x hx := collapse_sound hc ht htδ ht1 (ha.2 x hx).2 hZA
        have hmB x hx := collapse_sound hc ht htδ ht1 (hb.2 x hx).2 hZB
        exact ⟨binaryC_continuousOn ha.1 hb.1 hmB hU,
          fun x hx => ⟨(ha.2 x hx).1,(hb.2 x hx).1,
            scaleConst_sound (binaryC_real_sound hc op (hmA x hx) (hmB x hx) hU) t⟩⟩
      cases op with
      | add => exact ⟨ha.1.add hb.1,fun x hx => ⟨⟨(ha.2 x hx).1,(hb.2 x hx).1⟩,
          by simpa [NExpr.real,Binary.real,Complex.ofReal_add] using
            scaleAdd_sound hc ht htδ ht1 (ha.2 x hx).2 (hb.2 x hx).2 h⟩⟩
      | sub => exact ⟨ha.1.sub hb.1,fun x hx => ⟨⟨(ha.2 x hx).1,(hb.2 x hx).1⟩,
          by simpa [NExpr.real,Binary.real,Complex.ofReal_sub] using
            scaleSub_sound hc ht htδ ht1 (ha.2 x hx).2 (hb.2 x hx).2 h⟩⟩
      | mul =>
        have he : scaleMul c A B = V := Option.some.inj h
        subst V
        exact ⟨ha.1.mul hb.1,fun x hx => ⟨⟨(ha.2 x hx).1,(hb.2 x hx).1⟩,by
          simpa [NExpr.real,Binary.real,Complex.ofReal_mul] using
            scaleMul_sound ht (ha.2 x hx).2 (hb.2 x hx).2⟩⟩
      | div =>
        have hp : (CBox.normSq c.prec B.coeff).pos = true := by
          by_contra hn
          simp [scaleDiv,hn] at h
        refine ⟨ha.1.div hb.1 (fun x hx => scale_real_ne_zero ht ht1 (hb.2 x hx).2 hp),?_⟩
        intro x hx
        exact ⟨⟨(ha.2 x hx).1,(hb.2 x hx).1⟩,by
          simpa [NExpr.real,Binary.real,Complex.ofReal_div] using
            scaleDiv_sound ht (ha.2 x hx).2 (hb.2 x hx).2 h⟩
      | max =>
        have hh := fallback .max h
        exact ⟨hh.1,fun x hx => ⟨⟨(hh.2 x hx).1,(hh.2 x hx).2.1⟩,(hh.2 x hx).2.2⟩⟩
      | min =>
        have hh := fallback .min h
        exact ⟨hh.1,fun x hx => ⟨⟨(hh.2 x hx).1,(hh.2 x hx).2.1⟩,(hh.2 x hx).2.2⟩⟩
    | pow a n =>
      rw [scaled.eq_10] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,h⟩ := h
      have he : scalePow c A n = V := Option.some.inj h
      subst V
      have ha := ih a env A hs hA s p hm
      exact ⟨ha.1.pow n,fun x hx => ⟨(ha.2 x hx).1,by
        simpa [NExpr.real,Complex.ofReal_pow] using scalePow_sound ht (ha.2 x hx).2 n⟩⟩
    | rpow a q =>
      rw [scaled.eq_11] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,h⟩ := h
      have ha := ih a env A hs hA s p hm
      split at h
      · simp at h
      · rename_i hl
        have hlogs : A.logs = 0 := by simpa using hl
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨U,hU,h⟩ := h
        have he : Scale.mk (A.power*q) 0 U = V := Option.some.inj h
        subst V
        have hpos : A.coeff.re.pos = true := by
          by_contra hn
          simp [rationalPowerC,hn] at hU
        have hxpos : ∀ x ∈ s, 0 < a.real (p.val x) := by
          intro x hx
          obtain ⟨y,hy,he⟩ := A.real_coeff ht ht1 (ha.2 x hx).2
          rw [he]
          exact mul_pos (A.weight_pos ht ht1) (Ival.pos_of hpos hy.1)
        exact ⟨ha.1.rpow_const (fun x hx => Or.inl (hxpos x hx).ne'),fun x hx =>
          ⟨(ha.2 x hx).1,scaleRpow_real_sound hc ht ht1 (ha.2 x hx).2 hlogs hU⟩⟩
    | integral k a b f =>
      rw [scaled.eq_12] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,B,hB,h⟩ := h
      have hsc := hs
      simp only [NExpr.scoped,Bool.and_eq_true] at hsc
      obtain ⟨⟨hsa,hsb⟩,hsf⟩ := hsc
      have ha := ih a env A hsa hA s p hm
      have hb := ih b env B hsb hB s p hm
      let tail : Option Scale := do
        if !k.finite then none else do
          let W ← scaleAdd c δ B A true
          if k != .interval && !W.coeff.re.nonneg then none else do
            let Y ← scaleAdd c δ A (scaleMul c W (scaleConst (CBox.ofReal unit)))
            let F ← scaled fuel c δ decay f (env.push Y)
            return scaleMul c W F
      have htail : ∀ J, tail = some J →
          ContinuousOn (fun x => (NExpr.integral k a b f).real (p.val x)) s ∧
            ∀ x ∈ s, (NExpr.integral k a b f).Converges (p.val x) ∧
              J.Mem t ((NExpr.integral k a b f).real (p.val x):ℂ) := by
        intro J hj
        dsimp only [tail] at hj
        split at hj
        · simp at hj
        · rename_i hk
          have hk : k.finite = true := by simpa using hk
          simp only [Bind.bind,Option.bind_eq_some_iff] at hj
          obtain ⟨W,hW,hj⟩ := hj
          split at hj
          · simp at hj
          · rename_i horder
            have horder : k = .interval ∨ W.coeff.re.nonneg = true := by
              simpa only [Bool.and_eq_true,Bool.not_eq_true, Bool.not_eq_false,
                bne_iff_ne,not_and_or,not_not,Bool.not_eq_false'] using horder
            simp only [Option.bind_eq_some_iff] at hj
            obtain ⟨Y,hY,F,hF,hj⟩ := hj
            have hJ : scaleMul c W F = J := Option.some.inj hj
            subst J
            let afun : X → ℝ := fun x => a.real (p.val x)
            let wfun : X → ℝ := fun x => b.real (p.val x)-a.real (p.val x)
            have hwcont : ContinuousOn wfun s := hb.1.sub ha.1
            have hwmem : ∀ x ∈ s, W.Mem t (wfun x:ℂ) := by
              intro x hx
              simpa only [wfun,Complex.ofReal_sub] using
                scaleSub_sound hc ht htδ ht1 (hb.2 x hx).2 (ha.2 x hx).2 hW
            let sp : Set (X × ℝ) := s ×ˢ Icc (0:ℝ) 1
            let base : ParameterPath (X × ℝ) sp env.size :=
              p.comp Prod.fst continuous_fst.continuousOn (fun q hq => hq.1)
            have hxy : ContinuousOn (fun q : X × ℝ => afun q.1+wfun q.1*q.2) sp :=
              (ha.1.comp continuous_fst.continuousOn (fun q hq => hq.1)).add
                ((hwcont.comp continuous_fst.continuousOn (fun q hq => hq.1)).mul
                  continuous_snd.continuousOn)
            let path := base.push (fun q : X × ℝ => afun q.1+wfun q.1*q.2) hxy
            have henv : ∀ q ∈ sp, ∀ i < env.size+1,
                ((env.push Y)[i]!).Mem t (((path.val q)[i]?.getD 0:ℝ):ℂ) := by
              apply ParameterPath.mem_push (R := fun i y => ((env.push Y)[i]!).Mem t (y:ℂ)) base
              · intro q hq i hi
                have hip : i < (env.push Y).size := by simp; omega
                simpa only [base,ParameterPath.comp, getElem!_pos (env.push Y) i hip,
                  Array.getElem_push_lt hi,getElem!_pos env i hi] using hm q.1 hq.1 i hi
              · intro q hq
                have hu : q.2 ∈ unit := Ival.mem_ofRats (by simpa using hq.2.1) (by simpa using hq.2.2)
                have hw := scaleMul_sound (c := c) ht (hwmem q.1 hq.1)
                  (scaleConst_sound (CBox.mem_ofReal hu) t)
                have hy := scaleAdd_sound hc ht htδ ht1 (ha.2 q.1 hq.1).2 hw hY
                simpa only [getElem!_pos (env.push Y) env.size (by simp),Array.getElem_push_eq,
                  afun,Complex.ofReal_add,Complex.ofReal_mul] using hy
            have hf := ih f (env.push Y) F (by simpa using hsf) hF sp (path.resize (by simp))
              (by simpa only [Array.size_push,ParameterPath.resize] using henv)
            let G : X × ℝ → ℝ := fun q => wfun q.1 *
              f.real (p.val q.1++[afun q.1+wfun q.1*q.2])
            have hG : ContinuousOn G sp := by
              simpa only [G,path,ParameterPath.push,ParameterPath.resize,base,ParameterPath.comp, Function.comp_def, Pi.mul_def] using
                (hwcont.comp continuous_fst.continuousOn (fun q hq => hq.1)).mul hf.1
            have hpoint : ∀ x ∈ s, ∀ u ∈ Icc (0:ℝ) 1,
                f.Converges (p.val x++[afun x+wfun x*u]) ∧
                  F.Mem t (f.real (p.val x++[afun x+wfun x*u]):ℂ) := by
              intro x hx u hu
              exact hf.2 (x,u) ⟨hx,hu⟩
            have hslice x (hx : x ∈ s) : ContinuousOn (fun u => G (x,u)) (Icc (0:ℝ) 1) :=
              hG.comp (continuous_const.prodMk continuous_id).continuousOn (fun u hu => ⟨hx,hu⟩)
            have hi x (hx : x ∈ s) := (hslice x hx).intervalIntegrable_of_Icc (μ := volume) zero_le_one
            have hsem : ∀ x ∈ s, (NExpr.integral k a b f).Converges (p.val x) ∧
                (NExpr.integral k a b f).real (p.val x) = ∫ u in (0:ℝ)..1, G (x,u) := by
              intro x hx
              refine finite_integral_of_affine hk (ha.2 x hx).1 (hb.2 x hx).1 ?_ (hi x hx) ?_
              · intro hki
                have hp := horder.resolve_left hki
                obtain ⟨y,hy,he⟩ := W.real_coeff ht ht1 (hwmem x hx)
                have hnonneg : 0 ≤ wfun x := by
                  rw [he]
                  exact mul_nonneg (W.weight_pos ht ht1).le (Ival.nonneg_of hp hy.1)
                exact sub_nonneg.mp hnonneg
              · intro u hu
                exact (hpoint x hx u ⟨hu.1.le,hu.2.le⟩).1
            refine ⟨(continuousOn_unitIntegral hG).congr (fun x hx => (hsem x hx).2),?_⟩
            intro x hx
            refine ⟨(hsem x hx).1,?_⟩
            rw [(hsem x hx).2]
            have hiC := (Complex.continuous_ofReal.comp_continuousOn (hslice x hx)).intervalIntegrable_of_Icc (μ := volume) zero_le_one
            have hmG : ∀ u ∈ Ioo (0:ℝ) 1, (scaleMul c W F).Mem t ((G (x,u):ℝ):ℂ) := by
              intro u hu
              simpa only [G,Complex.ofReal_mul] using scaleMul_sound (c := c) ht (hwmem x hx)
                (hpoint x hx u ⟨hu.1.le,hu.2.le⟩).2
            have hbound := scale_intervalIntegral_mem_unit ht ht1 hiC hmG
            have hcast : (∫ u in (0:ℝ)..1, ((G (x,u):ℝ):ℂ)) =
                ((∫ u in (0:ℝ)..1, G (x,u):ℝ):ℂ) :=
              Complex.ofRealCLM.intervalIntegral_comp_comm (hi x hx)
            change (scaleMul c W F).Mem t (∫ u in (0:ℝ)..1, ((G (x,u):ℝ):ℂ)) at hbound
            rwa [hcast] at hbound
      split at h
      · rename_i hzero
        have hh : k.finite = true ∧ a = b := by simpa only [Bool.and_eq_true,beq_iff_eq] using hzero
        have he : scaleZero = V := Option.some.inj h
        subst V
        have hzero x (hx : x ∈ s) := finite_integral_zero_width (f := f) hh.1
          (ha.2 x hx).1 (hb.2 x hx).1 (by rw [hh.2])
        exact ⟨continuousOn_const.congr (fun x hx => (hzero x hx).2),fun x hx =>
          ⟨(hzero x hx).1,(hzero x hx).2.symm ▸ scaleZero_sound t⟩⟩
      · cases hform : formula env.size k a b f with
        | none => exact htail V (by simpa only [hform,tail,Bind.bind] using h)
        | some form =>
          have hscope := formula_scoped hsa hsb hsf hform
          have finish (hv : scaled fuel c δ decay form.value env = some V)
              (hg : ∀ x ∈ s, ∀ g ∈ form.nonnegative, 0 ≤ g.real (p.val x)) :
              ContinuousOn (fun x => (NExpr.integral k a b f).real (p.val x)) s ∧
                ∀ x ∈ s, (NExpr.integral k a b f).Converges (p.val x) ∧
                  V.Mem t ((NExpr.integral k a b f).real (p.val x):ℂ) := by
            have hh := ih form.value env V hscope.1 hv s p hm
            have hsem x hx := formula_sound (by simpa only [p.length x hx] using hsa)
              (by simpa only [p.length x hx] using hsb) (ha.2 x hx).1 (hb.2 x hx).1
              (by simpa only [p.length x hx] using hform) (hg x hx)
            exact ⟨hh.1.congr (fun x hx => (hsem x hx).2),fun x hx =>
              ⟨(hsem x hx).1,(hsem x hx).2.symm ▸ (hh.2 x hx).2⟩⟩
          simp only [hform] at h
          cases hg : form.nonnegative with
          | none =>
            apply finish (by simpa [hg] using h)
            simp [hg]
          | some guard =>
            cases hG : scaled fuel c δ decay guard env with
            | none => simp [hg,hG] at h
            | some U =>
              by_cases hnon : scaleGuard c δ U false = true
              · apply finish (by simpa [hg,hG,hnon] using h)
                have hgs : guard.scoped env.size = true := hscope.2 guard (by simp [hg])
                have hguard := ih guard env U hgs hG s p hm
                intro x hx g hgm
                have he : g = guard := by simpa [hg] using hgm.symm
                subst g
                obtain ⟨y,hy,he⟩ := U.real_coeff ht ht1 (hguard.2 x hx).2
                rw [he]
                exact mul_nonneg (U.weight_pos ht ht1).le
                  (Ival.nonneg_of (show U.coeff.re.nonneg = true from hnon) hy.1)
              · exact htail V (by simpa [hg,hG,hnon,tail] using h)

end Lynth.Interval.Integral.Nested
