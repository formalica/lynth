module

import all Lynth.Interval.Integral.NestedEndpointSound

/-! Recursive convergence, real enclosures, and parameter continuity for complex bounds. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl Fns MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 2400000 in
theorem boundC_real_model {c : Ctx} (hc : c.Valid) :
    ∀ fuel (e : Expr) (env : Array CBox) (Z : CBox),
      e.scoped env.size = true → boundC fuel c e env = some Z →
      ∀ {X : Type} [TopologicalSpace X] [FirstCountableTopology X] (s : Set X)
        (p : ParameterPath X s env.size),
        (∀ x ∈ s, ∀ i < env.size, ((p.val x)[i]?.getD 0 : ℂ) ∈ env[i]!) →
        ContinuousOn (fun x => e.real (p.val x)) s ∧
          ∀ x ∈ s, e.Converges (p.val x) ∧ (e.real (p.val x) : ℂ) ∈ Z := by
  intro fuel
  induction fuel with
  | zero => intro e env Z hs h; simp [boundC] at h
  | succ fuel ih =>
    intro e env Z hs h X _ _ s p hm
    cases e with
    | var i =>
      rw [boundC.eq_2] at h
      have hi : i < env.size := by simpa [NExpr.scoped] using hs
      have he : env[i]! = Z := by
        simpa only [getElem!_pos env i hi,Array.getElem?_eq_getElem hi,Option.some.injEq] using h
      exact ⟨p.continuous i hi,fun x hx => ⟨trivial,he ▸ hm x hx i hi⟩⟩
    | rat q =>
      rw [boundC.eq_3] at h
      have he : CBox.ofReal (Ival.ofRat c.prec q) = Z := Option.some.inj h
      subst Z
      exact ⟨continuousOn_const,fun x hx => ⟨trivial,CBox.mem_ofReal (Ival.mem_ofRat c.prec q)⟩⟩
    | pi =>
      rw [boundC.eq_4] at h
      have he : CBox.ofReal c.pi = Z := Option.some.inj h
      subst Z
      exact ⟨continuousOn_const,fun x hx => ⟨trivial,CBox.mem_ofReal hc.pi_mem⟩⟩
    | unary op a =>
      rw [boundC.eq_5] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,hU⟩ := h
      have ha := ih a env A hs hA s p hm
      exact ⟨unaryC_continuousOn hc ha.1 (fun x hx => (ha.2 x hx).2) hU,
        fun x hx => ⟨(ha.2 x hx).1,unaryC_real_sound hc op (ha.2 x hx).2 hU⟩⟩
    | binary op a b =>
      by_cases hspecial : ∃ b0 n, op = .div ∧ b = .pow b0 n
      · obtain ⟨b0,n,rfl,rfl⟩ := hspecial
        rw [boundC.eq_6] at h
        simp only [Bind.bind,Option.bind_eq_some_iff] at h
        obtain ⟨A,hA,B,hB,BI,hBI,hM⟩ := h
        have hsc := Bool.and_eq_true_iff.mp hs
        have ha := ih a env A hsc.1 hA s p hm
        have hb := ih b0 env B hsc.2 hB s p hm
        have hp : (CBox.normSq c.prec B).pos = true := by
          by_contra hn
          simp [unaryC,hn] at hBI
        have hn : ∀ x ∈ s, b0.real (p.val x) ≠ 0 :=
          fun x hx => cbox_real_ne_zero (hb.2 x hx).2 hp
        refine ⟨ha.1.div (hb.1.pow n) (fun x hx => pow_ne_zero n (hn x hx)),?_⟩
        intro x hx
        refine ⟨⟨(ha.2 x hx).1,(hb.2 x hx).1⟩,?_⟩
        have hi := unaryC_real_sound hc .inv (hb.2 x hx).2 hBI
        have hpow' : ((((b0.real (p.val x))⁻¹)^n:ℝ):ℂ) ∈ powC c.prec BI n := by
          simpa only [Unary.real,Complex.ofReal_pow,Complex.ofReal_inv] using
            powC_sound (p := c.prec) hi n
        have hv := binaryC_real_sound hc .mul (ha.2 x hx).2 hpow' hM
        simpa only [NExpr.real,Binary.real,div_eq_mul_inv,inv_pow] using hv
      · rw [boundC.eq_7 c env fuel op a b (fun b0 n ho he => hspecial ⟨b0,n,ho,he⟩)] at h
        simp only [Bind.bind,Option.bind_eq_some_iff] at h
        obtain ⟨A,hA,B,hB,hM⟩ := h
        have hsc := Bool.and_eq_true_iff.mp hs
        have ha := ih a env A hsc.1 hA s p hm
        have hb := ih b env B hsc.2 hB s p hm
        exact ⟨binaryC_continuousOn ha.1 hb.1 (fun x hx => (hb.2 x hx).2) hM,
          fun x hx => ⟨⟨(ha.2 x hx).1,(hb.2 x hx).1⟩,
            binaryC_real_sound hc op (ha.2 x hx).2 (hb.2 x hx).2 hM⟩⟩
    | pow a n =>
      rw [boundC.eq_8] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,h⟩ := h
      split at h
      · have he : powC c.prec A n = Z := Option.some.inj h
        subst Z
        have ha := ih a env A hs hA s p hm
        exact ⟨ha.1.pow n,fun x hx => ⟨(ha.2 x hx).1,by
          simpa only [NExpr.real,Complex.ofReal_pow] using powC_sound (ha.2 x hx).2 n⟩⟩
      · simp at h
    | rpow a q =>
      rw [boundC.eq_9] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,hU⟩ := h
      have ha := ih a env A hs hA s p hm
      have hp : A.re.pos = true := by
        by_contra hn
        simp [rationalPowerC,hn] at hU
      exact ⟨ha.1.rpow_const (fun x hx => Or.inl (Ival.pos_of hp (ha.2 x hx).2.1).ne'),
        fun x hx => ⟨(ha.2 x hx).1,rationalPowerC_real_sound hc (ha.2 x hx).2 hU⟩⟩
    | integral k a b f =>
      rw [boundC.eq_10] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,B,hB,h⟩ := h
      have hsc := hs
      simp only [NExpr.scoped,Bool.and_eq_true] at hsc
      obtain ⟨⟨hsa,hsb⟩,hsf⟩ := hsc
      have ha := ih a env A hsa hA s p hm
      have hb := ih b env B hsb hB s p hm
      let P : CBox → Prop := fun J =>
        ContinuousOn (fun x => (NExpr.integral k a b f).real (p.val x)) s ∧
          ∀ x ∈ s, (NExpr.integral k a b f).Converges (p.val x) ∧
            ((NExpr.integral k a b f).real (p.val x):ℂ) ∈ J
      let W := CBox.sub c.prec B A
      let Y := CBox.add c.prec A (CBox.mul c.prec W (CBox.ofReal unit))
      have hproper (hk : k.finite = true)
          (horder : k ≠ .interval → Ival.leB A.re B.re = true) {V : CBox}
          (hV : boundC fuel c f (env.push Y) = some V) : P (CBox.mul c.prec W V) := by
        let afun : X → ℝ := fun x => a.real (p.val x)
        let wfun : X → ℝ := fun x => b.real (p.val x)-a.real (p.val x)
        have hwcont : ContinuousOn wfun s := hb.1.sub ha.1
        have hwmem : ∀ x ∈ s, (wfun x:ℂ) ∈ W := by
          intro x hx
          simpa only [wfun,Complex.ofReal_sub] using CBox.mem_sub (p := c.prec) (hb.2 x hx).2 (ha.2 x hx).2
        let sp : Set (X × ℝ) := s ×ˢ Icc (0:ℝ) 1
        let base : ParameterPath (X × ℝ) sp env.size :=
          p.comp Prod.fst continuous_fst.continuousOn (fun q hq => hq.1)
        have hxy : ContinuousOn (fun q : X × ℝ => afun q.1+wfun q.1*q.2) sp :=
          (ha.1.comp continuous_fst.continuousOn (fun q hq => hq.1)).add
            ((hwcont.comp continuous_fst.continuousOn (fun q hq => hq.1)).mul continuous_snd.continuousOn)
        let path := base.push (fun q : X × ℝ => afun q.1+wfun q.1*q.2) hxy
        have henv : ∀ q ∈ sp, ∀ i < env.size+1,
            (((path.val q)[i]?.getD 0:ℝ):ℂ) ∈ (env.push Y)[i]! := by
          apply ParameterPath.mem_push (R := fun i y => (y:ℂ) ∈ (env.push Y)[i]!) base
          · intro q hq i hi
            have hip : i < (env.push Y).size := by simp; omega
            simpa only [base,ParameterPath.comp,getElem!_pos (env.push Y) i hip,
              Array.getElem_push_lt hi,getElem!_pos env i hi] using hm q.1 hq.1 i hi
          · intro q hq
            have hu : q.2 ∈ unit := Ival.mem_ofRats (by simpa using hq.2.1) (by simpa using hq.2.2)
            have hy := CBox.mem_add (p := c.prec) (ha.2 q.1 hq.1).2
              (CBox.mem_mul (p := c.prec) (hwmem q.1 hq.1) (CBox.mem_ofReal hu))
            simpa only [Y,getElem!_pos (env.push Y) env.size (by simp),Array.getElem_push_eq,
              afun,Complex.ofReal_add,Complex.ofReal_mul] using hy
        have hf := ih f (env.push Y) V (by simpa using hsf) hV sp (path.resize (by simp))
          (by simpa only [Array.size_push,ParameterPath.resize] using henv)
        let g : X × ℝ → ℝ := fun q => f.real (p.val q.1++[afun q.1+wfun q.1*q.2])
        have hg : ContinuousOn g sp := by
          simpa only [g,path,ParameterPath.push,ParameterPath.resize,base,ParameterPath.comp] using hf.1
        let G : X × ℝ → ℝ := fun q => wfun q.1*g q
        have hG : ContinuousOn G sp := by
          simpa only [G,Function.comp_def,Pi.mul_def] using
            (hwcont.comp continuous_fst.continuousOn (fun q hq => hq.1)).mul hg
        have hpoint : ∀ x ∈ s, ∀ u ∈ Icc (0:ℝ) 1,
            f.Converges (p.val x++[afun x+wfun x*u]) ∧ (g (x,u):ℂ) ∈ V := by
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
            exact Ival.le_of_leB (ha.2 x hx).2.1 (hb.2 x hx).2.1 (horder hki)
          · intro u hu
            exact (hpoint x hx u ⟨hu.1.le,hu.2.le⟩).1
        refine ⟨(continuousOn_unitIntegral hG).congr (fun x hx => (hsem x hx).2),?_⟩
        intro x hx
        refine ⟨(hsem x hx).1,?_⟩
        rw [(hsem x hx).2]
        have hgcont : ContinuousOn (fun u => g (x,u)) (Icc (0:ℝ) 1) :=
          hg.comp (continuous_const.prodMk continuous_id).continuousOn (fun u hu => ⟨hx,hu⟩)
        have higi := hgcont.intervalIntegrable_of_Icc (μ := volume) zero_le_one
        have hiC := (Complex.continuous_ofReal.comp_continuousOn hgcont).intervalIntegrable_of_Icc (μ := volume) zero_le_one
        have hmean := cbox_intervalIntegral_mem_unit hiC (fun u hu => (hpoint x hx u ⟨hu.1.le,hu.2.le⟩).2)
        have hcast : (∫ u in (0:ℝ)..1, (g (x,u):ℂ)) = ((∫ u in (0:ℝ)..1, g (x,u):ℝ):ℂ) :=
          Complex.ofRealCLM.intervalIntegral_comp_comm higi
        change (∫ u in (0:ℝ)..1, (g (x,u):ℂ)) ∈ V at hmean
        rw [hcast] at hmean
        have hh := CBox.mem_mul (p := c.prec) (hwmem x hx) hmean
        simpa only [G,intervalIntegral.integral_const_mul,Complex.ofReal_mul] using hh
      let how := if k.finite then Change.affine else if k == .right then Change.right else Change.left
      let E := transformed env.size how a b f
      have hsE : E.scoped (env.size+1) = true := transformed_scoped hsa hsb hsf
      have htruncated (hkw : k ≠ .whole)
          (horder : k.finite = true → k ≠ .interval → Ival.leB A.re B.re = true)
          (d : Dy) (V : CBox) (L R : Dy)
          (hV : boundC fuel c E (env.push (CBox.ofReal (Ival.ofRats c.prec d.toRat (1-d.toRat)))) = some V)
          {dl dr : Nat}
          (hL : endpointBound c E env d false dl = some L)
          (hR : endpointBound c E env d true dr = some R) :
          P (let mid := CBox.mul c.prec (CBox.ofReal (Ival.ofRat c.prec (1-2*d.toRat))) V
            let err := Dy.addU c.prec L R
            ⟨Ival.widen c.prec mid.re err,Ival.widen c.prec mid.im err⟩) := by
        obtain ⟨hd,hd1,hlcont,hlgood⟩ := endpointBound_real_sound hc hsE hL p hm
        obtain ⟨_,_,hrcont,hrgood⟩ := endpointBound_real_sound hc hsE hR p hm
        simp only [Bool.false_eq_true,↓reduceIte] at hlcont hlgood hrcont hrgood
        have hab : d.toReal ≤ 1-d.toReal := by linarith
        let T := Ival.ofRats c.prec d.toRat (1-d.toRat)
        let sp : Set (X × ℝ) := s ×ˢ Icc d.toReal (1-d.toReal)
        let base : ParameterPath (X × ℝ) sp env.size :=
          p.comp Prod.fst continuous_fst.continuousOn (fun q hq => hq.1)
        let path := base.push Prod.snd continuous_snd.continuousOn
        have henv : ∀ q ∈ sp, ∀ i < env.size+1,
            (((path.val q)[i]?.getD 0:ℝ):ℂ) ∈ (env.push (CBox.ofReal T))[i]! := by
          apply ParameterPath.mem_push (R := fun i y => (y:ℂ) ∈ (env.push (CBox.ofReal T))[i]!) base
          · intro q hq i hi
            have hip : i < (env.push (CBox.ofReal T)).size := by simp; omega
            simpa only [base,ParameterPath.comp,getElem!_pos (env.push (CBox.ofReal T)) i hip,
              Array.getElem_push_lt hi,getElem!_pos env i hi] using hm q.1 hq.1 i hi
          · intro q hq
            have hu : q.2 ∈ T := Ival.mem_ofRats
              (by simpa only [Dy.toReal_def] using hq.2.1)
              (by simpa only [Dy.toReal_def,Rat.cast_sub,Rat.cast_one] using hq.2.2)
            simpa only [getElem!_pos (env.push (CBox.ofReal T)) env.size (by simp),
              Array.getElem_push_eq] using CBox.mem_ofReal hu
        have hf := ih E (env.push (CBox.ofReal T)) V (by simpa using hsE) hV
          sp (path.resize (by simp)) (by simpa only [Array.size_push,ParameterPath.resize] using henv)
        have hmidcont : ContinuousOn (fun q : X × ℝ => E.real (p.val q.1++[q.2])) sp := by
          simpa only [path,ParameterPath.push,ParameterPath.resize,base,ParameterPath.comp] using hf.1
        have hmidgood x (hx : x ∈ s) : IntervalIntegrable
            (fun u => E.real (p.val x++[u])) volume d.toReal (1-d.toReal) := by
          simpa only [Function.comp_def,Function.id_def] using (hmidcont.comp
            (continuous_const.prodMk continuous_id).continuousOn
            (fun u hu => ⟨hx,hu⟩)).intervalIntegrable_of_Icc (μ := volume) hab
        have hrightEq (x : X) :
            (∫ u in (0:ℝ)..d.toReal, E.real (p.val x++[1-u])) =
              ∫ u in (1-d.toReal)..(1:ℝ), E.real (p.val x++[u]) := by
          simpa only [sub_zero] using (intervalIntegral.integral_comp_sub_left
            (f := fun u => E.real (p.val x++[u])) (a := 0) (b := d.toReal) 1)
        have hrightgood x (hx : x ∈ s) :
            IntervalIntegrable (fun u => E.real (p.val x++[u])) volume (1-d.toReal) 1 := by
          simpa only [sub_sub_cancel,sub_zero] using ((hrgood x hx).1.comp_sub_left 1).symm
        have hrightcont := hrcont.congr (fun x hx => (hrightEq x).symm)
        have htotal : ContinuousOn (fun x => ∫ u in (0:ℝ)..1, E.real (p.val x++[u])) s := by
          apply ((hlcont.add (continuousOn_intervalIntegral hab hmidcont)).add hrightcont).congr
          intro x hx
          dsimp only [Pi.add_apply]
          rw [← intervalIntegral.integral_add_adjacent_intervals
            ((hlgood x hx).1.trans (hmidgood x hx)) (hrightgood x hx),
            ← intervalIntegral.integral_add_adjacent_intervals (hlgood x hx).1 (hmidgood x hx)]
        have hhow : how.Admissible k := by
          cases k <;> try rfl
          exact (hkw rfl).elim
        have hfull : ∀ x ∈ s,
            IntervalIntegrable (fun u => E.real (p.val x++[u])) volume 0 1 ∧
              ((∫ u in (0:ℝ)..1, E.real (p.val x++[u]):ℝ):ℂ) ∈
                (let mid := CBox.mul c.prec (CBox.ofReal (Ival.ofRat c.prec (1-2*d.toRat))) V
                 let err := Dy.addU c.prec L R
                 ⟨Ival.widen c.prec mid.re err,Ival.widen c.prec mid.im err⟩ : CBox) := by
          intro x hx
          apply real_integral_widen (hlgood x hx).1 (hmidgood x hx) (hrightgood x hx)
            (hlgood x hx).2.1 (by simpa only [hrightEq x] using (hrgood x hx).2.1)
          obtain ⟨z,hz,he⟩ := cbox_real_integral_mean hab (hmidgood x hx)
            (fun u hu => (hf.2 (x,u) ⟨hx,hu⟩).2)
          rw [he]
          apply CBox.mem_mul (p := c.prec) _ hz
          apply CBox.mem_ofReal
          have hw : (1-d.toReal)-d.toReal = ((1-2*d.toRat:ℚ):ℝ) := by
            simp only [Dy.toReal_def,Rat.cast_sub,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat]
            ring
          rw [hw]
          exact Ival.mem_ofRat c.prec (1-2*d.toRat)
        have hsem : ∀ x ∈ s, (NExpr.integral k a b f).Converges (p.val x) ∧
            (NExpr.integral k a b f).real (p.val x) = ∫ u in (0:ℝ)..1, E.real (p.val x++[u]) := by
          intro x hx
          have hcan : (NExpr.integral .interval (.rat 0) (.rat 1) E).Converges (p.val x) := by
            refine ⟨trivial,trivial,?_,?_⟩
            · simpa only [NDomain.Converges,NExpr.real,Rat.cast_zero,Rat.cast_one] using (hfull x hx).1
            intro u hu
            have hu' : u ∈ Ioo (0:ℝ) 1 := by
              simpa only [NExpr.real,Rat.cast_zero,Rat.cast_one,uIoo_of_le zero_le_one] using hu
            by_cases hl : u ≤ d.toReal
            · exact (hlgood x hx).2.2 u ⟨hu'.1,hl⟩
            · by_cases hr : 1-d.toReal ≤ u
              · have hh := (hrgood x hx).2.2 (1-u) ⟨by linarith [hu'.2],by linarith⟩
                simpa only [sub_sub_cancel] using hh
              · exact (hf.2 (x,u) ⟨hx,⟨(le_of_not_ge hl),le_of_lt (lt_of_not_ge hr)⟩⟩).1
          have hh := transformed_integral_transport hhow
            (by simpa only [p.length x hx] using hsa) (by simpa only [p.length x hx] using hsb)
            (by simpa only [p.length x hx] using hsf) (ha.2 x hx).1 (hb.2 x hx).1
            (fun hfin hki => Ival.le_of_leB (ha.2 x hx).2.1 (hb.2 x hx).2.1 (horder hfin hki))
            (by simpa only [E,p.length x hx] using hcan)
          refine ⟨hh.1,?_⟩
          simpa only [E,p.length x hx,NExpr.real,NDomain.value,Rat.cast_zero,Rat.cast_one] using hh.2
        exact ⟨htotal.congr (fun x hx => (hsem x hx).2),fun x hx =>
          ⟨(hsem x hx).1,(hsem x hx).2.symm ▸ (hfull x hx).2⟩⟩
      let fallback : Option CBox := do
        for bits in ([4,8,16,32] : List Int) do
          let d : Dy := ⟨1,-bits⟩
          let T := Ival.ofRats c.prec d.toRat (1-d.toRat)
          if let some V := boundC fuel c E (env.push (CBox.ofReal T)) then
            for decay in ([2,4,8,16] : List Nat) do
              let some left := endpointBound c E env d false decay | continue
              let some right := endpointBound c E env d true decay | continue
              let mid := CBox.mul c.prec (CBox.ofReal (Ival.ofRat c.prec (1-2*d.toRat))) V
              let err := Dy.addU c.prec left right
              return ⟨Ival.widen c.prec mid.re err,Ival.widen c.prec mid.im err⟩
        none
      have hgeneric (hkw : k ≠ .whole)
          (horder : k.finite = true → k ≠ .interval → Ival.leB A.re B.re = true) :
          ∀ J, fallback = some J → P J := by
        let State := Option CBox × Unit
        let Inv : State → Prop := fun st => ∀ J, st.1 = some J → P J
        have hinit : Inv (none,()) := by intro J hJ; simp at hJ
        let substep : Dy → CBox → Nat → State → Option (ForInStep State) := fun d V decay _ =>
          match endpointBound c E env d false decay with
          | some left =>
            match endpointBound c E env d true decay with
            | some right =>
              let mid := CBox.mul c.prec (CBox.ofReal (Ival.ofRat c.prec (1-2*d.toRat))) V
              let err := Dy.addU c.prec left right
              pure (.done (some ⟨Ival.widen c.prec mid.re err,Ival.widen c.prec mid.im err⟩,()))
            | _ => pure (.yield (none,()))
          | _ => pure (.yield (none,()))
        have hsub d V (hV : boundC fuel c E
            (env.push (CBox.ofReal (Ival.ofRats c.prec d.toRat (1-d.toRat)))) = some V) :
            ∀ decay ∈ ([2,4,8,16] : List Nat), ∀ st out, Inv st →
              substep d V decay st = some out → Inv out.value := by
          intro decay _ st out _ hout
          cases hL : endpointBound c E env d false decay with
          | none =>
            have he : ForInStep.yield (none,()) = out := by simpa only [substep,hL,Option.pure_def,Option.some.injEq] using hout
            subst out
            exact hinit
          | some L =>
            cases hR : endpointBound c E env d true decay with
            | none =>
              have he : ForInStep.yield (none,()) = out := by simpa only [substep,hL,hR,Option.pure_def,Option.some.injEq] using hout
              subst out
              exact hinit
            | some R =>
              let mid := CBox.mul c.prec (CBox.ofReal (Ival.ofRat c.prec (1-2*d.toRat))) V
              let err := Dy.addU c.prec L R
              let J : CBox := ⟨Ival.widen c.prec mid.re err,Ival.widen c.prec mid.im err⟩
              have he : ForInStep.done (some J,()) = out := by
                simpa only [substep,hL,hR,mid,err,J,Option.pure_def,Option.some.injEq] using hout
              subst out
              intro K hK
              have hK' : J = K := Option.some.inj hK
              subst K
              exact htruncated hkw horder d V L R hV hL hR
        let step : Int → State → Option (ForInStep State) := fun bits _ =>
          let d : Dy := ⟨1,-bits⟩
          let T := Ival.ofRats c.prec d.toRat (1-d.toRat)
          match boundC fuel c E (env.push (CBox.ofReal T)) with
          | some V => do
            let st ← forIn ([2,4,8,16] : List Nat) (none,()) (substep d V)
            match st.1 with
            | some J => pure (.done (some J,()))
            | _ => pure (.yield (none,()))
          | _ => pure (.yield (none,()))
        have hstep : ∀ bits ∈ ([4,8,16,32] : List Int), ∀ st out, Inv st →
            step bits st = some out → Inv out.value := by
          intro bits _ st out _ hout
          let d : Dy := ⟨1,-bits⟩
          cases hV : boundC fuel c E (env.push (CBox.ofReal (Ival.ofRats c.prec d.toRat (1-d.toRat)))) with
          | none =>
            have he : ForInStep.yield (none,()) = out := by
              simpa only [step,show (⟨1,-bits⟩ : Dy) = d from rfl,hV,Option.pure_def,Option.some.injEq] using hout
            subst out
            exact hinit
          | some V =>
            cases hloop : forIn ([2,4,8,16] : List Nat) (none,()) (substep d V) with
            | none => simp only [step,show (⟨1,-bits⟩ : Dy) = d from rfl,hV,hloop,Bind.bind,Option.bind_none,reduceCtorEq] at hout
            | some result =>
              have hresult := list_forIn_preserves Inv (substep d V) [2,4,8,16] (hsub d V hV) hinit hloop
              cases hfound : result.1 with
              | none =>
                have he : ForInStep.yield (none,()) = out := by
                  simpa only [step,show (⟨1,-bits⟩ : Dy) = d from rfl,hV,hloop,Bind.bind,Option.bind_some,hfound,Option.pure_def,Option.some.injEq] using hout
                subst out
                exact hinit
              | some J =>
                have he : ForInStep.done (some J,()) = out := by
                  simpa only [step,show (⟨1,-bits⟩ : Dy) = d from rfl,hV,hloop,Bind.bind,Option.bind_some,hfound,Option.pure_def,Option.some.injEq] using hout
                subst out
                intro K hK
                have he : J = K := Option.some.inj hK
                subst K
                exact hresult J hfound
        intro J hj
        have hcode : fallback = ((forIn ([4,8,16,32] : List Int) (none,()) step).bind fun st =>
            match st.1 with | some r => pure r | none => none) := by
          dsimp only [fallback,step,substep,Bind.bind,Option.pure_def]
          congr 2
          · funext bits st
            cases hv : boundC fuel c E (env.push (CBox.ofReal
                (Ival.ofRats c.prec ((⟨1,-bits⟩ : Dy).toRat) (1-(⟨1,-bits⟩ : Dy).toRat)))) with
            | none => rfl
            | some V =>
              dsimp only
              congr 1
              funext st
              cases st.1 <;> rfl
          · funext st
            cases st.1 <;> rfl
        rw [hcode] at hj
        cases hloop : forIn ([4,8,16,32] : List Int) (none,()) step with
        | none => simp only [hloop,Option.bind_none,reduceCtorEq] at hj
        | some st =>
          have hs := list_forIn_preserves Inv step [4,8,16,32] hstep hinit hloop
          cases hfound : st.1 with
          | none => simp only [hloop,Option.bind_some,hfound,reduceCtorEq] at hj
          | some K =>
            have he : K = J := by simpa only [hloop,Option.bind_some,hfound,Option.pure_def,Option.some.injEq] using hj
            exact he ▸ hs K hfound
      let tail : Option CBox :=
        if k == .whole then do
          let anchor := center env.size f
          let C ← boundC fuel c anchor env
          let _ ← boundC fuel c f (env.push C)
          let R ← boundC fuel c (.integral .right anchor (.rat 0) f) env
          let L ← boundC fuel c (.integral .left anchor (.rat 0) f) env
          return CBox.add c.prec R L
        else if k.finite then
          if k != .interval && !Ival.leB A.re B.re then none else
            match boundC fuel c f (env.push Y) with
            | some V =>
              let out := CBox.mul c.prec W V
              if out.isFinite then pure out else fallback
            | _ => fallback
        else fallback
      have htail : ∀ J, tail = some J → P J := by
        intro J hj
        dsimp only [tail] at hj
        split at hj
        · rename_i hwhole
          have hkw : k = .whole := by simpa using hwhole
          subst k
          let anchor := center env.size f
          have hanchor := center_properties hsf
          simp only [Bind.bind,Option.bind_eq_some_iff] at hj
          obtain ⟨C,hC,F,hF,R,hR,L,hL,hj⟩ := hj
          have hJ : CBox.add c.prec R L = J := Option.some.inj hj
          subst J
          have hcA := ih anchor env C hanchor.1 hC s p hm
          let path := p.push (fun x => anchor.real (p.val x)) hcA.1
          have henv : ∀ x ∈ s, ∀ i < env.size+1,
              (((path.val x)[i]?.getD 0:ℝ):ℂ) ∈ (env.push C)[i]! := by
            apply ParameterPath.mem_push (R := fun i y => (y:ℂ) ∈ (env.push C)[i]!) p
            · intro x hx i hi
              have hip : i < (env.push C).size := by simp; omega
              simpa only [getElem!_pos (env.push C) i hip,Array.getElem_push_lt hi,
                getElem!_pos env i hi] using hm x hx i hi
            · intro x hx
              simpa only [getElem!_pos (env.push C) env.size (by simp),Array.getElem_push_eq] using (hcA.2 x hx).2
          have hfA := ih f (env.push C) F (by simpa using hsf) hF s
            (path.resize (by simp)) (by simpa only [Array.size_push,ParameterPath.resize] using henv)
          have hsr : (NExpr.integral .right anchor (.rat 0) f).scoped env.size = true := by
            simpa only [anchor,NExpr.scoped,hsf,Bool.and_true] using hanchor.1
          have hsl : (NExpr.integral .left anchor (.rat 0) f).scoped env.size = true := hsr
          have hr := ih (.integral .right anchor (.rat 0) f) env R hsr hR s p hm
          have hl := ih (.integral .left anchor (.rat 0) f) env L hsl hL s p hm
          have hsem : ∀ x ∈ s, (NExpr.integral .whole a b f).Converges (p.val x) ∧
              (NExpr.integral .whole a b f).real (p.val x) =
                (NExpr.integral .right anchor (.rat 0) f).real (p.val x) +
                  (NExpr.integral .left anchor (.rat 0) f).real (p.val x) := by
            intro x hx
            have hwhole := whole_split_at (hr.2 x hx).1.2.2.1 (hl.2 x hx).1.2.2.1
            refine ⟨⟨(ha.2 x hx).1,(hb.2 x hx).1,hwhole.1,?_⟩,hwhole.2⟩
            intro u _
            rcases lt_trichotomy u (anchor.real (p.val x)) with hlt | heq | hgt
            · exact (hl.2 x hx).1.2.2.2 u hlt
            · simpa only [heq,path,ParameterPath.resize,ParameterPath.push] using (hfA.2 x hx).1
            · exact (hr.2 x hx).1.2.2.2 u hgt
          refine ⟨(hr.1.add hl.1).congr (fun x hx => (hsem x hx).2),?_⟩
          intro x hx
          refine ⟨(hsem x hx).1,?_⟩
          rw [(hsem x hx).2,Complex.ofReal_add]
          exact CBox.mem_add (p := c.prec) (hr.2 x hx).2 (hl.2 x hx).2
        · rename_i hwhole
          have hkw : k ≠ .whole := by simpa using hwhole
          split at hj
          · rename_i hk
            split at hj
            · simp at hj
            · rename_i hguard
              have horder : k = .interval ∨ Ival.leB A.re B.re = true := by
                simpa only [Bool.and_eq_true,Bool.not_eq_true,Bool.not_eq_false,
                  bne_iff_ne,not_and_or,not_not,Bool.not_eq_false'] using hguard
              cases hV : boundC fuel c f (env.push Y) with
              | none => exact hgeneric hkw (fun _ hki => horder.resolve_left hki) J (by simpa only [hV] using hj)
              | some V =>
                simp only [hV] at hj
                split at hj
                · have hJ : CBox.mul c.prec W V = J := Option.some.inj hj
                  subst J
                  exact hproper hk (fun hki => horder.resolve_left hki) hV
                · exact hgeneric hkw (fun _ hki => horder.resolve_left hki) J hj
          · rename_i hk
            exact hgeneric hkw (fun hfin => (hk hfin).elim) J hj
      by_cases hzero : (k.finite && (a == b || (sameIval A.re B.re && exactPoint A.im 0 &&
          exactPoint B.im 0 && (A.re.width.map (fun w => w.mantissa == 0)).getD false))) = true
      · rw [if_pos hzero] at h
        have hz : k.finite = true ∧ (a = b ∨
            sameIval A.re B.re = true ∧ exactPoint A.im 0 = true ∧
              exactPoint B.im 0 = true ∧ (A.re.width.map (fun w => w.mantissa == 0)).getD false = true) := by
          simpa only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,and_assoc] using hzero
        have hZ : CBox.ofReal Ival.zero = Z := Option.some.inj h
        subst Z
        have hsem : ∀ x ∈ s, (NExpr.integral k a b f).Converges (p.val x) ∧
            (NExpr.integral k a b f).real (p.val x) = 0 := by
          intro x hx
          apply finite_integral_zero_width hz.1 (ha.2 x hx).1 (hb.2 x hx).1
          rcases hz.2 with heq | hbox
          · rw [heq]
          · have heq := sameIval_sound hbox.1
            exact zero_width_eq (ha.2 x hx).2.1 (heq.symm ▸ (hb.2 x hx).2.1) hbox.2.2.2
        exact ⟨continuousOn_const.congr (fun x hx => (hsem x hx).2),fun x hx =>
          ⟨(hsem x hx).1,(hsem x hx).2.symm ▸ CBox.mem_ofReal Ival.mem_zero⟩⟩
      · rw [if_neg hzero] at h
        cases hform : formula env.size k a b f with
        | none =>
          apply htail Z
          simp only [hform,Bind.bind] at h
          dsimp only [tail,W,Y,how,E,fallback,Bind.bind]
          convert h using 1 <;> congr!
        | some form =>
          have hscope := formula_scoped hsa hsb hsf hform
          have finish (hv : boundC fuel c form.value env = some Z)
              (hg : ∀ x ∈ s, ∀ g ∈ form.nonnegative, 0 ≤ g.real (p.val x)) : P Z := by
            have hh := ih form.value env Z hscope.1 hv s p hm
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
            cases hG : boundC fuel c guard env with
            | none => simp [hg,hG] at h
            | some G =>
              by_cases hnon : G.re.nonneg = true
              · apply finish (by simpa [hg,hG,hnon] using h)
                have hgs : guard.scoped env.size = true := hscope.2 guard (by simp [hg])
                have hguard := ih guard env G hgs hG s p hm
                intro x hx g hgm
                have he : g = guard := by simpa [hg] using hgm.symm
                subst g
                exact Ival.nonneg_of hnon (hguard.2 x hx).2.1
              · apply htail Z
                have hh := h
                simp only [hg,Option.toList_some,List.forIn_cons,List.forIn_nil,
                  hG,Bind.bind,Option.bind_some,Bool.true_and,hnon,↓reduceIte] at hh
                dsimp only [tail,W,Y,how,E,fallback,Bind.bind]
                convert hh using 1 <;> congr!




theorem boundC_real_sound {c : Ctx} (hc : c.Valid) {fuel : Nat}
    {e : Expr} {env : Array CBox} {xs : List ℝ} {Z : CBox}
    (hs : e.scoped env.size = true) (hl : xs.length = env.size)
    (hm : ∀ i < env.size, ((xs[i]?.getD 0 : ℝ):ℂ) ∈ env[i]!)
    (h : boundC fuel c e env = some Z) :
    e.Converges xs ∧ (e.real xs:ℂ) ∈ Z := by
  let p : ParameterPath Unit Set.univ env.size :=
    ⟨fun _ => xs,fun _ _ => hl,fun _ _ => continuousOn_const⟩
  exact (boundC_real_model hc fuel e env Z hs h Set.univ p
    (fun _ _ => hm)).2 () (Set.mem_univ ())

end Lynth.Interval.Integral.Nested
