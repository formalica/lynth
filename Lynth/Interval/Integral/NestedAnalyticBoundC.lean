import Lynth.Interval.Integral.NestedAnalyticScaled
import Lynth.Interval.Integral.Panel

/-! Analytic soundness of recursive complex bounds and their Bernstein ellipse extension. -/

namespace Lynth.Interval.Integral.Nested.AnalyticWork
open Intgrl Fns MeasureTheory Set Metric
open scoped Topology
open private unit from Lynth.Interval.Integral.NestedBounds

set_option maxHeartbeats 3200000 in
lemma boundC_analytic_model {c : Ctx} (hc : c.Valid) {S : Set ℂ} (hS : Convex ℝ S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ interior S) :
    ∀ fuel (e : Expr) (env : Array CBox) (Z : CBox),
      e.scoped env.size = true → boundC fuel c e env = some Z →
      ∀ {α : Type} [TopologicalSpace α] [FirstCountableTopology α] {T : Set α}
        (p : BoxInputs S T env),
        ∃ v : BoxModel S T Z, ∀ z ∈ S, ∀ a ∈ T, ∀ xs : List ℝ,
          p.Realizes z a xs → v.family.val z a = (e.real xs:ℂ) := by
  intro fuel
  induction fuel with
  | zero => intro e env Z hs h; simp [boundC] at h
  | succ fuel ih =>
    intro e env Z hs h α _ _ T p
    cases e with
    | var i =>
      rw [boundC.eq_2] at h
      have hi : i < env.size := by simpa [NExpr.scoped] using hs
      have he : env[i]! = Z := by
        simpa only [getElem!_pos env i hi,Array.getElem?_eq_getElem hi,Option.some.injEq] using h
      subst Z
      exact ⟨p.get i hi,fun z hz a ha xs hx => hx.2 i hi⟩
    | rat q =>
      rw [boundC.eq_3] at h
      have he : CBox.ofReal (Ival.ofRat c.prec q) = Z := Option.some.inj h
      subst Z
      exact ⟨.constant (q:ℂ) (CBox.mem_ofReal (Ival.mem_ofRat c.prec q)),fun _ _ _ _ _ _ => rfl⟩
    | pi =>
      rw [boundC.eq_4] at h
      have he : CBox.ofReal c.pi = Z := Option.some.inj h
      subst Z
      exact ⟨.constant (Real.pi:ℂ) (CBox.mem_ofReal hc.pi_mem),fun _ _ _ _ _ _ => rfl⟩
    | unary op a =>
      rw [boundC.eq_5] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,hU⟩ := h
      obtain ⟨f,hf⟩ := ih a env A hs hA p
      obtain ⟨v,hv⟩ := f.unary hc op hU
      exact ⟨v,fun z hz u hu xs hx => hv z hz u hu _ (hf z hz u hu xs hx)⟩
    | binary op a b =>
      by_cases hspecial : ∃ b0 n, op = .div ∧ b = .pow b0 n
      · obtain ⟨b0,n,rfl,rfl⟩ := hspecial
        rw [boundC.eq_6] at h
        simp only [Bind.bind,Option.bind_eq_some_iff] at h
        obtain ⟨A,hA,B,hB,BI,hBI,hM⟩ := h
        have hsc := Bool.and_eq_true_iff.mp hs
        obtain ⟨f,hf⟩ := ih a env A hsc.1 hA p
        obtain ⟨g,hg⟩ := ih b0 env B hsc.2 hB p
        obtain ⟨gi,hgi⟩ := g.unary hc .inv hBI
        obtain ⟨gn,hgn⟩ := gi.pow (p := c.prec) n
        obtain ⟨v,hv⟩ := f.binary hc gn .mul hM
        refine ⟨v,?_⟩
        intro z hz u hu xs hx
        have hgin := hgi z hz u hu _ (hg z hz u hu xs hx)
        have hgnreal : gn.family.val z u = (((b0.real xs)⁻¹^n:ℝ):ℂ) := by
          rw [hgn,hgin]; simp only [Unary.real,Complex.ofReal_pow]
        have he := hv z hz u hu _ _ (hf z hz u hu xs hx) hgnreal
        simpa only [NExpr.real,Binary.real,div_eq_mul_inv,inv_pow] using he
      · rw [boundC.eq_7 c env fuel op a b (fun b0 n ho he => hspecial ⟨b0,n,ho,he⟩)] at h
        simp only [Bind.bind,Option.bind_eq_some_iff] at h
        obtain ⟨A,hA,B,hB,hM⟩ := h
        have hsc := Bool.and_eq_true_iff.mp hs
        obtain ⟨f,hf⟩ := ih a env A hsc.1 hA p
        obtain ⟨g,hg⟩ := ih b env B hsc.2 hB p
        obtain ⟨v,hv⟩ := f.binary hc g op hM
        exact ⟨v,fun z hz u hu xs hx => hv z hz u hu _ _ (hf z hz u hu xs hx) (hg z hz u hu xs hx)⟩
    | pow a n =>
      rw [boundC.eq_8] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,h⟩ := h
      split at h
      · have he : powC c.prec A n = Z := Option.some.inj h
        subst Z
        obtain ⟨f,hf⟩ := ih a env A hs hA p
        obtain ⟨v,hv⟩ := f.pow (p := c.prec) n
        exact ⟨v,fun z hz u hu xs hx => by
          rw [hv,hf z hz u hu xs hx]; simp only [NExpr.real,Complex.ofReal_pow]⟩
      · simp at h
    | rpow a q =>
      rw [boundC.eq_9] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,hU⟩ := h
      obtain ⟨f,hf⟩ := ih a env A hs hA p
      obtain ⟨v,hv⟩ := f.rpow hc q hU
      exact ⟨v,fun z hz u hu xs hx => hv z hz u hu _ (hf z hz u hu xs hx)⟩
    | integral k a b f =>
      rw [boundC.eq_10] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,B,hB,h⟩ := h
      have hsc := hs
      simp only [NExpr.scoped,Bool.and_eq_true] at hsc
      obtain ⟨⟨hsa,hsb⟩,hsf⟩ := hsc
      obtain ⟨fa,hfa⟩ := ih a env A hsa hA p
      obtain ⟨fb,hfb⟩ := ih b env B hsb hB p
      let P : CBox → Prop := fun J => ∃ v : BoxModel S T J,
        ∀ z ∈ S, ∀ u ∈ T, ∀ xs, p.Realizes z u xs →
          v.family.val z u = ((NExpr.integral k a b f).real xs:ℂ)
      let W := CBox.sub c.prec B A
      let Y := CBox.add c.prec A (CBox.mul c.prec W (CBox.ofReal unit))
      have hproper (hk : k.finite = true)
          (horder : k ≠ .interval → Ival.leB A.re B.re = true) {V : CBox}
          (hV : boundC fuel c f (env.push Y) = some V) : P (CBox.mul c.prec W V) := by
        let fw : BoxModel S T W := fb.sub fa
        let U : Set (α × ℝ) := T ×ˢ Icc (0:ℝ) 1
        let fal : BoxModel S U A := fa.reindex Prod.fst continuous_fst.continuousOn (fun q hq => hq.1)
        let fwl : BoxModel S U W := fw.reindex Prod.fst continuous_fst.continuousOn (fun q hq => hq.1)
        let fy : BoxModel S U Y := fal.add (fwl.mul BoxModel.unitModel)
        let pp := (p.reindex Prod.fst continuous_fst.continuousOn (show MapsTo Prod.fst U T from fun q hq => hq.1)).push fy
        obtain ⟨ff,hff⟩ := ih f (env.push Y) V (by simpa using hsf) hV pp
        let v : BoxModel S T (CBox.mul c.prec W V) := fw.mul ff.mean
        refine ⟨v,?_⟩
        intro z hz u hu xs hx
        have hw : fw.family.val z u = ((b.real xs-a.real xs:ℝ):ℂ) := by
          change fb.family.val z u-fa.family.val z u = _
          rw [hfb z hz u hu xs hx,hfa z hz u hu xs hx,Complex.ofReal_sub]
        have hordered : k ≠ .interval → a.real xs ≤ b.real xs := fun hki =>
          Ival.le_of_leB (p.real_sound hc hsa hA hz hu hx).2.1
            (p.real_sound hc hsb hB hz hu hx).2.1 (horder hki)
        have hbody : ∀ r ∈ Icc (0:ℝ) 1,
            ff.family.val z (u,r) = (f.real (xs++[a.real xs+(b.real xs-a.real xs)*r]):ℂ) := by
          intro r hr
          apply hff z hz (u,r) ⟨hu,hr⟩ _
          apply BoxInputs.push_realizes
          · exact p.reindex_realizes _ _ _ hx
          · change fa.family.val z u+fw.family.val z u*(r:ℂ) = _
            rw [hfa z hz u hu xs hx,hw]
            push_cast; rfl
        change fw.family.val z u*ff.mean.family.val z u = _
        rw [BoxModel.mean_val,hw]
        change _ = ((k.value (fun x => f.real (xs++[x])) (a.real xs) (b.real xs):ℝ):ℂ)
        rw [finite_value_affine hk hordered,← intervalIntegral.integral_ofReal,← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro r hr
        change ((b.real xs-a.real xs:ℝ):ℂ)*ff.family.val z (u,r) = _
        rw [hbody r (by simpa only [uIcc_of_le (zero_le_one : (0:ℝ)≤1)] using hr)]
        push_cast; rfl
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
        obtain ⟨hd,hd1,fl,hfl,hflreal⟩ := endpoint_analytic_model hc hS hz₀ hsE hL p
        obtain ⟨_,_,fr,hfr,hfrreal⟩ := endpoint_analytic_model hc hS hz₀ hsE hR p
        have hab : d.toReal ≤ 1-d.toReal := by linarith
        let D := Ival.ofRats c.prec d.toRat (1-d.toRat)
        let U : Set (α × ℝ) := T ×ˢ Icc d.toReal (1-d.toReal)
        let var : BoxModel S U (CBox.ofReal D) :=
          ⟨UniformFamily.const (fun q : α × ℝ => (q.2:ℂ))
            (Complex.continuous_ofReal.comp continuous_snd).continuousOn 1 zero_le_one
            (by intro q hq
                have hp : 0 ≤ q.2 := hd.le.trans hq.2.1
                have hu : q.2 ≤ 1 := hq.2.2.trans (by linarith)
                simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp] using hu),
            fun z hz q hq => CBox.mem_ofReal (Ival.mem_ofRats
              (by simpa only [Dy.toReal_def] using hq.2.1)
              (by simpa only [Dy.toReal_def,Rat.cast_sub,Rat.cast_one] using hq.2.2))⟩
        let pp := (p.reindex Prod.fst continuous_fst.continuousOn (show MapsTo Prod.fst U T from fun q hq => hq.1)).push var
        obtain ⟨ff,hff⟩ := ih E (env.push (CBox.ofReal D)) V (by simpa using hsE) hV pp
        have hwidth : (1-d.toReal)-d.toReal ∈ Ival.ofRat c.prec (1-2*d.toRat) := by
          have he : (1-d.toReal)-d.toReal = ((1-2*d.toRat:ℚ):ℝ) := by
            simp only [Dy.toReal_def,Rat.cast_sub,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat]; ring
          rw [he]; exact Ival.mem_ofRat _ _
        let fm := ff.integrate (prec := c.prec) hab hwidth
        refine ⟨⟨(fl.add fm.family).add fr,fun z hz u hu =>
          complex_add_widen (hfl z hz u hu) (fm.mem z hz u hu) (hfr z hz u hu)⟩,?_⟩
        intro z hz u hu xs hx
        have hpp : ∀ r ∈ Icc d.toReal (1-d.toReal), pp.Realizes z (u,r) (xs++[r]) := by
          intro r hr
          apply BoxInputs.push_realizes
          · exact p.reindex_realizes _ _ _ hx
          · rfl
        have hbody : ∀ r ∈ Icc d.toReal (1-d.toReal), ff.family.val z (u,r) = (E.real (xs++[r]):ℂ) :=
          fun r hr => hff z hz (u,r) ⟨hu,hr⟩ _ (hpp r hr)
        have hmidreal : fm.family.val z u = ((∫ r in d.toReal..(1-d.toReal), E.real (xs++[r]):ℝ):ℂ) := by
          rw [BoxModel.integrate_val,← intervalIntegral.integral_ofReal]
          apply intervalIntegral.integral_congr
          intro r hr
          exact hbody r (by simpa only [uIcc_of_le hab] using hr)
        have hmidcont : ContinuousOn (fun r => E.real (xs++[r])) (Icc d.toReal (1-d.toReal)) := by
          have hh := ff.family.continuous.comp
            (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn
            (show MapsTo (fun r : ℝ => (z,(u,r))) (Icc d.toReal (1-d.toReal))
              (thickening ff.family.radius S ×ˢ U) from
              fun r hr => ⟨self_subset_thickening ff.family.radius_pos S hz,hu,hr⟩)
          exact (Complex.continuous_re.comp_continuousOn hh).congr
            (fun r hr => by
              change E.real (xs++[r]) = (ff.family.val z (u,r)).re
              rw [hbody r hr,Complex.ofReal_re])
        have hm := hmidcont.intervalIntegrable_of_Icc (μ := volume) hab
        have hl := endpoint_real_data hc hsE hL hx.1 (p.real_mem hz hu hx)
        have hr := endpoint_real_data hc hsE hR hx.1 (p.real_mem hz hu hx)
        simp only [Bool.false_eq_true,Bool.true_eq,↓reduceIte] at hl hr
        have hrightEq : (∫ r in (0:ℝ)..d.toReal, E.real (xs++[1-r])) =
            ∫ r in (1-d.toReal)..(1:ℝ), E.real (xs++[r]) := by
          simpa only [sub_zero] using (intervalIntegral.integral_comp_sub_left
            (f := fun r => E.real (xs++[r])) (a := 0) (b := d.toReal) 1)
        have hri : IntervalIntegrable (fun r => E.real (xs++[r])) volume (1-d.toReal) 1 := by
          simpa only [Bool.true_eq,↓reduceIte,sub_sub_cancel,sub_zero] using (hr.1.comp_sub_left 1).symm
        have hcan : (NExpr.integral .interval (.rat 0) (.rat 1) E).Converges xs := by
          refine ⟨trivial,trivial,?_,?_⟩
          · simpa only [NDomain.Converges,NExpr.real,Rat.cast_zero,Rat.cast_one] using hl.1.trans (hm.trans hri)
          intro r hr'
          have hrr : r ∈ Ioo (0:ℝ) 1 := by
            simpa only [NExpr.real,Rat.cast_zero,Rat.cast_one,uIoo_of_le zero_le_one] using hr'
          by_cases hleft : r ≤ d.toReal
          · exact hl.2 r ⟨hrr.1,hleft⟩
          · by_cases hright : 1-d.toReal ≤ r
            · have hh := hr.2 (1-r) ⟨by linarith [hrr.2],by linarith⟩
              simpa only [Bool.true_eq,↓reduceIte,sub_sub_cancel] using hh
            · have hmiddle : r ∈ Icc d.toReal (1-d.toReal) := ⟨(le_of_not_ge hleft),le_of_lt (lt_of_not_ge hright)⟩
              exact (pp.real_sound hc (by simpa using hsE) hV hz ⟨hu,hmiddle⟩ (hpp r hmiddle)).1
        have hhow : how.Admissible k := by
          cases k <;> try rfl
          exact (hkw rfl).elim
        have hsem := transformed_integral_transport hhow
          (by simpa only [hx.1] using hsa) (by simpa only [hx.1] using hsb)
          (by simpa only [hx.1] using hsf) (p.real_sound hc hsa hA hz hu hx).1
          (p.real_sound hc hsb hB hz hu hx).1
          (fun hfin hki => Ival.le_of_leB (p.real_sound hc hsa hA hz hu hx).2.1
            (p.real_sound hc hsb hB hz hu hx).2.1 (horder hfin hki))
          (by simpa only [E,hx.1] using hcan)
        have hvalue : (NExpr.integral k a b f).real xs = ∫ r in (0:ℝ)..1, E.real (xs++[r]) := by
          simpa only [E,hx.1,NExpr.real,NDomain.value,Rat.cast_zero,Rat.cast_one] using hsem.2
        change fl.val z u+fm.family.val z u+fr.val z u = _
        rw [hflreal z hz u hu xs hx,hmidreal,hfrreal z hz u hu xs hx]
        simp only [Bool.false_eq_true,Bool.true_eq,↓reduceIte]
        rw [hrightEq,hvalue,← Complex.ofReal_add,← Complex.ofReal_add,
          intervalIntegral.integral_add_adjacent_intervals hl.1 hm,
          intervalIntegral.integral_add_adjacent_intervals (hl.1.trans hm) hri]
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
          have hsr : (NExpr.integral .right anchor (.rat 0) f).scoped env.size = true := by
            simpa only [anchor,NExpr.scoped,hsf,Bool.and_true] using hanchor.1
          have hsl : (NExpr.integral .left anchor (.rat 0) f).scoped env.size = true := hsr
          obtain ⟨fr,hfr⟩ := ih (.integral .right anchor (.rat 0) f) env R hsr hR p
          obtain ⟨fl,hfl⟩ := ih (.integral .left anchor (.rat 0) f) env L hsl hL p
          refine ⟨fr.add fl,?_⟩
          intro z hz u hu xs hx
          have hr := (p.real_sound hc hsr hR hz hu hx).1.2.2.1
          have hl := (p.real_sound hc hsl hL hz hu hx).1.2.2.1
          have hwhole := whole_split_at hr hl
          change fr.family.val z u+fl.family.val z u = _
          rw [hfr z hz u hu xs hx,hfl z hz u hu xs hx,← Complex.ofReal_add]
          exact congrArg (fun x : ℝ => (x:ℂ)) hwhole.2.symm
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
        have hzz : k.finite = true ∧ (a = b ∨
            sameIval A.re B.re = true ∧ exactPoint A.im 0 = true ∧
              exactPoint B.im 0 = true ∧ (A.re.width.map (fun w => w.mantissa == 0)).getD false = true) := by
          simpa only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,and_assoc] using hzero
        have hZ : CBox.ofReal Ival.zero = Z := Option.some.inj h
        subst Z
        refine ⟨.constant 0 (CBox.mem_ofReal Ival.mem_zero),?_⟩
        intro z hz u hu xs hx
        have ha := p.real_sound hc hsa hA hz hu hx
        have hb := p.real_sound hc hsb hB hz hu hx
        have heq : a.real xs = b.real xs := by
          rcases hzz.2 with heq | hbox
          · rw [heq]
          · have heq := sameIval_sound hbox.1
            exact zero_width_eq ha.2.1 (heq.symm ▸ hb.2.1) hbox.2.2.2
        have hsem := finite_integral_zero_width (f := f) hzz.1 ha.1 hb.1 heq
        simp only [hsem.2,Complex.ofReal_zero,BoxModel.constant,UniformFamily.const]
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
              (hg : ∀ z ∈ S, ∀ u ∈ T, ∀ xs, p.Realizes z u xs → ∀ g ∈ form.nonnegative, 0 ≤ g.real xs) : P Z := by
            obtain ⟨v,hv⟩ := ih form.value env Z hscope.1 hv p
            refine ⟨v,?_⟩
            intro z hz u hu xs hx
            have hsem := formula_sound (by simpa only [hx.1] using hsa) (by simpa only [hx.1] using hsb)
              (p.real_sound hc hsa hA hz hu hx).1 (p.real_sound hc hsb hB hz hu hx).1
              (by simpa only [hx.1] using hform) (hg z hz u hu xs hx)
            rw [hsem.2]
            exact hv z hz u hu xs hx
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
                intro z hz u hu xs hx g hgm
                have he : g = guard := by simpa [hg] using hgm.symm
                subst g
                have hgs : guard.scoped env.size = true := hscope.2 guard (by simp [hg])
                exact Ival.nonneg_of hnon (p.real_sound hc hgs hG hz hu hx).2.1
              · apply htail Z
                have hh := h
                simp only [hg,Option.toList_some,List.forIn_cons,List.forIn_nil,
                  hG,Bind.bind,Option.bind_some,Bool.true_and,hnon,↓reduceIte] at hh
                dsimp only [tail,W,Y,how,E,fallback,Bind.bind]
                convert hh using 1 <;> congr!

end Lynth.Interval.Integral.Nested.AnalyticWork

namespace Lynth.Interval.Integral.Nested.AnalyticWork
open Intgrl Fns MeasureTheory Set Metric
open scoped Topology

def rectangle (m X Y : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc (m-X) (m+X) ∧ z.im ∈ Icc (-Y) Y}

lemma rectangle_convex (m X Y : ℝ) : Convex ℝ (rectangle m X Y) :=
  (convex_Icc (𝕜 := ℝ) (m-X) (m+X)).linear_preimage Complex.reLm |>.inter
    ((convex_Icc (𝕜 := ℝ) (-Y) Y).linear_preimage Complex.imLm)

lemma rectangle_interior (m : ℝ) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    (m:ℂ) ∈ interior (rectangle m X Y) := by
  let U := Complex.re ⁻¹' Ioo (m-X) (m+X) ∩ Complex.im ⁻¹' Ioo (-Y) Y
  have hU : IsOpen U := (isOpen_Ioo.preimage Complex.continuous_re).inter
    (isOpen_Ioo.preimage Complex.continuous_im)
  have hm : (m:ℂ) ∈ U := by
    change (m-X < m ∧ m < m+X) ∧ -Y < 0 ∧ 0 < Y
    exact ⟨⟨by linarith,by linarith⟩,by linarith,hY⟩
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset (hU.mem_nhds hm) (fun z hz => ⟨⟨hz.1.1.le,hz.1.2.le⟩,hz.2.1.le,hz.2.2.le⟩)

lemma rectangle_norm {m X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    {z : ℂ} (hz : z ∈ rectangle m X Y) : ‖z‖ ≤ |m|+X+Y := by
  have hre : |z.re| ≤ |m|+X := abs_le.mpr ⟨by linarith [hz.1.1,neg_abs_le m],by linarith [hz.1.2,le_abs_self m]⟩
  have him : |z.im| ≤ Y := abs_le.mpr hz.2
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)

noncomputable def UniformFamily.identity {S : Set ℂ} {α : Type} [TopologicalSpace α]
    {T : Set α} {B : ℝ} (hB : 0 ≤ B) (hb : ∀ z ∈ S, ‖z‖ ≤ B) : UniformFamily S T where
  val z _ := z
  radius := 1
  radius_pos := zero_lt_one
  bound := B+1
  bound_nonneg := by linarith
  continuous := continuous_fst.continuousOn
  analytic _ _ := analyticOnNhd_id
  norm_le z hz _ _ := by
    obtain ⟨w,hw,hd⟩ := mem_thickening_iff.mp hz
    have hh := norm_add_le (z-w) w
    have he : z-w+w = z := sub_add_cancel _ _
    rw [he] at hh
    rw [dist_eq_norm] at hd
    linarith [hb w hw]

set_option maxHeartbeats 800000 in
lemma ellipse_extension {c : Ctx} (hc : c.Valid) {e : Expr} {env : Array Ival} {xs : List ℝ}
    (hl : xs.length = env.size) (hm : ∀ i < env.size, xs[i]?.getD 0 ∈ env[i]!)
    (hs : e.scoped (env.size+1) = true) {a b ρ : Dy} (hab : a.toReal < b.toReal)
    (hρ : 1 < ρ.toReal) {Z : CBox}
    (hZ : boundC (e.size+32) c e ((env.map CBox.ofReal).push (ellipseBox c a b ρ)) = some Z) :
    ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F ((affine a.toReal b.toReal) '' ellipse ρ.toReal) ∧
      (∀ z ∈ ellipse ρ.toReal, F (affine a.toReal b.toReal z) ∈ Z) ∧
      (∀ x ∈ Ioo a.toReal b.toReal, F x = (e.real (xs++[x]):ℂ)) := by
  let m := (a.toReal+b.toReal)/2
  let d := (b.toReal-a.toReal)/2
  let X := d*ellipseX ρ.toReal
  let Y := d*ellipseY ρ.toReal
  have hd : 0 < d := by dsimp [d]; linarith
  have hX : 0 < X := mul_pos hd (zero_lt_one.trans (ellipseX_pos hρ))
  have hY : 0 < Y := mul_pos hd (ellipseY_pos hρ)
  let S := rectangle m X Y
  have hS : Convex ℝ S := rectangle_convex m X Y
  have hcenter : (m:ℂ) ∈ interior S := rectangle_interior m hX hY
  have hbox : ∀ w ∈ S, w ∈ ellipseBox c a b ρ := by
    intro w hw
    let z := (w-(m:ℂ))/(d:ℂ)
    have hre : z.re = (w.re-m)/d := by simp [z,Complex.div_re,Complex.normSq_ofReal]; field_simp
    have him : z.im = w.im/d := by simp [z,Complex.div_im,Complex.normSq_ofReal]; field_simp
    have hzr : z ∈ (⟨Ival.ofRats c.prec (-((ρ.toRat+1/ρ.toRat)/2)) ((ρ.toRat+1/ρ.toRat)/2),
        Ival.ofRats c.prec (-((ρ.toRat-1/ρ.toRat)/2)) ((ρ.toRat-1/ρ.toRat)/2)⟩ : CBox) := by
      have hwr : m-X ≤ w.re ∧ w.re ≤ m+X := hw.1
      have hwi : -Y ≤ w.im ∧ w.im ≤ Y := hw.2
      have hrlo : -ellipseX ρ.toReal ≤ z.re := by rw [hre]; apply (le_div_iff₀ hd).mpr; dsimp [X] at hwr; linarith
      have hrhi : z.re ≤ ellipseX ρ.toReal := by rw [hre]; apply (div_le_iff₀ hd).mpr; dsimp [X] at hwr; linarith
      have hilo : -ellipseY ρ.toReal ≤ z.im := by rw [him]; apply (le_div_iff₀ hd).mpr; dsimp [Y] at hwi; linarith
      have hihi : z.im ≤ ellipseY ρ.toReal := by rw [him]; apply (div_le_iff₀ hd).mpr; dsimp [Y] at hwi; linarith
      constructor
      · exact Ival.mem_ofRats (by simpa [Dy.toReal_def,ellipseX,one_div] using hrlo)
          (by simpa [Dy.toReal_def,ellipseX,one_div] using hrhi)
      · exact Ival.mem_ofRats (by simpa [Dy.toReal_def,ellipseY,one_div] using hilo)
          (by simpa [Dy.toReal_def,ellipseY,one_div] using hihi)
    have hm' : m ∈ Ival.ofRat c.prec ((a.toRat+b.toRat)/2) := by
      simpa [m,Dy.toReal_def] using Ival.mem_ofRat c.prec ((a.toRat+b.toRat)/2)
    have hd' : d ∈ Ival.ofRat c.prec ((b.toRat-a.toRat)/2) := by
      simpa [d,Dy.toReal_def] using Ival.mem_ofRat c.prec ((b.toRat-a.toRat)/2)
    have hz := CBox.mem_add (p := c.prec) (CBox.mem_ofReal hm')
      (CBox.mem_mul (p := c.prec) (CBox.mem_ofReal hd') hzr)
    have he : (m:ℂ)+(d:ℂ)*z = w := by
      have hn : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      dsimp only [z]; field_simp; ring
    rw [he] at hz
    exact hz
  have hellipse : affine a.toReal b.toReal '' ellipse ρ.toReal ⊆ S := by
    rintro w ⟨z,hz,rfl⟩
    obtain ⟨hr,hi⟩ := ellipse_in_rectangle hρ hz
    change (affine a.toReal b.toReal z).re ∈ Icc (m-X) (m+X) ∧
      (affine a.toReal b.toReal z).im ∈ Icc (-Y) Y
    have hre : (affine a.toReal b.toReal z).re = m+d*z.re := by simp [affine,m,d]
    have him : (affine a.toReal b.toReal z).im = d*z.im := by simp [affine,d]
    rw [hre,him]
    exact ⟨⟨by nlinarith [(abs_le.mp hr).1],by nlinarith [(abs_le.mp hr).2]⟩,
      by nlinarith [(abs_le.mp hi).1],by nlinarith [(abs_le.mp hi).2]⟩
  let base : BoxInputs S (univ : Set Unit) (env.map CBox.ofReal) := {
    family := fun i => UniformFamily.const (fun _ => ((xs[i]?.getD 0:ℝ):ℂ)) continuousOn_const
      ‖((xs[i]?.getD 0:ℝ):ℂ)‖ (norm_nonneg _) (by simp)
    mem := by
      intro i hi z hz u hu
      have hin : i < env.size := by simpa using hi
      simpa only [getElem!_pos (env.map CBox.ofReal) i hi,Array.getElem_map,
        getElem!_pos env i hin,UniformFamily.const] using CBox.mem_ofReal (hm i hin)
  }
  let ident : BoxModel S (univ : Set Unit) (ellipseBox c a b ρ) := {
    family := UniformFamily.identity (by positivity : 0 ≤ |m|+X+Y)
      (fun z hz => rectangle_norm hX.le hY.le hz)
    mem := fun z hz _ _ => hbox z hz
  }
  let p := base.push ident
  obtain ⟨f,hf⟩ := boundC_analytic_model hc hS hcenter (e.size+32) e
    ((env.map CBox.ofReal).push (ellipseBox c a b ρ)) Z (by simpa using hs) hZ p
  refine ⟨fun z => f.family.val z (),(f.family.analytic () (mem_univ ())).mono
    (hellipse.trans (self_subset_thickening f.family.radius_pos S)),
    fun z hz => f.mem _ (hellipse ⟨z,hz,rfl⟩) () (mem_univ ()),?_⟩
  intro x hx
  have hxS : (x:ℂ) ∈ S := hellipse (real_mem_affine_ellipse hab hρ ⟨hx.1.le,hx.2.le⟩)
  apply hf (x:ℂ) hxS () (mem_univ ()) (xs++[x])
  apply BoxInputs.push_realizes
  · exact ⟨by simpa using hl,fun i hi => rfl⟩
  · rfl

end Lynth.Interval.Integral.Nested.AnalyticWork
