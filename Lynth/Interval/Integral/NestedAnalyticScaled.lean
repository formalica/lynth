module

import all Lynth.Interval.Integral.NestedAnalyticModels

/-! Analytic soundness of endpoint evaluation and the integrable tail models. -/

namespace Lynth.Interval.Integral.Nested.AnalyticWork
open Intgrl Fns MeasureTheory Set Metric
open scoped Topology

set_option maxHeartbeats 2400000 in
lemma scaled_analytic_model {c : Ctx} (hc : c.Valid) {S : Set ℂ} (hS : Convex ℝ S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ interior S) {δ : Dy} (hδ : δ.toReal ≤ 1/2) {decay : Nat} :
    ∀ fuel (e : Expr) (env : Array Scale) (V : Scale),
      e.scoped env.size = true → scaled fuel c δ decay e env = some V →
      ∀ {α : Type} [TopologicalSpace α] [FirstCountableTopology α] {T : Set α}
        {t : α → ℝ}, ContinuousOn t T → (∀ a ∈ T, 0 < t a) →
        (∀ a ∈ T, t a ≤ δ.toReal) → ∀ (p : ScaleInputs S T env),
        ∃ v : ScaleModel S T V, ∀ z ∈ S, ∀ a ∈ T, ∀ xs : List ℝ,
          p.Realizes t z a xs → v.actual t z a = (e.real xs:ℂ) := by
  have hδ1 : δ.toReal ≤ 1 := hδ.trans (by norm_num)
  intro fuel
  induction fuel with
  | zero => intro e env V hs h; simp [scaled] at h
  | succ fuel ih =>
    intro e env V hs h α _ _ T t ht ht0 htδ p
    have ht1 a ha := (htδ a ha).trans hδ1
    have unary_step (op : Unary) (a : Expr) (hsa : a.scoped env.size = true)
        (ha : (do let A ← scaled fuel c δ decay a env
                  scaleUnary c δ decay op A) = some V) :
        ∃ v : ScaleModel S T V, ∀ z ∈ S, ∀ u ∈ T, ∀ xs : List ℝ,
          p.Realizes t z u xs → v.actual t z u = ((NExpr.unary op a).real xs:ℂ) := by
      simp only [Bind.bind,Option.bind_eq_some_iff] at ha
      obtain ⟨A,hA,hU⟩ := ha
      obtain ⟨f,hf⟩ := ih a env A hsa hA ht ht0 htδ p
      obtain ⟨v,hv⟩ := f.unary hc hS hz₀ ht ht0 htδ hδ1 op hU
      exact ⟨v,fun z hz u hu xs hx => hv z hz u hu _ (hf z hz u hu xs hx)⟩
    cases e with
    | var i =>
      rw [scaled.eq_2] at h
      have hi : i < env.size := by simpa [NExpr.scoped] using hs
      have he : env[i]! = V := by
        simpa only [getElem!_pos env i hi,Array.getElem?_eq_getElem hi,Option.some.injEq] using h
      subst V
      exact ⟨p.get i hi,fun z hz a ha xs hx => hx.2 i hi⟩
    | rat q =>
      rw [scaled.eq_3] at h
      have he : scaleConst (CBox.ofReal (Ival.ofRat c.prec q)) = V := Option.some.inj h
      subst V
      let f : BoxModel S T (CBox.ofReal (Ival.ofRat c.prec q)) :=
        .constant (q:ℂ) (CBox.mem_ofReal (Ival.mem_ofRat c.prec q))
      exact ⟨f.toScale,fun _ _ _ _ _ _ => f.toScale_actual _ _ _⟩
    | pi =>
      rw [scaled.eq_4] at h
      have he : scaleConst (CBox.ofReal c.pi) = V := Option.some.inj h
      subst V
      let f : BoxModel S T (CBox.ofReal c.pi) := .constant (Real.pi:ℂ) (CBox.mem_ofReal hc.pi_mem)
      exact ⟨f.toScale,fun _ _ _ _ _ _ => f.toScale_actual _ _ _⟩
    | unary op a =>
      by_cases hvar : ∃ i, op = .log ∧ a = .var i
      · obtain ⟨i,rfl,rfl⟩ := hvar
        rw [scaled.eq_5] at h
        have hi : i < env.size := by simpa [NExpr.scoped] using hs
        cases hA : env[i]? with
        | none => simp [hA] at h
        | some A =>
          have heA : env[i]! = A := by
            simpa only [getElem!_pos env i hi,Array.getElem?_eq_getElem hi,Option.some.injEq] using hA
          let f : ScaleModel S T A := ⟨p.family i,fun z hz a ha => by
            simpa only [heA] using p.mem i hi z hz a ha⟩
          have hreal : ∀ z ∈ S, ∀ a ∈ T, ∀ xs, p.Realizes t z a xs →
              f.actual t z a = ((xs[i]?.getD 0:ℝ):ℂ) := by
            intro z hz a ha xs hx
            simpa only [f,ScaleModel.actual,heA] using hx.2 i hi
          simp only [hA,Bind.bind,Option.bind_some] at h
          split at h
          · rename_i hspecial
            obtain ⟨v,hv⟩ := ScaleModel.logEndpoint hc ht ht0 htδ hδ h
            refine ⟨v,?_⟩
            intro z hz a ha xs hx
            have he : xs[i]?.getD 0 = t a := by
              exact_mod_cast endpointVar_sound hspecial (heA ▸ p.real_mem hz ha hx i hi)
            simpa only [NExpr.real,Unary.real,he] using hv z hz a ha
          · obtain ⟨v,hv⟩ := f.unary hc hS hz₀ ht ht0 htδ hδ1 .log h
            exact ⟨v,fun z hz a ha xs hx => hv z hz a ha _ (hreal z hz a ha xs hx)⟩
      · by_cases hone : ∃ i, op = .log ∧ a = .binary .sub (.rat 1) (.var i)
        · obtain ⟨i,rfl,rfl⟩ := hone
          change (do let A ← env[i]?
                     if endpointVar A then logOneMinusEndpointScale c δ else
                       scaleUnary c δ decay .log (← scaled fuel c δ decay (.binary .sub (.rat 1) (.var i)) env)) = some V at h
          have hi : i < env.size := by simpa [NExpr.scoped] using hs
          cases hA : env[i]? with
          | none => simp [hA] at h
          | some A =>
            have heA : env[i]! = A := by
              simpa only [getElem!_pos env i hi,Array.getElem?_eq_getElem hi,Option.some.injEq] using hA
            simp only [hA,Bind.bind,Option.bind_some] at h
            split at h
            · rename_i hspecial
              obtain ⟨v,hv⟩ := ScaleModel.logOneMinus ht ht0 htδ hδ h
              refine ⟨v,?_⟩
              intro z hz a ha xs hx
              have he : xs[i]?.getD 0 = t a := by
                exact_mod_cast endpointVar_sound hspecial (heA ▸ p.real_mem hz ha hx i hi)
              simpa [NExpr.real,Unary.real,Binary.real,he] using hv z hz a ha
            · exact unary_step .log _ hs h
        · by_cases hrat : ∃ q, op = .log ∧ a = .rat q
          · obtain ⟨q,rfl,rfl⟩ := hrat
            rw [scaled.eq_7] at h
            have he : scaleConst (CBox.ofReal (unaryR c .log (Ival.ofRat c.prec q))) = V := Option.some.inj h
            subst V
            let f : BoxModel S T (CBox.ofReal (unaryR c .log (Ival.ofRat c.prec q))) :=
              .constant (Real.log (q:ℝ):ℂ) (CBox.mem_ofReal (unaryR_sound hc .log (Ival.mem_ofRat c.prec q)))
            exact ⟨f.toScale,fun _ _ _ _ _ _ => f.toScale_actual _ _ _⟩
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
      obtain ⟨f,hf⟩ := ih a env A hsc.1 hA ht ht0 htδ p
      obtain ⟨g,hg⟩ := ih b env B hsc.2 hB ht ht0 htδ p
      have fallback (op : Binary)
          (hF : (do return scaleConst (← binaryC c op (← collapse c δ A) (← collapse c δ B))) = some V) :
          ∃ v : ScaleModel S T V, ∀ z ∈ S, ∀ u ∈ T, ∀ xs,
            p.Realizes t z u xs → v.actual t z u = (op.real (a.real xs) (b.real xs):ℂ) := by
        simp only [Bind.bind,Option.bind_eq_some_iff] at hF
        obtain ⟨ZA,hZA,ZB,hZB,U,hU,hV⟩ := hF
        have he : scaleConst U = V := Option.some.inj hV
        subst V
        obtain ⟨fa,hfa⟩ := f.collapse hc ht ht0 htδ hδ1 hZA
        obtain ⟨gb,hgb⟩ := g.collapse hc ht ht0 htδ hδ1 hZB
        obtain ⟨v,hv⟩ := fa.binary hc gb op hU
        refine ⟨v.toScale,?_⟩
        intro z hz u hu xs hx
        rw [v.toScale_actual]
        exact hv z hz u hu _ _ ((hfa z hz u hu).trans (hf z hz u hu xs hx))
          ((hgb z hz u hu).trans (hg z hz u hu xs hx))
      cases op with
      | add =>
        obtain ⟨v,hv⟩ := f.add hc ht ht0 htδ hδ1 g h
        exact ⟨v,fun z hz u hu xs hx => by
          rw [hv z hz u hu,hf z hz u hu xs hx,hg z hz u hu xs hx]; simp only [NExpr.real,Binary.real,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow]⟩
      | sub =>
        obtain ⟨v,hv⟩ := f.sub hc ht ht0 htδ hδ1 g h
        exact ⟨v,fun z hz u hu xs hx => by
          rw [hv z hz u hu,hf z hz u hu xs hx,hg z hz u hu xs hx]; simp only [NExpr.real,Binary.real,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow]⟩
      | mul =>
        have he : scaleMul c A B = V := Option.some.inj h
        subst V
        obtain ⟨v,hv⟩ := f.mul (c := c) ht0 g
        exact ⟨v,fun z hz u hu xs hx => by
          rw [hv z hz u hu,hf z hz u hu xs hx,hg z hz u hu xs hx]; simp only [NExpr.real,Binary.real,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow]⟩
      | div =>
        obtain ⟨v,hv⟩ := f.div ht0 g h
        exact ⟨v,fun z hz u hu xs hx => by
          rw [hv z hz u hu,hf z hz u hu xs hx,hg z hz u hu xs hx]; simp only [NExpr.real,Binary.real,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow]⟩
      | max => exact fallback .max h
      | min => exact fallback .min h
    | pow a n =>
      rw [scaled.eq_10] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,h⟩ := h
      have he : scalePow c A n = V := Option.some.inj h
      subst V
      obtain ⟨f,hf⟩ := ih a env A hs hA ht ht0 htδ p
      obtain ⟨v,hv⟩ := f.pow (c := c) ht0 n
      exact ⟨v,fun z hz u hu xs hx => by rw [hv z hz u hu,hf z hz u hu xs hx]; simp only [NExpr.real,Binary.real,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow]⟩
    | rpow a q =>
      rw [scaled.eq_11] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,h⟩ := h
      split at h
      · simp at h
      · rename_i hl
        have hlogs : A.logs = 0 := by simpa using hl
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨U,hU,h⟩ := h
        have he : Scale.mk (A.power*q) 0 U = V := Option.some.inj h
        subst V
        obtain ⟨f,hf⟩ := ih a env A hs hA ht ht0 htδ p
        obtain ⟨v,hv⟩ := f.rpow hc ht0 ht1 hlogs hU
        exact ⟨v,fun z hz u hu xs hx => hv z hz u hu _ (hf z hz u hu xs hx)⟩
    | integral k a b f =>
      rw [scaled.eq_12] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨A,hA,B,hB,h⟩ := h
      have hsc := hs
      simp only [NExpr.scoped,Bool.and_eq_true] at hsc
      obtain ⟨⟨hsa,hsb⟩,hsf⟩ := hsc
      obtain ⟨fa,hfa⟩ := ih a env A hsa hA ht ht0 htδ p
      obtain ⟨fb,hfb⟩ := ih b env B hsb hB ht ht0 htδ p
      let tail : Option Scale := do
        if !k.finite then none else do
          let W ← scaleAdd c δ B A true
          if k != .interval && !W.coeff.re.nonneg then none else do
            let Y ← scaleAdd c δ A (scaleMul c W (scaleConst (CBox.ofReal unit)))
            let F ← scaled fuel c δ decay f (env.push Y)
            return scaleMul c W F
      have htail : ∀ J, tail = some J → ∃ v : ScaleModel S T J,
          ∀ z ∈ S, ∀ u ∈ T, ∀ xs, p.Realizes t z u xs →
            v.actual t z u = ((NExpr.integral k a b f).real xs:ℂ) := by
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
              simpa only [Bool.and_eq_true,Bool.not_eq_true,Bool.not_eq_false,
                bne_iff_ne,not_and_or,not_not,Bool.not_eq_false'] using horder
            simp only [Option.bind_eq_some_iff] at hj
            obtain ⟨Y,hY,F,hF,hj⟩ := hj
            have hJ : scaleMul c W F = J := Option.some.inj hj
            subst J
            obtain ⟨fw,hfw⟩ := fb.sub hc ht ht0 htδ hδ1 fa hW
            let U : Set (α × ℝ) := T ×ˢ Icc (0:ℝ) 1
            let ta : (α × ℝ) → ℝ := t ∘ Prod.fst
            have htU : ContinuousOn ta U := ht.comp continuous_fst.continuousOn (fun q hq => hq.1)
            have htU0 : ∀ q ∈ U, 0 < ta q := fun q hq => ht0 q.1 hq.1
            have htUδ : ∀ q ∈ U, ta q ≤ δ.toReal := fun q hq => htδ q.1 hq.1
            let fal : ScaleModel S U A := fa.reindex Prod.fst continuous_fst.continuousOn (fun q hq => hq.1)
            let fwl : ScaleModel S U W := fw.reindex Prod.fst continuous_fst.continuousOn (fun q hq => hq.1)
            obtain ⟨fu,hfu⟩ := fwl.mul (c := c) htU0 (ScaleModel.unitModel (S := S) (T := T))
            obtain ⟨fy,hfy⟩ := fal.add hc htU htU0 htUδ hδ1 fu hY
            let pp := (p.reindex Prod.fst continuous_fst.continuousOn (show MapsTo Prod.fst U T from fun q hq => hq.1)).push fy
            obtain ⟨ff,hff⟩ := ih f (env.push Y) F (by simpa using hsf) hF htU htU0 htUδ pp
            obtain ⟨v,hv⟩ := fw.mul (c := c) ht0 ff.mean
            refine ⟨v,?_⟩
            intro z hz u hu xs hx
            have hw : fw.actual t z u = ((b.real xs-a.real xs:ℝ):ℂ) := by
              rw [hfw z hz u hu,hfb z hz u hu xs hx,hfa z hz u hu xs hx,Complex.ofReal_sub]
            have hordered : k ≠ .interval → a.real xs ≤ b.real xs := by
              intro hki
              have hn := horder.resolve_left hki
              have hm := fw.asMem t hz hu
              rw [hw] at hm
              obtain ⟨y,hy,he⟩ := W.real_coeff (ht0 u hu) (ht1 u hu) hm
              have hh : 0 ≤ b.real xs-a.real xs := by
                rw [he]; exact mul_nonneg (W.weight_pos (ht0 u hu) (ht1 u hu)).le (Ival.nonneg_of hn hy.1)
              linarith
            have hbody : ∀ r ∈ Icc (0:ℝ) 1,
                ff.actual ta z (u,r) = (f.real (xs++[a.real xs+(b.real xs-a.real xs)*r]):ℂ) := by
              intro r hr
              apply hff z hz (u,r) ⟨hu,hr⟩ _
              apply ScaleInputs.push_realizes
              · exact p.reindex_realizes _ _ _ hx
              · rw [hfy z hz (u,r) ⟨hu,hr⟩,hfu z hz (u,r) ⟨hu,hr⟩,ScaleModel.unitModel_actual]
                change fa.actual t z u+fw.actual t z u*(r:ℂ) = _
                rw [hfa z hz u hu xs hx,hw]
                push_cast; rfl
            rw [hv z hz u hu,ScaleModel.mean_actual,hw]
            change _ = ((k.value (fun x => f.real (xs++[x])) (a.real xs) (b.real xs):ℝ):ℂ)
            rw [finite_value_affine hk hordered,← intervalIntegral.integral_ofReal,← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro r hr
            change ((b.real xs-a.real xs:ℝ):ℂ)*ff.actual ta z (u,r) = _
            rw [hbody r (by simpa only [uIcc_of_le (zero_le_one : (0:ℝ)≤1)] using hr)]
            push_cast; rfl
      split at h
      · rename_i hzero
        have hh : k.finite = true ∧ a = b := by simpa only [Bool.and_eq_true,beq_iff_eq] using hzero
        have he : scaleZero = V := Option.some.inj h
        subst V
        unfold scaleZero
        let v : BoxModel S T (CBox.ofReal Ival.zero) := .constant 0 (CBox.mem_ofReal Ival.mem_zero)
        refine ⟨v.toScale,?_⟩
        intro z hz u hu xs hx
        rw [v.toScale_actual]
        have hsem := finite_integral_zero_width (f := f) hh.1
          (p.real_sound hc hsa hA hz hu (ht0 u hu) (htδ u hu) (ht1 u hu) hx).1
          (p.real_sound hc hsb hB hz hu (ht0 u hu) (htδ u hu) (ht1 u hu) hx).1 (by rw [hh.2])
        simp only [hsem.2,Complex.ofReal_zero,v,BoxModel.constant,UniformFamily.const]
      · cases hform : formula env.size k a b f with
        | none => exact htail V (by simpa only [hform,tail,Bind.bind] using h)
        | some form =>
          have hscope := formula_scoped hsa hsb hsf hform
          have finish (hv : scaled fuel c δ decay form.value env = some V)
              (hg : ∀ z ∈ S, ∀ u ∈ T, ∀ xs, p.Realizes t z u xs → ∀ g ∈ form.nonnegative, 0 ≤ g.real xs) :
              ∃ v : ScaleModel S T V, ∀ z ∈ S, ∀ u ∈ T, ∀ xs, p.Realizes t z u xs →
                v.actual t z u = ((NExpr.integral k a b f).real xs:ℂ) := by
            obtain ⟨v,hv⟩ := ih form.value env V hscope.1 hv ht ht0 htδ p
            refine ⟨v,?_⟩
            intro z hz u hu xs hx
            have hsem := formula_sound (by simpa only [hx.1] using hsa) (by simpa only [hx.1] using hsb)
              (p.real_sound hc hsa hA hz hu (ht0 u hu) (htδ u hu) (ht1 u hu) hx).1
              (p.real_sound hc hsb hB hz hu (ht0 u hu) (htδ u hu) (ht1 u hu) hx).1
              (by simpa only [hx.1] using hform) (hg z hz u hu xs hx)
            rw [hsem.2]
            exact hv z hz u hu xs hx
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
                intro z hz u hu xs hx g hgm
                have he : g = guard := by simpa [hg] using hgm.symm
                subst g
                have hgs := hscope.2 guard (by simp [hg])
                have hm := (p.real_sound hc hgs hG hz hu (ht0 u hu) (htδ u hu) (ht1 u hu) hx).2
                obtain ⟨y,hy,he⟩ := U.real_coeff (ht0 u hu) (ht1 u hu) hm
                rw [he]
                exact mul_nonneg (U.weight_pos (ht0 u hu) (ht1 u hu)).le
                  (Ival.nonneg_of (show U.coeff.re.nonneg = true from hnon) hy.1)
              · exact htail V (by simpa [hg,hG,hnon,tail] using h)

end Lynth.Interval.Integral.Nested.AnalyticWork

namespace Lynth.Interval.Integral.Nested.AnalyticWork
open Intgrl Fns MeasureTheory Set Metric
open scoped Topology

set_option maxHeartbeats 1600000 in
lemma endpoint_analytic_model {c : Ctx} (hc : c.Valid) {S : Set ℂ} (hS : Convex ℝ S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ interior S) {e : Expr} {env : Array CBox}
    (hs : e.scoped (env.size+1) = true) {δ : Dy} {right : Bool} {decay : Nat} {R : Dy}
    (h : endpointBound c e env δ right decay = some R)
    {α : Type} [TopologicalSpace α] [FirstCountableTopology α] {T : Set α}
    (p : BoxInputs S T env) :
    0 < δ.toReal ∧ δ.toReal ≤ 1/2 ∧ ∃ v : UniformFamily S T,
      (∀ z ∈ S, ∀ a ∈ T, ‖v.val z a‖ ≤ R.toReal) ∧
      (∀ z ∈ S, ∀ a ∈ T, ∀ xs, p.Realizes z a xs →
        v.val z a = ((∫ u in (0:ℝ)..δ.toReal, e.real (xs++[if right then 1-u else u]):ℝ):ℂ)) := by
  classical
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
    cases hquery : scaled (E.size+32) c δ decay E senv with
    | none => simp [E,senv,hquery] at h
    | some A =>
      have hA : endpointErrorBound c δ A = some R := by
        simpa only [show endpointExpr env.size right e = E from rfl,
          show (env.map scaleConst).push (Scale.mk 1 0 (CBox.ofReal Ival.one)) = senv from rfl,
          hquery,Bind.bind,Option.bind_some] using h
      let J : Set ℝ := Ioc 0 δ.toReal
      let U : Set (α × ℝ) := T ×ˢ J
      let pl : BoxInputs S U env := p.reindex Prod.fst continuous_fst.continuousOn (fun q hq => hq.1)
      let var : ScaleModel S U (Scale.mk 1 0 (CBox.ofReal Ival.one)) :=
        ⟨UniformFamily.const (fun _ => (1:ℂ)) continuousOn_const 1 zero_le_one (by simp),
          fun _ _ _ _ => CBox.mem_ofReal Ival.mem_one⟩
      have hvar (z : ℂ) (q : α × ℝ) : var.actual Prod.snd z q = (q.2:ℂ) := by
        simp only [var,ScaleModel.actual,weight,UniformFamily.const,Rat.cast_one,Real.rpow_one,
          pow_zero,mul_one]
      let pp : ScaleInputs S U senv := pl.toScale.push var
      have hsc : E.scoped senv.size = true := by
        simpa only [senv,Array.size_push,Array.size_map] using endpointExpr_scoped (right := right) hs
      obtain ⟨f,hf⟩ := scaled_analytic_model hc hS hz₀ hd1 (E.size+32) E senv A hsc hquery
        continuous_snd.continuousOn (fun q hq => hq.2.1) (fun q hq => hq.2.2) pp
      obtain ⟨hp,r,hr,_⟩ := endpointErrorBound_value hc hA
      have hp' : (-1:ℝ) < (A.power:ℝ) := by exact_mod_cast hp
      have hw : IntegrableOn (fun u => weight A u) J := by
        rw [integrableOn_Ioc_iff_integrableOn_Ioo]
        apply (integrableOn_rpow_mul_one_sub_log_pow hp' A.logs).mono_set
        exact Ioo_subset_Ioo le_rfl (hd1.trans (by norm_num))
      have hwC : IntegrableOn (fun u => (weight A u:ℂ)) J := hw.ofReal
      let v := f.family.integralSet measurableSet_Ioc (fun u => (weight A u:ℂ)) hwC
      have hv (z : ℂ) (a : α) : v.val z a = ∫ u in J, f.actual Prod.snd z (a,u) := rfl
      refine ⟨hd,hd1,v,?_,?_⟩
      · intro z hz a ha
        have hfc : ContinuousOn (fun u => f.actual Prod.snd z (a,u)) J := by
          have hc := f.family.continuous.comp
            (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn
            (fun u hu => ⟨self_subset_thickening f.family.radius_pos S hz,ha,hu⟩)
          exact (Complex.continuous_ofReal.comp_continuousOn
            (weight_continuous A continuousOn_id (fun u hu => hu.1))).mul hc
        let F : ℝ → ℂ := J.piecewise (fun u => f.actual Prod.snd z (a,u)) (fun _ => 0)
        have hFm : Measurable F := hfc.measurable_piecewise continuousOn_const measurableSet_Ioc
        have hpoint : ∀ u ∈ Ioo (0:ℝ) δ.toReal, A.Mem u (F u) := by
          intro u hu
          rw [show F u = f.actual Prod.snd z (a,u) from piecewise_eq_of_mem J _ _ ⟨hu.1,hu.2.le⟩]
          exact f.asMem Prod.snd hz ⟨ha,hu.1,hu.2.le⟩
        have hbound := (endpointErrorBound_sound hc hA hd (hd1.trans (by norm_num)) hFm hpoint).2
        rw [intervalIntegral.integral_of_le hd.le] at hbound
        rw [hv]
        convert hbound using 2
        apply setIntegral_congr_fun measurableSet_Ioc
        intro u hu
        exact (piecewise_eq_of_mem J (fun u => f.actual Prod.snd z (a,u)) (fun _ => 0) hu).symm
      · intro z hz a ha xs hx
        rw [hv,intervalIntegral.integral_of_le hd.le,← integral_complex_ofReal]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro u hu
        have hpp : pp.Realizes Prod.snd z (a,u) (xs++[u]) := by
          apply ScaleInputs.push_realizes
          · exact pl.toScale_realizes Prod.snd (p.reindex_realizes _ _ _ hx)
          · exact hvar z (a,u)
        have he := hf z hz (a,u) ⟨ha,hu⟩ (xs++[u]) hpp
        have hsem := (endpointExpr_semantics e xs right u).1
        have hsem' : E.real (xs++[u]) = e.real (xs++[if right then 1-u else u]) := by
          simpa only [hx.1,E] using hsem
        exact he.trans (congrArg (fun x : ℝ => (x:ℂ)) hsem')

end Lynth.Interval.Integral.Nested.AnalyticWork

namespace Lynth.Interval.Integral.Nested.AnalyticWork
open Intgrl Fns MeasureTheory Set Metric
open scoped Topology

namespace BoxModel
variable {S : Set ℂ} {α : Type} [TopologicalSpace α] {T : Set α}

noncomputable def unitModel : BoxModel S (T ×ˢ Icc (0:ℝ) 1) (CBox.ofReal unit) :=
  ⟨ScaleModel.unitModel.family,ScaleModel.unitModel.mem⟩

lemma integral_affine (g : ℝ → ℂ) (a b : ℝ) :
    (∫ u in a..b, g u) = ((b-a:ℝ):ℂ)*(∫ u in (0:ℝ)..1, g (a+(b-a)*u)) := by
  have hh := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1) g (b-a) a
  simpa only [mul_zero,add_zero,mul_one,add_sub_cancel,Complex.real_smul] using hh.symm

noncomputable def integrate [FirstCountableTopology α] {a b : ℝ} (hab : a ≤ b)
    {Z : CBox} {prec : Nat} (f : BoxModel S (T ×ˢ Icc a b) Z) {D : Ival} (hD : b-a ∈ D) :
    BoxModel S T (CBox.mul prec (CBox.ofReal D) Z) := by
  let g : BoxModel S (T ×ˢ Icc (0:ℝ) 1) Z := f.reindex
    (fun q : α × ℝ => (q.1,a+(b-a)*q.2))
    (continuous_fst.prodMk (continuous_const.add (continuous_const.mul continuous_snd))).continuousOn
    (by intro q hq; exact ⟨hq.1,by nlinarith [hq.2.1,hq.2.2],by nlinarith [hq.2.1,hq.2.2]⟩)
  exact (constant ((b-a:ℝ):ℂ) (CBox.mem_ofReal hD)).mul g.mean

lemma integrate_val [FirstCountableTopology α] {a b : ℝ} (hab : a ≤ b)
    {Z : CBox} {prec : Nat} (f : BoxModel S (T ×ˢ Icc a b) Z) {D : Ival} (hD : b-a ∈ D) (z : ℂ) (u : α) :
    (f.integrate (prec := prec) hab hD).family.val z u = ∫ x in a..b, f.family.val z (u,x) := by
  change _ * (BoxModel.mean _).family.val z u = _
  rw [BoxModel.mean_val]
  exact (integral_affine (fun x => f.family.val z (u,x)) a b).symm

end BoxModel

lemma complex_add_widen {c : Ctx} {V : CBox} {L R : Dy} {l m r : ℂ}
    (hl : ‖l‖ ≤ L.toReal) (hm : m ∈ V) (hr : ‖r‖ ≤ R.toReal) :
    l+m+r ∈ (⟨Ival.widen c.prec V.re (Dy.addU c.prec L R),
      Ival.widen c.prec V.im (Dy.addU c.prec L R)⟩ : CBox) := by
  have hnorm : ‖l+r‖ ≤ (Dy.addU c.prec L R).toReal := by
    apply ((norm_add_le _ _).trans (add_le_add hl hr)).trans
    simpa only [Dy.toReal_def,Rat.cast_add] using (Rat.cast_mono (K := ℝ) (Dy.le_addU c.prec L R))
  constructor
  · apply Ival.mem_widen hm.1
    have he : (l+m+r).re-m.re = (l+r).re := by simp only [Complex.add_re]; ring
    rw [he]
    exact (Complex.abs_re_le_norm _).trans hnorm
  · apply Ival.mem_widen hm.2
    have he : (l+m+r).im-m.im = (l+r).im := by simp only [Complex.add_im]; ring
    rw [he]
    exact (Complex.abs_im_le_norm _).trans hnorm

lemma endpoint_real_data {c : Ctx} (hc : c.Valid) {e : Expr} {env : Array CBox}
    (hs : e.scoped (env.size+1) = true) {δ : Dy} {right : Bool} {decay : Nat} {R : Dy}
    (h : endpointBound c e env δ right decay = some R) {xs : List ℝ}
    (hl : xs.length = env.size) (hm : ∀ i < env.size, ((xs[i]?.getD 0:ℝ):ℂ) ∈ env[i]!) :
    IntervalIntegrable (fun u => e.real (xs++[if right then 1-u else u])) volume 0 δ.toReal ∧
      ∀ u ∈ Ioc (0:ℝ) δ.toReal, e.Converges (xs++[if right then 1-u else u]) := by
  let p : ParameterPath Unit univ env.size := ⟨fun _ => xs,fun _ _ => hl,fun _ _ => continuousOn_const⟩
  have hgood := (endpointBound_real_sound hc hs h p (fun _ _ => hm)).2.2.2 () (mem_univ ())
  exact ⟨hgood.1,hgood.2.2⟩

end Lynth.Interval.Integral.Nested.AnalyticWork
