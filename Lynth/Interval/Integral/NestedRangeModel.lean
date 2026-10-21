import Lynth.Interval.Integral.NestedLogEndpointProof
import Lynth.Interval.Integral.NestedRealBoundsProof
import Lynth.Interval.Integral.Math.NestedChange

/-! Parameter paths and integral averaging lemmas for recursive range evaluation. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl Fns MeasureTheory Set Filter
open scoped Topology
open private unit from Lynth.Interval.Integral.NestedBounds

lemma intervalIntegral_mem_unit {f : ℝ → ℝ} {V : Ival}
    (hi : IntervalIntegrable f volume 0 1)
    (hv : ∀ t ∈ Ioo (0:ℝ) 1, f t ∈ V) : (∫ t in (0:ℝ)..1, f t) ∈ V := by
  constructor
  · intro l hl
    have h := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ) ≤ 1)
      intervalIntegrable_const hi (fun t ht => (hv t ht).1 l hl)
    simpa using h
  · intro u hu
    have h := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ) ≤ 1)
      hi intervalIntegrable_const (fun t ht => (hv t ht).2 u hu)
    simpa using h

lemma cbox_intervalIntegral_mem_unit {f : ℝ → ℂ} {V : CBox}
    (hi : IntervalIntegrable f volume 0 1)
    (hv : ∀ t ∈ Ioo (0:ℝ) 1, f t ∈ V) : (∫ t in (0:ℝ)..1, f t) ∈ V := by
  constructor
  · change Complex.reCLM (∫ t in (0:ℝ)..1, f t) ∈ V.re
    rw [← Complex.reCLM.intervalIntegral_comp_comm hi]
    exact intervalIntegral_mem_unit ⟨hi.1.re, hi.2.re⟩ (fun t ht => (hv t ht).1)
  · change Complex.imCLM (∫ t in (0:ℝ)..1, f t) ∈ V.im
    rw [← Complex.imCLM.intervalIntegral_comp_comm hi]
    exact intervalIntegral_mem_unit ⟨hi.1.im, hi.2.im⟩ (fun t ht => (hv t ht).2)

lemma scale_intervalIntegral_mem_unit {f : ℝ → ℂ} {V : Scale} {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hi : IntervalIntegrable f volume 0 1)
    (hv : ∀ s ∈ Ioo (0:ℝ) 1, V.Mem t (f s)) :
    V.Mem t (∫ s in (0:ℝ)..1, f s) := by
  let w : ℂ := ((t ^ (V.power:ℝ) * (1-Real.log t)^V.logs : ℝ) : ℂ)
  have hw : w ≠ 0 := by
    dsimp [w]
    exact_mod_cast (V.weight_pos ht ht1).ne'
  have hint := hi.div_const w
  have hb : ∀ s ∈ Ioo (0:ℝ) 1, f s / w ∈ V.coeff := by
    intro s hs
    obtain ⟨v, hv, he⟩ := hv s hs
    have he' : f s = w*v := he
    simpa only [he', mul_div_cancel_left₀ _ hw] using hv
  refine ⟨_, cbox_intervalIntegral_mem_unit hint hb, ?_⟩
  change (∫ s in (0:ℝ)..1, f s) = w * ∫ s in (0:ℝ)..1, f s / w
  rw [intervalIntegral.integral_div]
  field_simp

lemma continuousOn_intervalIntegral {X E : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set X} {F : X × ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (s ×ˢ Icc a b)) :
    ContinuousOn (fun x => ∫ t in a..b, F (x,t)) s := by
  intro x hx
  have hFx : ContinuousOn (fun t => F (x,t)) (Icc a b) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hx,ht⟩)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hFx
  obtain ⟨v,hv,hclose⟩ := isCompact_Icc.mem_uniformity_of_prod (f := fun x t => F (x,t)) hF hx
    (Metric.dist_mem_uniformity zero_lt_one)
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := fun _ => C+1)
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hc : ContinuousOn (fun t => F (y,t)) (Icc a b) :=
      hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hy,ht⟩)
    exact (hc.mono (by simpa only [uIoc_of_le hab] using (Ioc_subset_Icc_self : Ioc a b ⊆ Icc a b))).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [hv] with y hy
    exact Eventually.of_forall fun t ht => by
      have ht' : t ∈ Icc a b := by exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using ht)
      have hc : dist (F (y,t)) (F (x,t)) < 1 := hclose y hy t ht'
      calc ‖F (y,t)‖ = ‖F (y,t)-F (x,t)+F (x,t)‖ := by rw [sub_add_cancel]
        _ ≤ ‖F (y,t)-F (x,t)‖+‖F (x,t)‖ := norm_add_le _ _
        _ ≤ C+1 := by
          rw [← dist_eq_norm]
          linarith [hC t ht']
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t ht => by
      have ht' : t ∈ Icc a b := by exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using ht)
      exact hF.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun y hy => ⟨hy,ht'⟩) x hx



lemma continuousOn_unitIntegral {X E : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set X} {F : X × ℝ → E}
    (hF : ContinuousOn F (s ×ˢ Icc (0:ℝ) 1)) :
    ContinuousOn (fun x => ∫ t in (0:ℝ)..1, F (x,t)) s :=
  continuousOn_intervalIntegral zero_le_one hF

structure ParameterPath (X : Type*) [TopologicalSpace X] (s : Set X) (n : Nat) where
  val : X → List ℝ
  length : ∀ x ∈ s, (val x).length = n
  continuous : ∀ i < n, ContinuousOn (fun x => (val x)[i]?.getD 0) s

namespace ParameterPath
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {s : Set X} {r : Set Y} {n : Nat}

def resize (p : ParameterPath X s n) {m : Nat} (h : m = n) : ParameterPath X s m where
  val := p.val
  length x hx := (p.length x hx).trans h.symm
  continuous i hi := p.continuous i (h ▸ hi)

def comp (p : ParameterPath X s n) (g : Y → X)
    (hg : ContinuousOn g r) (hgs : MapsTo g r s) : ParameterPath Y r n where
  val x := p.val (g x)
  length x hx := p.length (g x) (hgs hx)
  continuous i hi := (p.continuous i hi).comp hg hgs

def push (p : ParameterPath X s n) (f : X → ℝ) (hf : ContinuousOn f s) :
    ParameterPath X s (n+1) where
  val x := p.val x ++ [f x]
  length x hx := by simp [p.length x hx]
  continuous i hi := by
    by_cases hin : i < n
    · apply (p.continuous i hin).congr
      intro x hx
      simp [List.getElem?_append, p.length x hx, hin]
    · have he : i = n := by omega
      subst i
      apply hf.congr
      intro x hx
      simp [List.getElem?_append, p.length x hx]

lemma mem_push {R : Nat → ℝ → Prop} (p : ParameterPath X s n)
    {f : X → ℝ} {hf : ContinuousOn f s} (hp : ∀ x ∈ s, ∀ i < n,
      R i ((p.val x)[i]?.getD 0)) (hfmem : ∀ x ∈ s, R n (f x)) :
    ∀ x ∈ s, ∀ i < n+1, R i (((p.push f hf).val x)[i]?.getD 0) := by
  intro x hx i hi
  by_cases hin : i < n
  · simpa [push,List.getElem?_append,p.length x hx,hin] using hp x hx i hin
  · have he : i = n := by omega
    subst i
    simpa [push,p.length x hx] using hfmem x hx

end ParameterPath

open private unaryCRaw unaryC_raw_result from Lynth.Interval.Integral.NestedPrimitiveProof

lemma unaryC_continuousOn {X : Type*} [TopologicalSpace X] {s : Set X}
    {c : Ctx} (hc : c.Valid) {op : Unary} {Z V : CBox} {f : X → ℝ}
    (hf : ContinuousOn f s) (hz : ∀ x ∈ s, (f x : ℂ) ∈ Z)
    (h : unaryC c op Z = some V) : ContinuousOn (fun x => op.real (f x)) s := by
  have hr := unaryC_raw_result h
  cases op <;> simp only [Unary.real]
  · exact hf.neg
  · have hn : (CBox.normSq c.prec Z).pos = true := by
      by_contra hn
      simp [unaryCRaw,hn] at hr
    exact hf.inv₀ (fun x hx => by
      have hh := Ival.pos_of hn (CBox.mem_normSq (p := c.prec) (hz x hx))
      intro he
      simp [he] at hh)
  · exact Real.continuous_exp.comp_continuousOn hf
  · exact Real.continuous_sin.comp_continuousOn hf
  · exact Real.continuous_cos.comp_continuousOn hf
  · exact Real.continuous_sinh.comp_continuousOn hf
  · exact Real.continuous_cosh.comp_continuousOn hf
  · have hn : Z.re.negv = true ∨ Z.re.pos = true := by
      by_contra hn
      push Not at hn
      simp [unaryCRaw,hn.1,hn.2] at hr
    intro x hx
    apply (Real.continuousAt_log ?_).comp_continuousWithinAt (hf x hx)
    rcases hn with hn | hp
    · exact (Ival.neg_of hn (hz x hx).1).ne
    · exact (Ival.pos_of hp (hz x hx).1).ne'
  · exact Real.continuous_sqrt.comp_continuousOn hf
  · exact continuous_abs.comp_continuousOn hf
  · cases hlo : (intFloorIval Z.re).lo with
    | none => simp [unaryCRaw,hlo] at hr
    | some a =>
      cases hhi : (intFloorIval Z.re).hi with
      | none => simp [unaryCRaw,hlo,hhi] at hr
      | some b =>
        have he : V = CBox.ofReal (Ival.pt a) := by
          simp only [unaryCRaw,hlo,hhi] at hr
          split at hr
          · exact (Option.some.inj hr).symm
          · simp at hr
        apply continuousOn_const.congr
        intro x hx
        have hv := unaryC_real_sound hc .floor (hz x hx) h
        rw [he] at hv
        exact le_antisymm (hv.1.2 a rfl) (hv.1.1 a rfl)
  · exact Real.continuous_arctan.comp_continuousOn hf
  · exact Real.continuous_erf.comp_continuousOn hf
  · exact Real.continuous_Si.comp_continuousOn hf
  · have he : (fun x : ℝ => (Complex.dirichletEta (x:ℂ)).re) = Real.dirichletEta := by
      funext x
      rw [(SpecialFunctions.entire_agrees.2 x).2.2.1]
      rfl
    rw [← he]
    have ha := SpecialFunctions.entire_agrees.1 Complex.dirichletEta (by simp)
    exact (Complex.continuous_re.comp (continuousOn_univ.mp ha.continuousOn
      |>.comp Complex.continuous_ofReal)).comp_continuousOn hf
  · exact Real.continuous_airyAi.comp_continuousOn hf



lemma cbox_real_ne_zero {c : Ctx} {Z : CBox} {x : ℝ}
    (hz : (x:ℂ) ∈ Z) (hp : (CBox.normSq c.prec Z).pos = true) : x ≠ 0 := by
  have h := Ival.pos_of hp (CBox.mem_normSq (p := c.prec) hz)
  intro he
  simp [he] at h

lemma scale_real_ne_zero {c : Ctx} {A : Scale} {t x : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hA : A.Mem t (x:ℂ))
    (hp : (CBox.normSq c.prec A.coeff).pos = true) : x ≠ 0 := by
  obtain ⟨y,hy,he⟩ := A.real_coeff ht ht1 hA
  rw [he]
  exact mul_ne_zero (A.weight_pos ht ht1).ne' (cbox_real_ne_zero hy hp)

lemma binaryC_continuousOn {X : Type*} [TopologicalSpace X] {s : Set X}
    {c : Ctx} {op : Binary} {A B V : CBox} {f g : X → ℝ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hb : ∀ x ∈ s, (g x : ℂ) ∈ B) (h : binaryC c op A B = some V) :
    ContinuousOn (fun x => op.real (f x) (g x)) s := by
  cases op <;> simp only [Binary.real]
  · exact hf.add hg
  · exact hf.sub hg
  · exact hf.mul hg
  · have hp : (CBox.normSq c.prec B).pos = true := by
      by_contra hn
      simp [binaryC,hn] at h
    exact hf.div hg (fun x hx => cbox_real_ne_zero (hb x hx) hp)
  · exact (continuous_fst.max continuous_snd).comp_continuousOn (hf.prodMk hg)
  · exact (continuous_fst.min continuous_snd).comp_continuousOn (hf.prodMk hg)

lemma unary_real_continuousOn {X : Type*} [TopologicalSpace X] {s : Set X}
    {op : Unary} {f : X → ℝ} (hf : ContinuousOn f s)
    (hfloor : op ≠ .floor)
    (hzero : op = .inv ∨ op = .log → ∀ x ∈ s, f x ≠ 0) :
    ContinuousOn (fun x => op.real (f x)) s := by
  cases op <;> simp only [Unary.real]
  · exact hf.neg
  · exact hf.inv₀ (hzero (Or.inl rfl))
  · exact Real.continuous_exp.comp_continuousOn hf
  · exact Real.continuous_sin.comp_continuousOn hf
  · exact Real.continuous_cos.comp_continuousOn hf
  · exact Real.continuous_sinh.comp_continuousOn hf
  · exact Real.continuous_cosh.comp_continuousOn hf
  · exact fun x hx => (Real.continuousAt_log (hzero (Or.inr rfl) x hx)).comp_continuousWithinAt (hf x hx)
  · exact Real.continuous_sqrt.comp_continuousOn hf
  · exact continuous_abs.comp_continuousOn hf
  · exact (hfloor rfl).elim
  · exact Real.continuous_arctan.comp_continuousOn hf
  · exact Real.continuous_erf.comp_continuousOn hf
  · exact Real.continuous_Si.comp_continuousOn hf
  · have he : (fun x : ℝ => (Complex.dirichletEta (x:ℂ)).re) = Real.dirichletEta := by
      funext x
      rw [(SpecialFunctions.entire_agrees.2 x).2.2.1]
      rfl
    rw [← he]
    have ha := SpecialFunctions.entire_agrees.1 Complex.dirichletEta (by simp)
    exact (Complex.continuous_re.comp (continuousOn_univ.mp ha.continuousOn
      |>.comp Complex.continuous_ofReal)).comp_continuousOn hf
  · exact Real.continuous_airyAi.comp_continuousOn hf

lemma scaleUnary_continuousOn {X : Type*} [TopologicalSpace X] {s : Set X}
    {c : Ctx} (hc : c.Valid) {δ : Dy} {decay : Nat} {op : Unary}
    {A V : Scale} {t : ℝ} (ht : 0 < t) (htδ : t ≤ δ.toReal) (ht1 : t ≤ 1)
    {f : X → ℝ} (hf : ContinuousOn f s) (hA : ∀ x ∈ s, A.Mem t (f x : ℂ))
    (h : scaleUnary c δ decay op A = some V) : ContinuousOn (fun x => op.real (f x)) s := by
  by_cases hop : op = .floor
  · subst op
    simp only [scaleUnary, Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨Z,hZ,U,hU,_⟩ := h
    exact unaryC_continuousOn hc hf (fun x hx => collapse_sound hc ht htδ ht1 (hA x hx) hZ) hU
  · apply unary_real_continuousOn hf hop
    intro hzero x hx
    rcases hzero with rfl | rfl
    · have hp : (CBox.normSq c.prec A.coeff).pos = true := by
        by_contra hn
        simp [scaleUnary,scaleDiv,hn] at h
      exact scale_real_ne_zero ht ht1 (hA x hx) hp
    · simp only [scaleUnary,Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨Z,hZ,_⟩ := h
      have hh := unaryC_raw_result hZ
      have hp : A.coeff.re.negv = true ∨ A.coeff.re.pos = true := by
        by_contra hn
        push Not at hn
        simp [unaryCRaw,hn.1,hn.2] at hh
      obtain ⟨y,hy,he⟩ := A.real_coeff ht ht1 (hA x hx)
      rw [he]
      apply mul_ne_zero (A.weight_pos ht ht1).ne'
      rcases hp with hn | hp
      · exact (Ival.neg_of hn hy.1).ne
      · exact (Ival.pos_of hp hy.1).ne'



lemma finite_integral_of_affine {k : NDomain} (hk : k.finite = true)
    {a b f : Expr} {xs : List ℝ} (ha : a.Converges xs) (hb : b.Converges xs)
    (horder : k ≠ .interval → a.real xs ≤ b.real xs)
    (hi : IntervalIntegrable (fun u => (b.real xs-a.real xs) *
      f.real (xs++[a.real xs+(b.real xs-a.real xs)*u])) volume 0 1)
    (hf : ∀ u ∈ Ioo (0:ℝ) 1,
      f.Converges (xs++[a.real xs+(b.real xs-a.real xs)*u])) :
    (NExpr.integral k a b f).Converges xs ∧
      (NExpr.integral k a b f).real xs = ∫ u in (0:ℝ)..1,
        (b.real xs-a.real xs)*f.real (xs++[a.real xs+(b.real xs-a.real xs)*u]) := by
  have hint := (finite_affine_integrable (f.measurable_body xs)).mpr hi
  have hval := finite_affine_value hint
  have hconv : ∀ x ∈ uIoo (a.real xs) (b.real xs), f.Converges (xs++[x]) := by
    intro x hx
    obtain ⟨u,hu,rfl⟩ := affine_surj hx
    exact hf u hu
  by_cases hki : k = .interval
  · subst k
    exact ⟨⟨ha,hb,hint,hconv⟩,hval⟩
  · have hab := horder hki
    have hd := finite_domain_of_interval hk hab hint
    refine ⟨⟨ha,hb,hd.1,?_⟩,hd.2.trans hval⟩
    cases k <;> simp only [NDomain.finite,Bool.false_eq_true] at hk
    all_goals simpa only [uIoo_of_le hab] using hconv

lemma cbox_real_integral_mean {a b : ℝ} {f : ℝ → ℝ} {V : CBox}
    (hab : a ≤ b) (hi : IntervalIntegrable f volume a b)
    (hv : ∀ x ∈ Icc a b, (f x:ℂ) ∈ V) :
    ∃ z ∈ V, ((∫ x in a..b, f x:ℝ):ℂ) = ((b-a:ℝ):ℂ)*z := by
  rcases hab.eq_or_lt with he | hlt
  · subst b
    exact ⟨(f a:ℂ),hv a ⟨le_rfl,le_rfl⟩,by simp⟩
  · have hw : 0 < b-a := sub_pos.mpr hlt
    let v := (∫ x in a..b, f x)/(b-a)
    have hm : (v:ℂ) ∈ V := by
      constructor
      · constructor
        · intro l hl
          have hlo := intervalIntegral.integral_mono_on_of_le_Ioo hab
            intervalIntegrable_const hi (fun x hx => (hv x ⟨hx.1.le,hx.2.le⟩).1.1 l hl)
          apply (le_div_iff₀ hw).mpr
          simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hlo
        · intro u hu
          have hhi := intervalIntegral.integral_mono_on_of_le_Ioo hab
            hi intervalIntegrable_const (fun x hx => (hv x ⟨hx.1.le,hx.2.le⟩).1.2 u hu)
          apply (div_le_iff₀ hw).mpr
          simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hhi
      · exact (hv a ⟨le_rfl,hab⟩).2
    refine ⟨(v:ℂ),hm,?_⟩
    rw [← Complex.ofReal_mul]
    congr 1
    dsimp [v]
    field_simp

lemma nondegenerate_predicate_trans {P : ℝ → Prop} {a b c : ℝ}
    (hab : a ≠ b → ∀ x ∈ uIcc a b, P x)
    (hbc : b ≠ c → ∀ x ∈ uIcc b c, P x) :
    a ≠ c → ∀ x ∈ uIcc a c, P x := by
  by_cases he : a = b
  · subst b
    exact hbc
  by_cases he' : b = c
  · subst c
    exact hab
  intro _ x hx
  rcases uIcc_subset_uIcc_union_uIcc (a := a) (b := b) (c := c) hx with hx | hx
  · exact hab he x hx
  · exact hbc he' x hx

lemma piece_chain_predicate {P : ℝ → Prop} (p : Piece) (ps : List Piece)
    (hchain : ((p::ps).zip (p::ps).tail).all (fun pq => dyEq pq.1.b pq.2.a) = true)
    (horder : ∀ q ∈ p::ps, q.a.toReal ≤ q.b.toReal)
    (hP : ∀ q ∈ p::ps, q.a.toReal < q.b.toReal →
      ∀ x ∈ Icc q.a.toReal q.b.toReal, P x) :
    p.a.toReal ≤ (ps.getLastD p).b.toReal ∧
      (p.a.toReal < (ps.getLastD p).b.toReal →
        ∀ x ∈ Icc p.a.toReal (ps.getLastD p).b.toReal, P x) := by
  induction ps generalizing p with
  | nil => exact ⟨horder p (by simp),hP p (by simp)⟩
  | cons q qs ih =>
    have hh : dyEq p.b q.a = true ∧
        ((q::qs).zip (q::qs).tail).all (fun pq => dyEq pq.1.b pq.2.a) = true := by
      simpa only [List.tail_cons,List.zip_cons_cons,List.all_cons,Bool.and_eq_true] using hchain
    have hpq : p.b.toReal = q.a.toReal := by
      have he : p.b.toRat = q.a.toRat := by simpa only [dyEq,beq_iff_eq] using hh.1
      exact congrArg (fun r : ℚ => (r:ℝ)) he
    have hrec := ih q hh.2 (fun r hr => horder r (by simp only [List.mem_cons] at hr ⊢; tauto))
      (fun r hr => hP r (by simp only [List.mem_cons] at hr ⊢; tauto))
    have hpl := horder p (by simp)
    have hle : p.a.toReal ≤ (qs.getLastD q).b.toReal := hpl.trans (hpq.trans_le hrec.1)
    refine ⟨by simpa only [List.getLastD_cons] using hle,?_⟩
    simp only [List.getLastD_cons]
    intro hw x hx
    by_cases hxp : x ≤ p.b.toReal
    · by_cases hp : p.a.toReal < p.b.toReal
      · exact hP p (by simp) hp x ⟨hx.1,hxp⟩
      · have he : p.a.toReal = p.b.toReal := le_antisymm hpl (le_of_not_gt hp)
        have hxq : x = q.a.toReal := le_antisymm (hxp.trans hpq.le) (hpq.symm.le.trans (he.symm.le.trans hx.1))
        apply hrec.2 (by simpa only [← hpq,← he] using hw) x
        exact ⟨hxq.symm.le,hx.2⟩
    · exact hrec.2 (lt_of_lt_of_le (by simpa only [hpq] using lt_of_not_ge hxp) hx.2)
        x ⟨by simpa only [← hpq] using (lt_of_not_ge hxp).le,hx.2⟩

lemma partition_predicate {P : ℝ → Prop} {cert : Certificate}
    (hp : partitionCheck cert = true)
    (hP : ∀ q ∈ cert.pieces, q.a.toReal < q.b.toReal →
      ∀ x ∈ Icc q.a.toReal q.b.toReal, P x) :
    cert.a.toReal ≤ cert.b.toReal ∧
      (cert.a.toReal < cert.b.toReal → ∀ x ∈ Icc cert.a.toReal cert.b.toReal, P x) := by
  cases hs : cert.pieces with
  | nil => simp [partitionCheck,hs] at hp
  | cons p ps =>
    simp only [partitionCheck,hs,Bool.and_eq_true] at hp
    have ha : p.a.toReal = cert.a.toReal := by
      have he : p.a.toRat = cert.a.toRat := by simpa [dyEq] using hp.1.1.1
      exact congrArg (fun q : ℚ => (q:ℝ)) he
    have hb : (ps.getLastD p).b.toReal = cert.b.toReal := by
      have he : (ps.getLastD p).b.toRat = cert.b.toRat := by simpa [dyEq] using hp.1.1.2
      exact congrArg (fun q : ℚ => (q:ℝ)) he
    have horder : ∀ q ∈ p::ps, q.a.toReal ≤ q.b.toReal := fun q hq =>
      Dy.toReal_le_of_leB (List.all_eq_true.mp hp.1.2 q hq)
    have hh := piece_chain_predicate p ps hp.2 horder (by simpa only [hs] using hP)
    simpa only [ha,hb] using hh

end Lynth.Interval.Integral.Nested
