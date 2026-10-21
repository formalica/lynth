import Lynth.Interval.Integral.NestedAnalyticFamily

/-! Analytic models for normalized endpoint coefficients and their arithmetic. -/

namespace Lynth.Interval.Integral.Nested.AnalyticWork
open Intgrl Fns MeasureTheory Set Metric
open scoped Topology
open private unit from Lynth.Interval.Integral.NestedBounds

noncomputable abbrev weight (A : Scale) (t : ℝ) : ℝ :=
  t^(A.power:ℝ)*(1-Real.log t)^A.logs

lemma ival_set_isClosed (A : Ival) : IsClosed {x : ℝ | x ∈ A} := by
  rcases A with ⟨lo,hi⟩
  cases lo <;> cases hi <;>
    simp only [Ival.mem_mk,Ival.loLe_none,Ival.leHi_none,Ival.loLe_some,Ival.leHi_some,
      true_and,and_true,Set.setOf_true]
  · exact isClosed_univ
  · exact isClosed_Iic
  · exact isClosed_Ici
  · exact isClosed_Icc

lemma cbox_set_isClosed (Z : CBox) : IsClosed {z : ℂ | z ∈ Z} :=
  ((ival_set_isClosed Z.re).preimage Complex.continuous_re).inter
    ((ival_set_isClosed Z.im).preimage Complex.continuous_im)

lemma weight_continuous {α : Type} [TopologicalSpace α] {T : Set α}
    (A : Scale) {t : α → ℝ} (ht : ContinuousOn t T) (hpos : ∀ a ∈ T, 0 < t a) :
    ContinuousOn (fun a => weight A (t a)) T := by
  have hl : ContinuousOn (fun a => Real.log (t a)) T := fun a ha =>
    (Real.continuousAt_log (hpos a ha).ne').comp_continuousWithinAt (ht a ha)
  exact (ht.rpow_const (fun a ha => Or.inl (hpos a ha).ne')).mul
    ((continuousOn_const.sub hl).pow A.logs)

lemma weight_ratio_le_one (A V : Scale) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hp : V.power ≤ A.power) (hl : A.logs ≤ V.logs) :
    0 ≤ weight A t/weight V t ∧ weight A t/weight V t ≤ 1 := by
  have hpos := V.weight_pos ht ht1
  refine ⟨div_nonneg (A.weight_pos ht ht1).le hpos.le,(div_le_one hpos).mpr ?_⟩
  have hlog : 1 ≤ 1-Real.log t := by linarith [Real.log_nonpos ht.le ht1]
  exact mul_le_mul
    (Real.rpow_le_rpow_of_exponent_ge ht ht1 (Rat.cast_le.mpr hp))
    (pow_le_pow_right₀ hlog hl) (pow_nonneg (by linarith) _) (Real.rpow_nonneg ht.le _)

lemma coefficient_mem {A : Scale} {t : ℝ} {z : ℂ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hz : A.Mem t z) : z/(weight A t:ℂ) ∈ A.coeff := by
  have hn : (weight A t:ℂ) ≠ 0 := by exact_mod_cast (A.weight_pos ht ht1).ne'
  obtain ⟨w,hw,he⟩ := hz
  change z = (weight A t:ℂ)*w at he
  rw [he]
  simpa only [mul_div_cancel_left₀ _ hn] using hw

structure BoxModel (S : Set ℂ) {α : Type} [TopologicalSpace α] (T : Set α) (Z : CBox) where
  family : UniformFamily S T
  mem : ∀ z ∈ S, ∀ a ∈ T, family.val z a ∈ Z

structure ScaleModel (S : Set ℂ) {α : Type} [TopologicalSpace α] (T : Set α) (A : Scale) where
  family : UniformFamily S T
  mem : ∀ z ∈ S, ∀ a ∈ T, family.val z a ∈ A.coeff

namespace ScaleModel
variable {S : Set ℂ} {α : Type} [TopologicalSpace α] {T : Set α}

noncomputable abbrev actual {A : Scale} (f : ScaleModel S T A) (t : α → ℝ) (z : ℂ) (a : α) : ℂ :=
  (weight A (t a):ℂ)*f.family.val z a

lemma asMem {A : Scale} (f : ScaleModel S T A) (t : α → ℝ) {z : ℂ} (hz : z ∈ S)
    {a : α} (ha : a ∈ T) : A.Mem (t a) (f.actual t z a) :=
  ⟨f.family.val z a,f.mem z hz a ha,rfl⟩

noncomputable def neg {A : Scale} (f : ScaleModel S T A) :
    ScaleModel S T {A with coeff := CBox.neg A.coeff} where
  family := (UniformFamily.const (fun _ : α => (-1:ℂ)) continuousOn_const 1 zero_le_one
    (fun _ _ => by norm_num)).mul f.family
  mem z hz a ha := by
    simpa only [UniformFamily.mul,UniformFamily.const,neg_one_mul] using CBox.mem_neg (f.mem z hz a ha)

lemma neg_actual {A : Scale} (f : ScaleModel S T A) (t : α → ℝ) (z : ℂ) (a : α) :
    f.neg.actual t z a = -f.actual t z a := by
  simp only [neg,actual,UniformFamily.mul,UniformFamily.const,neg_one_mul,mul_neg]

lemma add {c : Ctx} (hc : c.Valid) {δ : Dy} {A B V : Scale}
    {t : α → ℝ} (ht : ContinuousOn t T) (ht0 : ∀ a ∈ T, 0 < t a)
    (htδ : ∀ a ∈ T, t a ≤ δ.toReal) (hδ1 : δ.toReal ≤ 1)
    (f : ScaleModel S T A) (g : ScaleModel S T B) (h : scaleAdd c δ A B = some V) :
    ∃ v : ScaleModel S T V, ∀ z ∈ S, ∀ a ∈ T,
      v.actual t z a = f.actual t z a+g.actual t z a := by
  have ht1 a ha := (htδ a ha).trans hδ1
  have hOrig := h
  by_cases hza : boxZero A.coeff = true
  · have he : B = V := by simpa [scaleAdd,hza] using h
    subst V
    refine ⟨g,?_⟩
    intro z hz a ha
    have hfzero := boxZero_sound (f.mem z hz a ha) hza
    simp only [actual,hfzero,mul_zero,zero_add]
  · by_cases hzb : boxZero B.coeff = true
    · have he : A = V := by simpa [scaleAdd,hza,hzb] using h
      subst V
      refine ⟨f,?_⟩
      intro z hz a ha
      have hgzero := boxZero_sound (g.mem z hz a ha) hzb
      simp only [actual,hgzero,mul_zero,add_zero]
    · unfold scaleAdd at h
      simp only [Bool.false_eq_true,↓reduceIte,hza,hzb] at h
      simp only [Bind.bind,Option.bind_eq_some_iff] at h
      obtain ⟨fa,hfa,fb,hfb,h⟩ := h
      have he := Option.some.inj h
      subst V
      let V : Scale := ⟨min A.power B.power,max A.logs B.logs,
        CBox.add c.prec
          (CBox.mul c.prec (if A.logs < max A.logs B.logs then CBox.mul c.prec fa (CBox.ofReal unit) else fa) A.coeff)
          (CBox.mul c.prec (if B.logs < max A.logs B.logs then CBox.mul c.prec fb (CBox.ofReal unit) else fb) B.coeff)⟩
      have hvpos a ha : weight V (t a) ≠ 0 := (V.weight_pos (ht0 a ha) (ht1 a ha)).ne'
      have hratA : ContinuousOn (fun a => ((weight A (t a)/weight V (t a):ℝ):ℂ)) T :=
        Complex.continuous_ofReal.comp_continuousOn
          ((weight_continuous A ht ht0).div (weight_continuous V ht ht0) hvpos)
      have hratB : ContinuousOn (fun a => ((weight B (t a)/weight V (t a):ℝ):ℂ)) T :=
        Complex.continuous_ofReal.comp_continuousOn
          ((weight_continuous B ht ht0).div (weight_continuous V ht ht0) hvpos)
      let rA : UniformFamily S T := UniformFamily.const _ hratA 1 zero_le_one (by
        intro a ha
        have hh := weight_ratio_le_one A V (ht0 a ha) (ht1 a ha) (min_le_left _ _) (Nat.le_max_left _ _)
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2)
      let rB : UniformFamily S T := UniformFamily.const _ hratB 1 zero_le_one (by
        intro a ha
        have hh := weight_ratio_le_one B V (ht0 a ha) (ht1 a ha) (min_le_right _ _) (Nat.le_max_right _ _)
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2)
      let v := (rA.mul f.family).add (rB.mul g.family)
      have hactual : ∀ z a, a ∈ T → (weight V (t a):ℂ)*v.val z a = f.actual t z a+g.actual t z a := by
        intro z a ha
        have hn : (weight V (t a):ℂ) ≠ 0 := by exact_mod_cast hvpos a ha
        dsimp only [v,UniformFamily.add,UniformFamily.mul,rA,rB,UniformFamily.const,actual]
        simp only [Complex.ofReal_div]
        field_simp
      refine ⟨⟨v,?_⟩,fun z hz a ha => hactual z a ha⟩
      intro z hz a ha
      have hm := scaleAdd_sound hc (ht0 a ha) (htδ a ha) (ht1 a ha) (f.asMem t hz ha) (g.asMem t hz ha) hOrig
      have hn : (weight V (t a):ℂ) ≠ 0 := by exact_mod_cast hvpos a ha
      have hh := coefficient_mem (ht0 a ha) (ht1 a ha) hm
      change (f.actual t z a+g.actual t z a)/(weight V (t a):ℂ) ∈ V.coeff at hh
      rw [← hactual z a ha] at hh
      simpa only [V,mul_div_cancel_left₀ _ hn] using hh

lemma sub {c : Ctx} (hc : c.Valid) {δ : Dy} {A B V : Scale}
    {t : α → ℝ} (ht : ContinuousOn t T) (ht0 : ∀ a ∈ T, 0 < t a)
    (htδ : ∀ a ∈ T, t a ≤ δ.toReal) (hδ1 : δ.toReal ≤ 1)
    (f : ScaleModel S T A) (g : ScaleModel S T B) (h : scaleAdd c δ A B true = some V) :
    ∃ v : ScaleModel S T V, ∀ z ∈ S, ∀ a ∈ T,
      v.actual t z a = f.actual t z a-g.actual t z a := by
  change scaleAdd c δ A {B with coeff := CBox.neg B.coeff} false = some V at h
  obtain ⟨v,hv⟩ := add hc ht ht0 htδ hδ1 f g.neg h
  exact ⟨v,fun z hz a ha => by rw [hv z hz a ha,g.neg_actual]; rfl⟩

lemma mul {c : Ctx} {A B : Scale} {t : α → ℝ}
    (ht0 : ∀ a ∈ T, 0 < t a) (f : ScaleModel S T A) (g : ScaleModel S T B) :
    ∃ v : ScaleModel S T (scaleMul c A B), ∀ z ∈ S, ∀ a ∈ T,
      v.actual t z a = f.actual t z a*g.actual t z a := by
  let v : ScaleModel S T (scaleMul c A B) :=
    ⟨f.family.mul g.family,fun z hz a ha => CBox.mem_mul (p := c.prec) (f.mem z hz a ha) (g.mem z hz a ha)⟩
  refine ⟨v,?_⟩
  intro z hz a ha
  have hw : weight (scaleMul c A B) (t a) = weight A (t a)*weight B (t a) := by
    simp only [weight,scaleMul,Rat.cast_add,Real.rpow_add (ht0 a ha),pow_add]
    ring
  change (weight (scaleMul c A B) (t a):ℂ)*(f.family.val z a*g.family.val z a) = _
  rw [hw,Complex.ofReal_mul]
  dsimp only [actual]
  ring

lemma pow {c : Ctx} {A : Scale} {t : α → ℝ}
    (ht0 : ∀ a ∈ T, 0 < t a) (f : ScaleModel S T A) (n : Nat) :
    ∃ v : ScaleModel S T (scalePow c A n), ∀ z ∈ S, ∀ a ∈ T,
      v.actual t z a = (f.actual t z a)^n := by
  obtain ⟨G,hG⟩ := f.family.comp isClosed_univ (fun _ _ _ _ => mem_univ _)
    (show AnalyticOnNhd ℂ (fun z : ℂ => z^n) univ from fun _ _ => analyticAt_id.pow n)
  let v : ScaleModel S T (scalePow c A n) := ⟨G,by
    intro z hz a ha
    rw [hG]
    exact powC_sound (p := c.prec) (f.mem z hz a ha) n⟩
  refine ⟨v,?_⟩
  intro z hz a ha
  have hw : weight (scalePow c A n) (t a) = (weight A (t a))^n := by
    simp only [weight,scalePow,Rat.cast_mul,Rat.cast_natCast,Real.rpow_mul (ht0 a ha).le,
      Real.rpow_natCast,mul_pow,pow_mul]
  change (weight (scalePow c A n) (t a):ℂ)*G.val z a = _
  rw [hw,Complex.ofReal_pow,hG,mul_pow]

lemma div {c : Ctx} {A B V : Scale} {t : α → ℝ}
    (ht0 : ∀ a ∈ T, 0 < t a) (f : ScaleModel S T A) (g : ScaleModel S T B)
    (h : scaleDiv c A B = some V) :
    ∃ v : ScaleModel S T V, ∀ z ∈ S, ∀ a ∈ T,
      v.actual t z a = f.actual t z a/g.actual t z a := by
  have hl : B.logs = 0 := by by_contra hn; simp [scaleDiv,hn] at h
  have hp : (CBox.normSq c.prec B.coeff).pos = true := by
    by_contra hn
    simp [scaleDiv,hn] at h
  have he : Scale.mk (A.power-B.power) A.logs (CBox.div c.prec A.coeff B.coeff) = V := by
    simpa [scaleDiv,hl,hp] using h
  subst V
  have hinv : AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) {z | z ∈ B.coeff} := by
    intro z hz
    exact analyticAt_id.inv (Complex.normSq_pos.mp (Ival.pos_of hp (CBox.mem_normSq (p := c.prec) hz)))
  obtain ⟨G,hG⟩ := g.family.comp (cbox_set_isClosed B.coeff) g.mem hinv
  let v : ScaleModel S T (Scale.mk (A.power-B.power) A.logs (CBox.div c.prec A.coeff B.coeff)) :=
    ⟨f.family.mul G,by
      intro z hz a ha
      change f.family.val z a*G.val z a ∈ CBox.div c.prec A.coeff B.coeff
      rw [hG]
      exact CBox.mem_div (p := c.prec) (f.mem z hz a ha) (g.mem z hz a ha)⟩
  refine ⟨v,?_⟩
  intro z hz a ha
  have hw : weight (Scale.mk (A.power-B.power) A.logs (CBox.div c.prec A.coeff B.coeff)) (t a) =
      weight A (t a)/weight B (t a) := by
    simp only [weight,hl,pow_zero,mul_one,Rat.cast_sub,Real.rpow_sub (ht0 a ha)]
    ring
  change (weight (Scale.mk (A.power-B.power) A.logs (CBox.div c.prec A.coeff B.coeff)) (t a):ℂ)*
    (f.family.val z a*G.val z a) = _
  rw [hw,Complex.ofReal_div,hG]
  simp only [actual,div_eq_mul_inv,mul_inv_rev]
  ring

lemma collapse {c : Ctx} (hc : c.Valid) {δ : Dy} {A : Scale} {Z : CBox}
    {t : α → ℝ} (ht : ContinuousOn t T) (ht0 : ∀ a ∈ T, 0 < t a)
    (htδ : ∀ a ∈ T, t a ≤ δ.toReal) (hδ1 : δ.toReal ≤ 1)
    (f : ScaleModel S T A) (h : Nested.collapse c δ A = some Z) :
    ∃ v : BoxModel S T Z, ∀ z ∈ S, ∀ a ∈ T, v.family.val z a = f.actual t z a := by
  have ht1 a ha := (htδ a ha).trans hδ1
  by_cases hz : boxZero A.coeff = true
  · let G : UniformFamily S T := UniformFamily.const (fun _ => (0:ℂ)) continuousOn_const 0 le_rfl (by simp)
    have he : ∀ z ∈ S, ∀ a ∈ T, f.actual t z a = 0 := by
      intro z hz' a ha
      simp only [actual,boxZero_sound (f.mem z hz' a ha) hz,mul_zero]
    refine ⟨⟨G,?_⟩,fun z hz' a ha => (he z hz' a ha).symm⟩
    intro z hz' a ha
    have hh := collapse_sound hc (ht0 a ha) (htδ a ha) (ht1 a ha) (f.asMem t hz' ha) h
    rwa [he z hz' a ha] at hh
  · have hp : 0 ≤ A.power := by
      by_contra hn
      have hn' : A.power < 0 := lt_of_not_ge hn
      simp [Nested.collapse,hz,hn'] at h
    have hp' : A.logs ≠ 0 → 0 < A.power := by
      intro hn
      have he : A.power ≠ 0 := by
        intro he
        simp [Nested.collapse,hz,he,hn] at h
      exact lt_of_le_of_ne hp (Ne.symm he)
    let C : ℝ := if A.logs = 0 then 1 else
      (2:ℝ)^A.logs * (1+(A.logs.factorial:ℝ)/((A.power:ℝ)/2)^A.logs)
    have hC : 0 ≤ C := by dsimp only [C]; split <;> positivity
    have hb : ∀ a ∈ T, ‖(weight A (t a):ℂ)‖ ≤ C := by
      intro a ha
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (A.weight_pos (ht0 a ha) (ht1 a ha))]
      dsimp only [C]
      split
      · rename_i hl
        simpa only [weight,hl,pow_zero,mul_one] using
          Real.rpow_le_one (ht0 a ha).le (ht1 a ha) (Rat.cast_nonneg.mpr hp)
      · rename_i hl
        have hpp : (0:ℝ) < (A.power:ℝ) := Rat.cast_pos.mpr (hp' hl)
        have hh := power_log_absorb (ht0 a ha) (ht1 a ha) hpp A.logs
        have hw : (t a)^((A.power:ℝ)/2) ≤ 1 := Real.rpow_le_one (ht0 a ha).le (ht1 a ha) (by positivity)
        apply hh.trans
        have hn : 0 ≤ (2:ℝ)^A.logs * (1+(A.logs.factorial:ℝ)/((A.power:ℝ)/2)^A.logs) := by positivity
        exact mul_le_of_le_one_right hn hw
    have hcont := Complex.continuous_ofReal.comp_continuousOn (weight_continuous A ht ht0)
    let G := (UniformFamily.const _ hcont C hC hb).mul f.family
    refine ⟨⟨G,?_⟩,fun _ _ _ _ => rfl⟩
    intro z hz' a ha
    exact collapse_sound hc (ht0 a ha) (htδ a ha) (ht1 a ha) (f.asMem t hz' ha) h

lemma coefficient_real {A : Scale} (f : ScaleModel S T A) {t : α → ℝ} {z : ℂ} {a : α} {x : ℝ}
    (ht : 0 < t a) (ht1 : t a ≤ 1) (h : f.actual t z a = (x:ℂ)) :
    f.family.val z a = ((x/weight A (t a):ℝ):ℂ) := by
  have hn : (weight A (t a):ℂ) ≠ 0 := by exact_mod_cast (A.weight_pos ht ht1).ne'
  apply mul_left_cancel₀ hn
  change (weight A (t a):ℂ)*f.family.val z a = _
  have hh : (weight A (t a):ℂ)*f.family.val z a = (x:ℂ) := h
  rw [hh]
  simp only [Complex.ofReal_div]
  field_simp

abbrev UnaryAgree {A V : Scale} (f : ScaleModel S T A) (v : ScaleModel S T V)
    (t : α → ℝ) (op : Unary) : Prop :=
  ∀ z ∈ S, ∀ a ∈ T, ∀ x : ℝ, f.actual t z a = (x:ℂ) →
    v.actual t z a = (op.real x:ℂ)

lemma collapsedUnary {c : Ctx} (hc : c.Valid) {δ : Dy} {A V : Scale}
    {t : α → ℝ} (ht : ContinuousOn t T) (ht0 : ∀ a ∈ T, 0 < t a)
    (htδ : ∀ a ∈ T, t a ≤ δ.toReal) (hδ1 : δ.toReal ≤ 1)
    (f : ScaleModel S T A) (op : Unary)
    (h : (do return scaleConst (← unaryC c op (← Nested.collapse c δ A))) = some V) :
    ∃ v : ScaleModel S T V, UnaryAgree f v t op := by
  simp only [Bind.bind,Option.bind_eq_some_iff] at h
  obtain ⟨ZA,hZA,Z,hZ,h⟩ := h
  have he : scaleConst Z = V := Option.some.inj h
  subst V
  obtain ⟨F,hF⟩ := collapse hc ht ht0 htδ hδ1 f hZA
  obtain ⟨φ,hφ,hφmem,hφreal⟩ := unaryC_analytic_witness hc op hZ
  obtain ⟨G,hG⟩ := F.family.comp (cbox_set_isClosed ZA) F.mem hφ
  let v : ScaleModel S T (scaleConst Z) := ⟨G,fun z hz a ha => by
    rw [hG]
    exact hφmem _ (F.mem z hz a ha)⟩
  refine ⟨v,?_⟩
  intro z hz a ha x hx
  change (weight (scaleConst Z) (t a):ℂ)*G.val z a = _
  simp only [weight,scaleConst,Rat.cast_zero,Real.rpow_zero,pow_zero,mul_one,
    Complex.ofReal_one,one_mul,hG]
  rw [hF z hz a ha,hx]
  exact hφreal x (by rw [← hx,← hF z hz a ha]; exact F.mem z hz a ha)

lemma sqrt {c : Ctx} (hc : c.Valid) {δ : Dy} {decay : Nat} {A V : Scale} {t : α → ℝ}
    (ht : ContinuousOn t T) (ht0 : ∀ a ∈ T, 0 < t a) (ht1 : ∀ a ∈ T, t a ≤ 1)
    (f : ScaleModel S T A) (h : scaleUnary c δ decay .sqrt A = some V) :
    ∃ v : ScaleModel S T V, UnaryAgree f v t .sqrt := by
  simp only [scaleUnary,Bind.bind,Option.bind_eq_some_iff] at h
  obtain ⟨Z,hZ,h⟩ := h
  have he : Scale.mk (A.power/2) ((A.logs+1)/2)
      (if A.logs == 0 then Z else CBox.mul c.prec (CBox.ofReal (Ival.ofRats 64 0 1)) Z) = V := by
    by_cases hl : A.logs = 0
    · simpa only [hl,beq_self_eq_true,↓reduceIte,Nat.zero_add,Nat.reduceDiv,Option.pure_def,Option.some.injEq] using h
    · simpa only [show (A.logs == 0) = false from by simpa using hl,Bool.false_eq_true,↓reduceIte,Option.pure_def,Option.some.injEq] using h
  subst V
  let V : Scale := Scale.mk (A.power/2) ((A.logs+1)/2)
    (if A.logs == 0 then Z else CBox.mul c.prec (CBox.ofReal (Ival.ofRats 64 0 1)) Z)
  obtain ⟨φ,hφ,hφmem,hφreal⟩ := unaryC_analytic_witness hc .sqrt hZ
  obtain ⟨G,hG⟩ := f.family.comp (cbox_set_isClosed A.coeff) f.mem hφ
  let γ : α → ℝ := fun a => Real.sqrt (weight A (t a))/weight V (t a)
  have hvpos a ha : 0 < weight V (t a) := V.weight_pos (ht0 a ha) (ht1 a ha)
  have hγ : ∀ a ∈ T, 0 ≤ γ a ∧ γ a ≤ 1 := by
    intro a ha
    obtain ⟨u,hu0,hu1,he⟩ := real_sqrt_log_scaled (p := (A.power:ℝ)) (a := 1) (m := A.logs) (ht0 a ha) (ht1 a ha)
    have he' : Real.sqrt (weight A (t a)) = weight V (t a)*u := by
      simpa only [weight,V,Rat.cast_div,Rat.cast_ofNat,Real.sqrt_one,mul_one] using he
    have heq : γ a = u := by dsimp only [γ]; rw [he']; exact mul_div_cancel_left₀ u (hvpos a ha).ne'
    simpa only [heq] using And.intro hu0 hu1
  have hγc : ContinuousOn (fun a => (γ a:ℂ)) T := Complex.continuous_ofReal.comp_continuousOn
    ((Real.continuous_sqrt.comp_continuousOn (weight_continuous A ht ht0)).div
      (weight_continuous V ht ht0) (fun a ha => (hvpos a ha).ne'))
  let γF : UniformFamily S T := UniformFamily.const _ hγc 1 zero_le_one (by
    intro a ha
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hγ a ha).1] using (hγ a ha).2)
  let H := γF.mul G
  have hHM : ∀ z ∈ S, ∀ a ∈ T, H.val z a ∈ V.coeff := by
    intro z hz a ha
    have hφz := hφmem _ (f.mem z hz a ha)
    change (γ a:ℂ)*G.val z a ∈ V.coeff
    rw [hG]
    dsimp only [V]
    by_cases hl : A.logs = 0
    · have hew : Real.sqrt (weight A (t a)) = weight V (t a) := by
        simpa only [weight,V,hl,pow_zero,mul_one,Real.sqrt_one,Nat.zero_add,Nat.reduceDiv,Rat.cast_div,Rat.cast_ofNat] using sqrt_power_factor (p := (A.power:ℝ)) (a := 1) (ht0 a ha)
      have heγ : γ a = 1 := by dsimp only [γ]; rw [hew]; exact div_self (hvpos a ha).ne'
      simpa only [hl,beq_self_eq_true,↓reduceIte,heγ,Complex.ofReal_one,one_mul] using hφz
    · simp only [show (A.logs == 0) = false from by simpa using hl,↓reduceIte]
      exact CBox.mem_mul (p := c.prec) (CBox.mem_ofReal (Ival.mem_ofRats
        (by simpa using (hγ a ha).1) (by simpa using (hγ a ha).2))) hφz
  let v : ScaleModel S T V := ⟨H,hHM⟩
  refine ⟨v,?_⟩
  intro z hz a ha x hx
  have hcR := coefficient_real f (ht0 a ha) (ht1 a ha) hx
  have hy : (((x/weight A (t a)):ℝ):ℂ) ∈ A.coeff := by
    rw [← hcR]
    exact f.mem z hz a ha
  have hφR := hφreal (x/weight A (t a)) hy
  have he : v.actual t z a = (Real.sqrt (weight A (t a)):ℂ)*φ (f.family.val z a) := by
    change (weight V (t a):ℂ)*((γ a:ℂ)*G.val z a) = _
    rw [hG]
    dsimp only [γ]
    simp only [Complex.ofReal_div]
    have hn : (weight V (t a):ℂ) ≠ 0 := by exact_mod_cast (hvpos a ha).ne'
    field_simp
  rw [he,hcR,hφR,← Complex.ofReal_mul]
  have hprod : weight A (t a)*(x/weight A (t a)) = x := by
    simpa only [mul_comm] using div_mul_cancel₀ x ((A.weight_pos (ht0 a ha) (ht1 a ha)).ne')
  simp only [Unary.real]
  rw [← Real.sqrt_mul (A.weight_pos (ht0 a ha) (ht1 a ha)).le,hprod]

lemma log {c : Ctx} (hc : c.Valid) {δ : Dy} {decay : Nat} {A V : Scale} {t : α → ℝ}
    (ht : ContinuousOn t T) (ht0 : ∀ a ∈ T, 0 < t a) (ht1 : ∀ a ∈ T, t a ≤ 1)
    (f : ScaleModel S T A) (h : scaleUnary c δ decay .log A = some V) :
    ∃ v : ScaleModel S T V, UnaryAgree f v t .log := by
  simp only [scaleUnary,Bind.bind,Option.bind_eq_some_iff] at h
  obtain ⟨Z,hZ,r,hr,R,hR,h⟩ := h
  have he : Scale.mk 0 1 (symmetricBox R) = V := Option.some.inj h
  subst V
  obtain ⟨φ,hφ,hφmem,hφreal⟩ := unaryC_analytic_witness hc .log hZ
  obtain ⟨G,hG⟩ := f.family.comp (cbox_set_isClosed A.coeff) f.mem hφ
  let L : α → ℝ := fun a => 1-Real.log (t a)
  let C : ℝ := |(A.power:ℝ)|+A.logs
  let γ : α → ℝ := fun a => Real.log (weight A (t a))/L a
  have hL (a : α) (ha : a ∈ T) : 1 ≤ L a := by dsimp [L]; linarith [Real.log_nonpos (ht0 a ha).le (ht1 a ha)]
  have hLp (a : α) (ha : a ∈ T) : 0 < L a := lt_of_lt_of_le zero_lt_one (hL a ha)
  have hLc : ContinuousOn L T := continuousOn_const.sub (fun a ha =>
    (Real.continuousAt_log (ht0 a ha).ne').comp_continuousWithinAt (ht a ha))
  have hγb : ∀ a ∈ T, |γ a| ≤ C := by
    intro a ha
    have hh := real_log_log_scaled_bound (p := (A.power:ℝ)) (a := 1) (m := A.logs) (ht0 a ha) (ht1 a ha)
    rw [abs_div,abs_of_pos (hLp a ha)]
    apply (div_le_iff₀ (hLp a ha)).mpr
    simpa only [weight,C,L,mul_one,Real.log_one,abs_zero,add_zero] using hh
  have hWlog : ContinuousOn (fun a => Real.log (weight A (t a))) T := by
    intro a ha
    exact (Real.continuousAt_log (A.weight_pos (ht0 a ha) (ht1 a ha)).ne').comp_continuousWithinAt
      (f := fun a => weight A (t a)) (weight_continuous A ht ht0 a ha)
  have hγc : ContinuousOn (fun a => (γ a:ℂ)) T := Complex.continuous_ofReal.comp_continuousOn
    (hWlog.div hLc (fun a ha => (hLp a ha).ne'))
  have hInvLc : ContinuousOn (fun a => ((1/L a:ℝ):ℂ)) T :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.div hLc (fun a ha => (hLp a ha).ne'))
  have hInvLb : ∀ a ∈ T, |1/L a| ≤ 1 := by
    intro a ha
    rw [abs_of_pos (one_div_pos.mpr (hLp a ha))]
    exact (div_le_one (hLp a ha)).mpr (hL a ha)
  let γF : UniformFamily S T := UniformFamily.const _ hγc C (by dsimp [C]; positivity)
    (fun a ha => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hγb a ha)
  let invLF : UniformFamily S T := UniformFamily.const _ hInvLc 1 zero_le_one
    (fun a ha => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hInvLb a ha)
  let H := γF.add (invLF.mul G)
  have hRlow : C+r.toReal ≤ R.toReal := by
    let B := Ival.add c.prec (Ival.ofRat c.prec |A.power|) (Ival.pt r)
    have hb : |(A.power:ℝ)|+r.toReal ∈ B := Ival.mem_add
      (by simpa only [Rat.cast_abs] using Ival.mem_ofRat c.prec |A.power|) (Ival.mem_pt r)
    by_cases hl : A.logs = 0
    · have hh : B.hi = some R := by simpa only [hl,beq_self_eq_true,↓reduceIte] using hR
      simpa only [C,hl,Nat.cast_zero,add_zero] using hb.2 R hh
    · have hh : (Ival.add c.prec B (Ival.ofRat c.prec A.logs)).hi = some R := by
        simpa only [show (A.logs == 0) = false from by simpa using hl,Bool.false_eq_true,↓reduceIte] using hR
      have hb' := (Ival.mem_add (p := c.prec) hb (Ival.mem_ofRat c.prec (A.logs:ℚ))).2 R hh
      have hb'' : |(A.power:ℝ)|+r.toReal+(A.logs:ℝ) ≤ R.toReal := by
        simpa only [Rat.cast_natCast] using hb'
      dsimp only [C]
      linarith
  have hHM : ∀ z ∈ S, ∀ a ∈ T, H.val z a ∈ (symmetricBox R) := by
    intro z hz a ha
    have hm := hφmem _ (f.mem z hz a ha)
    have hnorm : ‖φ (f.family.val z a)‖ ≤ r.toReal := (CBox.mem_norm (p := c.prec) hm).2 r hr
    apply symmetricBox_complex_mem
    change ‖(γ a:ℂ)+((1/L a:ℝ):ℂ)*G.val z a‖ ≤ _
    rw [hG]
    calc _ ≤ ‖(γ a:ℂ)‖+‖((1/L a:ℝ):ℂ)*φ (f.family.val z a)‖ := norm_add_le _ _
      _ ≤ C+‖φ (f.family.val z a)‖ := by
        apply add_le_add
        · simpa only [Complex.norm_real,Real.norm_eq_abs] using hγb a ha
        · rw [norm_mul]
          apply mul_le_of_le_one_left (norm_nonneg _)
          simpa only [Complex.norm_real,Real.norm_eq_abs] using hInvLb a ha
      _ ≤ C+r.toReal := by linarith
      _ ≤ R.toReal := hRlow
  let v : ScaleModel S T (Scale.mk 0 1 (symmetricBox R)) := ⟨H,hHM⟩
  refine ⟨v,?_⟩
  intro z hz a ha x hx
  have hcR := coefficient_real f (ht0 a ha) (ht1 a ha) hx
  have hy : (((x/weight A (t a)):ℝ):ℂ) ∈ A.coeff := by rw [← hcR]; exact f.mem z hz a ha
  have hyne := unaryC_log_real_ne_zero hZ hy
  have hφR := hφreal (x/weight A (t a)) hy
  have he : v.actual t z a = (Real.log (weight A (t a)):ℂ)+φ (f.family.val z a) := by
    change (weight (Scale.mk 0 1 (symmetricBox R)) (t a):ℂ)*
      ((γ a:ℂ)+((1/L a:ℝ):ℂ)*G.val z a) = _
    have hw : weight (Scale.mk 0 1 (symmetricBox R)) (t a) = L a := by simp [weight,L]
    rw [hw,hG]
    dsimp only [γ]
    simp only [Complex.ofReal_div,Complex.ofReal_one]
    have hn : (L a:ℂ) ≠ 0 := by exact_mod_cast (hLp a ha).ne'
    field_simp
  rw [he,hcR,hφR,← Complex.ofReal_add]
  have hprod : weight A (t a)*(x/weight A (t a)) = x := by
    simpa only [mul_comm] using div_mul_cancel₀ x ((A.weight_pos (ht0 a ha) (ht1 a ha)).ne')
  simp only [Unary.real]
  rw [← Real.log_mul (A.weight_pos (ht0 a ha) (ht1 a ha)).ne' hyne,hprod]

lemma expDecay {c : Ctx} {A : Scale} {t : α → ℝ}
    (ht : ContinuousOn t T) (ht0 : ∀ a ∈ T, 0 < t a) (ht1 : ∀ a ∈ T, t a ≤ 1)
    (f : ScaleModel S T A) (hlogs : A.logs = 0) (n : Nat) (hi R : Dy)
    (hhi : A.coeff.re.hi = some hi) (hC : Dy.isPos hi.neg = true)
    (hR : (Ival.div c.prec (Ival.ofRat c.prec n.factorial)
      (Ival.npow c.prec (Ival.pt hi.neg) n)).hi = some R) :
    ∃ v : ScaleModel S T (Scale.mk ((-A.power)*n) 0
      (if exactPoint A.coeff.im 0 then CBox.ofReal ⟨some Dy.zero,some R⟩ else symmetricBox R)),
      UnaryAgree f v t .exp := by
  let V := Scale.mk ((-A.power)*n) 0
    (if exactPoint A.coeff.im 0 then CBox.ofReal ⟨some Dy.zero,some R⟩ else symmetricBox R)
  let C := hi.neg.toReal
  have hCp : 0 < C := by
    dsimp only [C,Dy.toReal_def]
    exact Rat.cast_pos.mpr ((Dy.isPos_iff hi.neg).mp hC)
  have hRe : ∀ z ∈ S, ∀ a ∈ T, (f.family.val z a).re ≤ -C := by
    intro z hz a ha
    have hh := (f.mem z hz a ha).1.2 hi hhi
    simpa [C,Dy.toReal_def] using hh
  obtain ⟨δ,hδ,hδr,hclose⟩ := f.family.uniform_near (show 0 < C/2 by linarith)
  have hRe' : ∀ z ∈ thickening δ S, ∀ a ∈ T, (f.family.val z a).re ≤ -(C/2) := by
    intro z hz a ha
    obtain ⟨w,hw,hdist⟩ := hclose z hz a ha
    have hh := Complex.abs_re_le_norm (f.family.val z a-f.family.val w a)
    rw [Complex.sub_re,← dist_eq_norm] at hh
    have hle := hRe w hw a ha
    linarith [le_abs_self ((f.family.val z a).re-(f.family.val w a).re)]
  let F : ℂ → α → ℂ := fun z a => Complex.exp (f.actual t z a)/(weight V (t a):ℂ)
  have hvpos a (ha : a ∈ T) : 0 < weight V (t a) := V.weight_pos (ht0 a ha) (ht1 a ha)
  have hwA a : weight A (t a) = (t a)^(A.power:ℝ) := by simp only [weight,hlogs,pow_zero,mul_one]
  have hwV a : weight V (t a) = (t a)^((-(A.power:ℝ))*(n:ℝ)) := by
    simp only [weight,V,Rat.cast_mul,Rat.cast_neg,Rat.cast_natCast,pow_zero,mul_one]
  have hnorm (z : ℂ) (a : α) (ha : a ∈ T) {K : ℝ} (hK : 0 < K)
      (hneg : (f.family.val z a).re ≤ -K) : ‖F z a‖ ≤ (n.factorial:ℝ)/K^n := by
    dsimp only [F]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hvpos a ha)]
    apply (div_le_iff₀ (hvpos a ha)).mpr
    have hh := complex_exp_scaled_bound (p := (A.power:ℝ)) (z := f.family.val z a) (ht0 a ha) hK hneg n
    simpa only [actual,hwA,hwV] using hh
  have hcA : ContinuousOn (fun p : ℂ × α => ((weight A (t p.2):ℝ):ℂ)) (thickening δ S ×ˢ T) :=
    (Complex.continuous_ofReal.comp_continuousOn (weight_continuous A ht ht0)).comp
      continuous_snd.continuousOn (fun p hp => hp.2)
  have hcV : ContinuousOn (fun p : ℂ × α => ((weight V (t p.2):ℝ):ℂ)) (thickening δ S ×ˢ T) :=
    (Complex.continuous_ofReal.comp_continuousOn (weight_continuous V ht ht0)).comp
      continuous_snd.continuousOn (fun p hp => hp.2)
  have hcont : ContinuousOn (fun p : ℂ × α => F p.1 p.2) (thickening δ S ×ˢ T) := by
    have hh := Complex.continuous_exp.comp_continuousOn
      (hcA.mul (f.family.continuous.mono (Set.prod_mono (thickening_mono hδr S) Subset.rfl)))
    apply hh.div hcV
    intro p hp
    exact_mod_cast (hvpos p.2 hp.2).ne'
  let G : UniformFamily S T := {
    val := F
    radius := δ
    radius_pos := hδ
    bound := (n.factorial:ℝ)/(C/2)^n
    bound_nonneg := by positivity
    continuous := hcont
    analytic := by
      intro a ha z hz
      have hf := f.family.analytic a ha z (thickening_mono hδr S hz)
      have harg : AnalyticAt ℂ (fun z => f.actual t z a) z :=
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (weight A (t a):ℂ)) z).mul hf
      exact (analyticAt_cexp.comp (f := fun z => f.actual t z a) harg).div analyticAt_const
        (by exact_mod_cast (hvpos a ha).ne')
    norm_le := fun z hz a ha => hnorm z a ha (show 0 < C/2 by linarith) (hRe' z hz a ha)
  }
  have hnum : (n.factorial:ℝ)/C^n ≤ R.toReal :=
    (Ival.mem_div (p := c.prec) (Ival.mem_ofRat c.prec n.factorial)
      (Ival.mem_npow (Ival.mem_pt hi.neg) n)).2 R hR
  have hm : ∀ z ∈ S, ∀ a ∈ T, G.val z a ∈ V.coeff := by
    intro z hz a ha
    have hnorm' := (hnorm z a ha hCp (hRe z hz a ha)).trans hnum
    dsimp only [V]
    split
    · rename_i him
      have hzIm : (f.family.val z a).im = 0 := by simpa using exactPoint_sound (f.mem z hz a ha).2 him
      have he : f.family.val z a = ((f.family.val z a).re:ℂ) := Complex.ext rfl (by simp [hzIm])
      change F z a ∈ CBox.ofReal _
      dsimp only [F,actual]
      rw [he,← Complex.ofReal_mul,← Complex.ofReal_exp,← Complex.ofReal_div]
      apply CBox.mem_ofReal
      have hnonneg : 0 ≤ Real.exp (weight A (t a)*(f.family.val z a).re)/weight V (t a) :=
        (div_pos (Real.exp_pos _) (hvpos a ha)).le
      refine ⟨fun l hl => ?_,fun u hu => ?_⟩
      · cases Option.some.inj hl
        simpa [Dy.toReal_def] using hnonneg
      · cases Option.some.inj hu
        have hh := hnorm'
        dsimp only [F,actual] at hh
        rw [he,← Complex.ofReal_mul,← Complex.ofReal_exp,← Complex.ofReal_div,
          Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnonneg] at hh
        exact hh
    · exact symmetricBox_complex_mem hnorm'
  refine ⟨⟨G,hm⟩,?_⟩
  intro z hz a ha x hx
  change (weight V (t a):ℂ)*F z a = _
  dsimp only [F]
  rw [hx,← Complex.ofReal_exp]
  have hn : (weight V (t a):ℂ) ≠ 0 := by exact_mod_cast (hvpos a ha).ne'
  simp only [Unary.real]
  exact mul_div_cancel₀ _ hn

lemma oscillatory {c : Ctx} {A : Scale} {t : α → ℝ} (hS : Convex ℝ S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ interior S)
    (ht : ContinuousOn t T) (ht0 : ∀ a ∈ T, 0 < t a) (ht1 : ∀ a ∈ T, t a ≤ 1)
    (f : ScaleModel S T A) (op : Unary) (hop : op = .sin ∨ op = .cos)
    (him : exactPoint A.coeff.im 0 = true) :
    ∃ v : ScaleModel S T (scaleConst (CBox.ofReal (Ival.ofRats c.prec (-1) 1))), UnaryAgree f v t op := by
  have hreal : ∀ z ∈ S, ∀ a ∈ T, (f.family.val z a).im = 0 := by
    intro z hz a ha
    simpa using exactPoint_sound (f.mem z hz a ha).2 him
  have hfixed := f.family.real_constant hS hz₀ hreal
  let arg : α → ℝ := fun a => weight A (t a)*(f.family.val z₀ a).re
  have hfc : ContinuousOn (fun a => (f.family.val z₀ a).re) T :=
    Complex.continuous_re.comp_continuousOn (f.family.continuous.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun a ha => ⟨self_subset_thickening f.family.radius_pos S (interior_subset hz₀),ha⟩))
  have hargc : ContinuousOn arg T := (weight_continuous A ht ht0).mul hfc
  have hc : ContinuousOn (fun a => (op.real (arg a):ℂ)) T := by
    rcases hop with rfl | rfl
    · exact Complex.continuous_ofReal.comp_continuousOn (Real.continuous_sin.comp_continuousOn hargc)
    · exact Complex.continuous_ofReal.comp_continuousOn (Real.continuous_cos.comp_continuousOn hargc)
  have hb : ∀ a, |op.real (arg a)| ≤ 1 := by
    intro a
    rcases hop with rfl | rfl
    · exact abs_le.mpr ⟨Real.neg_one_le_sin _,Real.sin_le_one _⟩
    · exact abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  let G : UniformFamily S T := UniformFamily.const _ hc 1 zero_le_one
    (fun a ha => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hb a)
  let v : ScaleModel S T (scaleConst (CBox.ofReal (Ival.ofRats c.prec (-1) 1))) := ⟨G,by
    intro z hz a ha
    apply CBox.mem_ofReal
    exact Ival.mem_ofRats (by simpa using (abs_le.mp (hb a)).1) (by simpa using (abs_le.mp (hb a)).2)⟩
  refine ⟨v,?_⟩
  intro z hz a ha x hx
  have he : arg a = x := by
    have hh := congrArg Complex.re hx
    simpa only [actual,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
      sub_zero,hfixed z hz a ha,arg] using hh
  change (weight (scaleConst (CBox.ofReal (Ival.ofRats c.prec (-1) 1))) (t a):ℂ)*(op.real (arg a):ℂ) = _
  simp only [weight,scaleConst,Rat.cast_zero,Real.rpow_zero,pow_zero,mul_one,Complex.ofReal_one,one_mul,he]

lemma unary {c : Ctx} (hc : c.Valid) {δ : Dy} {decay : Nat} {A V : Scale} {t : α → ℝ}
    (hS : Convex ℝ S) {z₀ : ℂ} (hz₀ : z₀ ∈ interior S)
    (ht : ContinuousOn t T) (ht0 : ∀ a ∈ T, 0 < t a)
    (htδ : ∀ a ∈ T, t a ≤ δ.toReal) (hδ1 : δ.toReal ≤ 1)
    (f : ScaleModel S T A) (op : Unary) (h : scaleUnary c δ decay op A = some V) :
    ∃ v : ScaleModel S T V, UnaryAgree f v t op := by
  have ht1 a ha := (htδ a ha).trans hδ1
  cases op <;> simp only [scaleUnary] at h
  case neg =>
    have he : {A with coeff := CBox.neg A.coeff} = V := Option.some.inj h
    subst V
    exact ⟨f.neg,fun z hz a ha x hx => by rw [neg_actual,hx]; simp only [Unary.real,Complex.ofReal_neg]⟩
  case inv =>
    let one : ScaleModel S T (scaleConst (CBox.ofReal Ival.one)) :=
      ⟨UniformFamily.const (fun _ => (1:ℂ)) continuousOn_const 1 zero_le_one (by simp),
        fun _ _ _ _ => CBox.mem_ofReal Ival.mem_one⟩
    obtain ⟨v,hv⟩ := div ht0 one f h
    refine ⟨v,?_⟩
    intro z hz a ha x hx
    rw [hv z hz a ha,hx]
    simp only [one,actual,weight,scaleConst,UniformFamily.const,Rat.cast_zero,Real.rpow_zero,
      pow_zero,mul_one,Complex.ofReal_one,one_mul,one_div,Unary.real,Complex.ofReal_inv]
  case sqrt => exact sqrt hc (δ := δ) (decay := decay) ht ht0 ht1 f h
  case log => exact log hc (δ := δ) (decay := decay) ht ht0 ht1 f h
  case abs =>
    split at h
    · rename_i hnon
      have he : A = V := Option.some.inj h
      subst V
      refine ⟨f,?_⟩
      intro z hz a ha x hx
      obtain ⟨y,hy,he⟩ := A.real_coeff (ht0 a ha) (ht1 a ha) (hx ▸ f.asMem t hz ha)
      have hxpos : 0 ≤ x := he ▸ mul_nonneg (A.weight_pos (ht0 a ha) (ht1 a ha)).le (Ival.nonneg_of hnon hy.1)
      simpa only [Unary.real,abs_of_nonneg hxpos] using hx
    · split at h
      · rename_i hnon
        have he : {A with coeff := CBox.neg A.coeff} = V := Option.some.inj h
        subst V
        refine ⟨f.neg,?_⟩
        intro z hz a ha x hx
        obtain ⟨y,hy,he⟩ := A.real_coeff (ht0 a ha) (ht1 a ha) (hx ▸ f.asMem t hz ha)
        have hyneg : y ≤ 0 := by
          have hh : 0 ≤ -y := Ival.nonneg_of (Ival.neg_nonneg_of_nonpos hnon) (Ival.mem_neg hy.1)
          linarith
        have hxneg : x ≤ 0 := he ▸ mul_nonpos_of_nonneg_of_nonpos (A.weight_pos (ht0 a ha) (ht1 a ha)).le hyneg
        rw [neg_actual,hx]
        simp only [Unary.real,abs_of_nonpos hxneg,Complex.ofReal_neg]
      · simp at h
  case sin =>
    split at h
    · rename_i hosc
      have he : scaleConst (CBox.ofReal (Ival.ofRats c.prec (-1) 1)) = V := Option.some.inj h
      subst V
      exact oscillatory hS hz₀ ht ht0 ht1 f .sin (Or.inl rfl) (Bool.and_eq_true_iff.mp hosc).2
    · exact collapsedUnary hc ht ht0 htδ hδ1 f .sin h
  case cos =>
    split at h
    · rename_i hosc
      have he : scaleConst (CBox.ofReal (Ival.ofRats c.prec (-1) 1)) = V := Option.some.inj h
      subst V
      exact oscillatory hS hz₀ ht ht0 ht1 f .cos (Or.inr rfl) (Bool.and_eq_true_iff.mp hosc).2
    · exact collapsedUnary hc ht ht0 htδ hδ1 f .cos h
  case exp =>
    have hl : A.logs = 0 := by by_contra hn; simp [hn] at h
    simp only [hl,bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at h
    split at h
    · cases hhi : A.coeff.re.hi with
      | none => simp [hhi] at h
      | some hi =>
        simp only [hhi] at h
        split at h
        · simp at h
        · rename_i hgood
          have hC : Dy.isPos hi.neg = true := by
            simpa using (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hgood)).1
          cases hR : (Ival.div c.prec (Ival.ofRat c.prec decay.factorial)
              (Ival.npow c.prec (Ival.pt hi.neg) decay)).hi with
          | none => simp [hR] at h
          | some R =>
            have he : Scale.mk ((-A.power)*decay) 0
                (if exactPoint A.coeff.im 0 then CBox.ofReal ⟨some Dy.zero,some R⟩ else symmetricBox R) = V := by
              simpa only [hR,Bind.bind,Option.bind_some,Option.pure_def,Option.some.injEq] using h
            subst V
            exact expDecay ht ht0 ht1 f hl decay hi R hhi hC hR
    · exact collapsedUnary hc ht ht0 htδ hδ1 f .exp h
  all_goals exact collapsedUnary hc ht ht0 htδ hδ1 f _ h

lemma rpow {c : Ctx} (hc : c.Valid) {A : Scale} {Z : CBox} {q : ℚ} {t : α → ℝ}
    (ht0 : ∀ a ∈ T, 0 < t a) (ht1 : ∀ a ∈ T, t a ≤ 1)
    (f : ScaleModel S T A) (hl : A.logs = 0) (h : rationalPowerC c A.coeff q = some Z) :
    ∃ v : ScaleModel S T (Scale.mk (A.power*q) 0 Z), ∀ z ∈ S, ∀ a ∈ T, ∀ x : ℝ,
      f.actual t z a = (x:ℂ) → v.actual t z a = ((x^(q:ℝ):ℝ):ℂ) := by
  obtain ⟨φ,hφ,hφmem,hφreal⟩ := rationalPowerC_analytic_witness hc h
  obtain ⟨G,hG⟩ := f.family.comp (cbox_set_isClosed A.coeff) f.mem hφ
  let v : ScaleModel S T (Scale.mk (A.power*q) 0 Z) :=
    ⟨G,fun z hz a ha => by rw [hG]; exact hφmem _ (f.mem z hz a ha)⟩
  have hp : A.coeff.re.pos = true := by by_contra hn; simp [rationalPowerC,hn] at h
  refine ⟨v,?_⟩
  intro z hz a ha x hx
  have hcr := coefficient_real f (ht0 a ha) (ht1 a ha) hx
  have hy : (((x/weight A (t a)):ℝ):ℂ) ∈ A.coeff := by rw [← hcr]; exact f.mem z hz a ha
  have hyp : 0 < x/weight A (t a) := Ival.pos_of hp hy.1
  change (weight (Scale.mk (A.power*q) 0 Z) (t a):ℂ)*G.val z a = _
  rw [hG,hcr,hφreal _ hy,← Complex.ofReal_mul]
  have hprod : weight A (t a)*(x/weight A (t a)) = x := by
    simpa only [mul_comm] using div_mul_cancel₀ x ((A.weight_pos (ht0 a ha) (ht1 a ha)).ne')
  have hh := real_rpow_scaled (p := (A.power:ℝ)) (q := (q:ℝ)) (ht0 a ha) hyp
  rw [show (t a)^(A.power:ℝ) = weight A (t a) by simp only [weight,hl,pow_zero,mul_one],hprod] at hh
  simpa only [weight,Rat.cast_mul,pow_zero,mul_one] using congrArg (fun y : ℝ => (y:ℂ)) hh.symm

lemma realScalar {V : Scale} {t x : α → ℝ}
    (ht : ContinuousOn t T) (ht0 : ∀ a ∈ T, 0 < t a) (ht1 : ∀ a ∈ T, t a ≤ 1)
    (hx : ContinuousOn x T) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a ∈ T, |x a/weight V (t a)| ≤ C)
    (hm : ∀ a ∈ T, V.Mem (t a) (x a:ℂ)) :
    ∃ v : ScaleModel S T V, ∀ z ∈ S, ∀ a ∈ T, v.actual t z a = (x a:ℂ) := by
  have hcont := Complex.continuous_ofReal.comp_continuousOn
    (hx.div (weight_continuous V ht ht0) (fun a ha => (V.weight_pos (ht0 a ha) (ht1 a ha)).ne'))
  let G : UniformFamily S T := UniformFamily.const (fun a => ((x a/weight V (t a):ℝ):ℂ)) hcont C hC
    (fun a ha => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hb a ha)
  let v : ScaleModel S T V := ⟨G,by
    intro z hz a ha
    have hh := coefficient_mem (ht0 a ha) (ht1 a ha) (hm a ha)
    change ((x a/weight V (t a):ℝ):ℂ) ∈ V.coeff
    simpa only [Complex.ofReal_div] using hh⟩
  refine ⟨v,?_⟩
  intro z hz a ha
  change (weight V (t a):ℂ)*((x a/weight V (t a):ℝ):ℂ) = (x a:ℂ)
  rw [← Complex.ofReal_mul]
  congr 1
  simpa only [mul_comm] using div_mul_cancel₀ (x a) ((V.weight_pos (ht0 a ha) (ht1 a ha)).ne')

lemma logEndpoint {c : Ctx} (hc : c.Valid) {δ : Dy} {V : Scale} {t : α → ℝ}
    (ht : ContinuousOn t T) (ht0 : ∀ a ∈ T, 0 < t a)
    (htδ : ∀ a ∈ T, t a ≤ δ.toReal) (hδ : δ.toReal ≤ 1/2)
    (h : logEndpointScale c δ = some V) :
    ∃ v : ScaleModel S T V, ∀ z ∈ S, ∀ a ∈ T, v.actual t z a = (Real.log (t a):ℂ) := by
  have ht1 a ha : t a ≤ 1 := (htδ a ha).trans (hδ.trans (by norm_num))
  have hshape : V.power = 0 ∧ V.logs = 1 := by
    have hh := h
    unfold logEndpointScale at hh
    split at hh
    · simp at hh
    · simp only [Bind.bind,Option.bind_eq_some_iff] at hh
      obtain ⟨r,hr,hh⟩ := hh
      have he := Option.some.inj hh
      subst V
      exact ⟨rfl,rfl⟩
  have hxc : ContinuousOn (fun a => Real.log (t a)) T := fun a ha =>
    (Real.continuousAt_log (ht0 a ha).ne').comp_continuousWithinAt (f := t) (ht a ha)
  apply realScalar (x := fun a => Real.log (t a)) ht ht0 ht1 hxc zero_le_one
  · intro a ha
    have hlog : Real.log (t a) ≤ 0 := Real.log_nonpos (ht0 a ha).le (ht1 a ha)
    have hLp : 0 < 1-Real.log (t a) := by linarith
    simp only [weight,hshape.1,hshape.2,Rat.cast_zero,Real.rpow_zero,pow_one,one_mul,
      abs_div,abs_of_nonpos hlog,abs_of_pos hLp]
    apply (div_le_one hLp).mpr
    linarith
  · intro a ha
    exact logEndpointScale_real_sound hc (ht0 a ha) (htδ a ha) hδ h

lemma logOneMinus {c : Ctx} {δ : Dy} {V : Scale} {t : α → ℝ}
    (ht : ContinuousOn t T) (ht0 : ∀ a ∈ T, 0 < t a)
    (htδ : ∀ a ∈ T, t a ≤ δ.toReal) (hδ : δ.toReal ≤ 1/2)
    (h : logOneMinusEndpointScale c δ = some V) :
    ∃ v : ScaleModel S T V, ∀ z ∈ S, ∀ a ∈ T, v.actual t z a = (Real.log (1-t a):ℂ) := by
  have ht1 a ha : t a ≤ 1 := (htδ a ha).trans (hδ.trans (by norm_num))
  have hshape : V.power = 1 ∧ V.logs = 0 := by
    have hh := h
    unfold logOneMinusEndpointScale at hh
    split at hh
    · simp at hh
    · simp only [Bind.bind,Option.bind_eq_some_iff] at hh
      obtain ⟨r,hr,hh⟩ := hh
      have he := Option.some.inj hh
      subst V
      exact ⟨rfl,rfl⟩
  have hxp a (ha : a ∈ T) : 0 < 1-t a := by linarith [htδ a ha,hδ]
  have hxc : ContinuousOn (fun a => Real.log (1-t a)) T := fun a ha =>
    (Real.continuousAt_log (hxp a ha).ne').comp_continuousWithinAt
      (f := fun a => 1-t a) (((continuousOn_const (c := 1)).sub ht) a ha)
  apply realScalar (x := fun a => Real.log (1-t a)) ht ht0 ht1 hxc (by norm_num : (0:ℝ) ≤ 2)
  · intro a ha
    simp only [weight,hshape.1,hshape.2,Rat.cast_one,Real.rpow_one,pow_zero,mul_one]
    have hb := real_log_one_sub_div_bounds (ht0 a ha) (htδ a ha) hδ
    have hp : 0 < 1-δ.toReal := by linarith
    have hInv : 1/(1-δ.toReal) ≤ 2 := by rw [div_le_iff₀ hp]; linarith
    have hb1 := hb.1
    rw [neg_div] at hb1
    exact abs_le.mpr ⟨by linarith,by linarith [hb.2]⟩
  · intro a ha
    exact logOneMinusEndpointScale_real_sound (ht0 a ha) (htδ a ha) hδ h

end ScaleModel
end Lynth.Interval.Integral.Nested.AnalyticWork
