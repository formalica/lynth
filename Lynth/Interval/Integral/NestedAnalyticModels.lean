import Lynth.Interval.Integral.NestedAnalyticScale
import Lynth.Interval.Integral.NestedBoundCSound

/-! Box models, scoped parameter environments, and finite integration of analytic families. -/

namespace Lynth.Interval.Integral.Nested.AnalyticWork
open Intgrl Fns MeasureTheory Set Metric
open scoped Topology
open private finite_value_eq from Lynth.Interval.Integral.NestedPrimitiveProof
open private unit from Lynth.Interval.Integral.NestedBounds

namespace BoxModel
variable {S : Set ℂ} {α : Type} [TopologicalSpace α] {T : Set α}

noncomputable def constant {Z : CBox} (v : ℂ) (hv : v ∈ Z) : BoxModel S T Z :=
  ⟨UniformFamily.const (fun _ => v) continuousOn_const ‖v‖ (norm_nonneg _) (by simp),
    fun _ _ _ _ => hv⟩

noncomputable def reindex {β : Type} [TopologicalSpace β] {U : Set β} {Z : CBox}
    (f : BoxModel S T Z) (g : β → α) (hg : ContinuousOn g U) (hm : MapsTo g U T) :
    BoxModel S U Z :=
  ⟨f.family.reindex g hg hm,fun z hz a ha => f.mem z hz (g a) (hm ha)⟩

noncomputable def toScale {Z : CBox} (f : BoxModel S T Z) : ScaleModel S T (scaleConst Z) :=
  ⟨f.family,f.mem⟩

lemma toScale_actual {Z : CBox} (f : BoxModel S T Z) (t : α → ℝ) (z : ℂ) (a : α) :
    f.toScale.actual t z a = f.family.val z a := by
  simp only [toScale,ScaleModel.actual,weight,scaleConst,Rat.cast_zero,Real.rpow_zero,pow_zero,
    mul_one,Complex.ofReal_one,one_mul]

lemma unary {c : Ctx} (hc : c.Valid) {A B : CBox} (f : BoxModel S T A) (op : Unary)
    (h : unaryC c op A = some B) :
    ∃ v : BoxModel S T B, ∀ z ∈ S, ∀ a ∈ T, ∀ x : ℝ,
      f.family.val z a = (x:ℂ) → v.family.val z a = (op.real x:ℂ) := by
  obtain ⟨φ,hφ,hmem,hreal⟩ := unaryC_analytic_witness hc op h
  obtain ⟨g,hg⟩ := f.family.comp (cbox_set_isClosed A) f.mem hφ
  exact ⟨⟨g,fun z hz a ha => hg z a ▸ hmem _ (f.mem z hz a ha)⟩,
    fun z hz a ha x hx => by rw [hg,hx]; exact hreal x (hx ▸ f.mem z hz a ha)⟩

noncomputable def add {p : Nat} {A B : CBox} (f : BoxModel S T A) (g : BoxModel S T B) :
    BoxModel S T (CBox.add p A B) :=
  ⟨f.family.add g.family,fun z hz a ha => CBox.mem_add (p := p) (f.mem z hz a ha) (g.mem z hz a ha)⟩

noncomputable def sub {p : Nat} {A B : CBox} (f : BoxModel S T A) (g : BoxModel S T B) :
    BoxModel S T (CBox.sub p A B) :=
  ⟨f.family.add g.family.neg,fun z hz a ha => by
    simpa only [UniformFamily.add,UniformFamily.neg,sub_eq_add_neg] using
      CBox.mem_sub (p := p) (f.mem z hz a ha) (g.mem z hz a ha)⟩

noncomputable def mul {p : Nat} {A B : CBox} (f : BoxModel S T A) (g : BoxModel S T B) :
    BoxModel S T (CBox.mul p A B) :=
  ⟨f.family.mul g.family,fun z hz a ha => CBox.mem_mul (p := p) (f.mem z hz a ha) (g.mem z hz a ha)⟩

lemma binary {c : Ctx} (hc : c.Valid) {A B V : CBox}
    (f : BoxModel S T A) (g : BoxModel S T B) (op : Binary)
    (h : binaryC c op A B = some V) :
    ∃ v : BoxModel S T V, ∀ z ∈ S, ∀ a ∈ T, ∀ x y : ℝ,
      f.family.val z a = (x:ℂ) → g.family.val z a = (y:ℂ) →
      v.family.val z a = (op.real x y:ℂ) := by
  cases op with
  | add =>
    have he : CBox.add c.prec A B = V := finite_value_eq h
    subst V
    exact ⟨f.add g,fun z hz a ha x y hx hy => by
      simp only [add,UniformFamily.add,hx,hy,Binary.real,Complex.ofReal_add]⟩
  | sub =>
    have he : CBox.sub c.prec A B = V := finite_value_eq h
    subst V
    exact ⟨f.sub g,fun z hz a ha x y hx hy => by
      simp only [sub,UniformFamily.add,UniformFamily.neg,hx,hy,Binary.real,Complex.ofReal_sub,sub_eq_add_neg,Complex.ofReal_add,Complex.ofReal_neg]⟩
  | mul =>
    have he : CBox.mul c.prec A B = V := finite_value_eq h
    subst V
    exact ⟨f.mul g,fun z hz a ha x y hx hy => by
      simp only [mul,UniformFamily.mul,hx,hy,Binary.real,Complex.ofReal_mul]⟩
  | div =>
    have hp : (CBox.normSq c.prec B).pos = true := by
      by_contra hn; simp [binaryC,hn] at h
    have he : CBox.div c.prec A B = V := by
      apply finite_value_eq
      simpa only [binaryC,hp,↓reduceIte,Bind.bind,Option.bind_some] using h
    subst V
    have hn : ∀ w ∈ B, w ≠ 0 := by
      intro w hw hw0
      have hh := Ival.pos_of hp (CBox.mem_normSq (p := c.prec) hw)
      simpa [hw0] using hh
    obtain ⟨gi,hgi⟩ := g.family.comp (φ := fun w : ℂ => w⁻¹) (cbox_set_isClosed B) g.mem
      (fun w hw => analyticAt_id.inv (hn w hw))
    refine ⟨⟨f.family.mul gi,fun z hz a ha => ?_⟩,?_⟩
    · simpa only [UniformFamily.mul,hgi,div_eq_mul_inv] using
        CBox.mem_div (p := c.prec) (f.mem z hz a ha) (g.mem z hz a ha)
    · intro z hz a ha x y hx hy
      simp only [UniformFamily.mul,hgi,hx,hy,Binary.real,Complex.ofReal_div,div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv]
  | max | min =>
    all_goals
      unfold binaryC at h
      by_cases hab : Ival.leB A.re B.re = true
      · simp only [hab,↓reduceIte,Bind.bind,Option.bind_some] at h
        have he := finite_value_eq h
        subst V
        first
        | refine ⟨g,?_⟩
          intro z hz a ha x y hx hy
          have hxy := Ival.le_of_leB (show x ∈ A.re by simpa only [hx,Complex.ofReal_re] using (f.mem z hz a ha).1)
            (show y ∈ B.re by simpa only [hy,Complex.ofReal_re] using (g.mem z hz a ha).1) hab
          simpa only [Binary.real,max_eq_right hxy] using hy
        | refine ⟨f,?_⟩
          intro z hz a ha x y hx hy
          have hxy := Ival.le_of_leB (show x ∈ A.re by simpa only [hx,Complex.ofReal_re] using (f.mem z hz a ha).1)
            (show y ∈ B.re by simpa only [hy,Complex.ofReal_re] using (g.mem z hz a ha).1) hab
          simpa only [Binary.real,min_eq_left hxy] using hx
      · by_cases hba : Ival.leB B.re A.re = true
        · simp only [hab,hba,↓reduceIte,Bind.bind,Option.bind_some] at h
          have he := finite_value_eq h
          subst V
          first
          | refine ⟨f,?_⟩
            intro z hz a ha x y hx hy
            have hyx := Ival.le_of_leB (show y ∈ B.re by simpa only [hy,Complex.ofReal_re] using (g.mem z hz a ha).1)
              (show x ∈ A.re by simpa only [hx,Complex.ofReal_re] using (f.mem z hz a ha).1) hba
            simpa only [Binary.real,max_eq_left hyx] using hx
          | refine ⟨g,?_⟩
            intro z hz a ha x y hx hy
            have hyx := Ival.le_of_leB (show y ∈ B.re by simpa only [hy,Complex.ofReal_re] using (g.mem z hz a ha).1)
              (show x ∈ A.re by simpa only [hx,Complex.ofReal_re] using (f.mem z hz a ha).1) hba
            simpa only [Binary.real,min_eq_right hyx] using hy
        · simp [hab,hba] at h

lemma pow {p : Nat} {A : CBox} (f : BoxModel S T A) (n : Nat) :
    ∃ v : BoxModel S T (powC p A n), ∀ z a, v.family.val z a = f.family.val z a^n := by
  obtain ⟨g,hg⟩ := f.family.comp (φ := fun w : ℂ => w^n) (cbox_set_isClosed A) f.mem
    (fun w _ => analyticAt_id.pow n)
  exact ⟨⟨g,fun z hz a ha => hg z a ▸ powC_sound (p := p) (f.mem z hz a ha) n⟩,hg⟩

lemma rpow {c : Ctx} (hc : c.Valid) {A B : CBox} (f : BoxModel S T A) (q : ℚ)
    (h : rationalPowerC c A q = some B) :
    ∃ v : BoxModel S T B, ∀ z ∈ S, ∀ a ∈ T, ∀ x : ℝ,
      f.family.val z a = (x:ℂ) → v.family.val z a = ((x^(q:ℝ):ℝ):ℂ) := by
  obtain ⟨φ,hφ,hm,hr⟩ := rationalPowerC_analytic_witness hc h
  obtain ⟨g,hg⟩ := f.family.comp (cbox_set_isClosed A) f.mem hφ
  exact ⟨⟨g,fun z hz a ha => hg z a ▸ hm _ (f.mem z hz a ha)⟩,
    fun z hz a ha x hx => by rw [hg,hx]; exact hr x (hx ▸ f.mem z hz a ha)⟩

noncomputable def mean [FirstCountableTopology α] {Z : CBox}
    (f : BoxModel S (T ×ˢ Icc (0:ℝ) 1) Z) : BoxModel S T Z := by
  let g := f.family.reindex id continuousOn_id
    (show MapsTo id (T ×ˢ Ioc (0:ℝ) 1) (T ×ˢ Icc (0:ℝ) 1) from
      fun p hp => ⟨hp.1,hp.2.1.le,hp.2.2⟩)
  let v := UniformFamily.integralSet measurableSet_Ioc g (fun _ => (1:ℂ)) (integrableOn_const (by simp))
  refine ⟨v,?_⟩
  intro z hz a ha
  change (∫ u in Ioc (0:ℝ) 1, (1:ℂ)*f.family.val z (a,u)) ∈ Z
  simp only [one_mul,← intervalIntegral.integral_of_le (zero_le_one : (0:ℝ)≤1)]
  have hcont : ContinuousOn (fun u => f.family.val z (a,u)) (Icc (0:ℝ) 1) :=
    f.family.continuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn
      (fun u hu => ⟨self_subset_thickening f.family.radius_pos S hz,ha,hu⟩)
  exact cbox_intervalIntegral_mem_unit (hcont.intervalIntegrable_of_Icc zero_le_one)
    (fun u hu => f.mem z hz (a,u) ⟨ha,hu.1.le,hu.2.le⟩)

lemma mean_val [FirstCountableTopology α] {Z : CBox}
    (f : BoxModel S (T ×ˢ Icc (0:ℝ) 1) Z) (z : ℂ) (a : α) :
    f.mean.family.val z a = ∫ u in (0:ℝ)..1, f.family.val z (a,u) := by
  change (∫ u in Ioc (0:ℝ) 1, (1:ℂ)*f.family.val z (a,u)) = _
  simp only [one_mul,intervalIntegral.integral_of_le (zero_le_one : (0:ℝ)≤1)]

end BoxModel
end Lynth.Interval.Integral.Nested.AnalyticWork

namespace Lynth.Interval.Integral.Nested.AnalyticWork
open Intgrl Fns MeasureTheory Set Metric
open scoped Topology

structure ScaleInputs (S : Set ℂ) {α : Type} [TopologicalSpace α] (T : Set α) (env : Array Scale) where
  family : Nat → UniformFamily S T
  mem : ∀ i < env.size, ∀ z ∈ S, ∀ a ∈ T, (family i).val z a ∈ (env[i]!).coeff

namespace ScaleInputs
variable {S : Set ℂ} {α : Type} [TopologicalSpace α] {T : Set α} {env : Array Scale}

def get (p : ScaleInputs S T env) (i : Nat) (hi : i < env.size) : ScaleModel S T env[i]! :=
  ⟨p.family i,p.mem i hi⟩

def Realizes (p : ScaleInputs S T env) (t : α → ℝ) (z : ℂ) (a : α) (xs : List ℝ) : Prop :=
  xs.length = env.size ∧ ∀ i < env.size,
    (weight env[i]! (t a):ℂ)*(p.family i).val z a = ((xs[i]?.getD 0:ℝ):ℂ)

lemma real_mem (p : ScaleInputs S T env) {t : α → ℝ} {z : ℂ} (hz : z ∈ S)
    {a : α} (ha : a ∈ T) {xs : List ℝ} (hx : p.Realizes t z a xs) :
    ∀ i < env.size, (env[i]!).Mem (t a) ((xs[i]?.getD 0:ℝ):ℂ) := by
  intro i hi
  rw [← hx.2 i hi]
  exact (p.get i hi).asMem t hz ha

lemma real_sound {c : Ctx} (hc : c.Valid) {δ : Dy} {decay fuel : Nat}
    {e : Expr} {V : Scale} (hs : e.scoped env.size = true)
    (h : scaled fuel c δ decay e env = some V) (p : ScaleInputs S T env)
    {t : α → ℝ} {z : ℂ} (hz : z ∈ S) {a : α} (ha : a ∈ T)
    (ht : 0 < t a) (htδ : t a ≤ δ.toReal) (ht1 : t a ≤ 1)
    {xs : List ℝ} (hx : p.Realizes t z a xs) : e.Converges xs ∧ V.Mem (t a) (e.real xs:ℂ) := by
  let q : ParameterPath Unit univ env.size :=
    ⟨fun _ => xs,fun _ _ => hx.1,fun _ _ => continuousOn_const⟩
  exact (scaled_real_model hc ht htδ ht1 fuel e env V hs h univ q
    (fun _ _ => p.real_mem hz ha hx)).2 () (mem_univ ())

def reindex {β : Type} [TopologicalSpace β] {U : Set β}
    (p : ScaleInputs S T env) (g : β → α) (hg : ContinuousOn g U) (hm : MapsTo g U T) :
    ScaleInputs S U env where
  family i := (p.family i).reindex g hg hm
  mem i hi z hz a ha := p.mem i hi z hz (g a) (hm ha)

lemma reindex_realizes {β : Type} [TopologicalSpace β] {U : Set β}
    (p : ScaleInputs S T env) (g : β → α) (hg : ContinuousOn g U) (hm : MapsTo g U T)
    {t : α → ℝ} {z : ℂ} {a : β} {xs : List ℝ} (hx : p.Realizes t z (g a) xs) :
    (p.reindex g hg hm).Realizes (t ∘ g) z a xs := hx

def push (p : ScaleInputs S T env) {Y : Scale} (y : ScaleModel S T Y) :
    ScaleInputs S T (env.push Y) where
  family i := if i < env.size then p.family i else y.family
  mem i hi z hz a ha := by
    by_cases hin : i < env.size
    · have hip : i < (env.push Y).size := hi
      simpa only [hin,↓reduceIte,getElem!_pos (env.push Y) i hip,Array.getElem_push_lt hin,
        getElem!_pos env i hin] using p.mem i hin z hz a ha
    · have he : i = env.size := by simp only [Array.size_push] at hi; omega
      subst i
      simpa only [hin,↓reduceIte,getElem!_pos (env.push Y) env.size (by simp),Array.getElem_push_eq]
        using y.mem z hz a ha

lemma push_realizes (p : ScaleInputs S T env) {Y : Scale} (y : ScaleModel S T Y)
    {t : α → ℝ} {z : ℂ} {a : α} {xs : List ℝ} (hx : p.Realizes t z a xs) {x : ℝ}
    (hy : y.actual t z a = (x:ℂ)) : (p.push y).Realizes t z a (xs++[x]) := by
  refine ⟨by simp [hx.1],?_⟩
  intro i hi
  by_cases hin : i < env.size
  · simpa only [push,hin,↓reduceIte,getElem!_pos (env.push Y) i hi,Array.getElem_push_lt hin,
      getElem!_pos env i hin,List.getElem?_append,hx.1,hin] using hx.2 i hin
  · have he : i = env.size := by simp only [Array.size_push] at hi; omega
    subst i
    simpa [Realizes,push,ScaleModel.actual,hx.1] using hy

end ScaleInputs

structure BoxInputs (S : Set ℂ) {α : Type} [TopologicalSpace α] (T : Set α) (env : Array CBox) where
  family : Nat → UniformFamily S T
  mem : ∀ i < env.size, ∀ z ∈ S, ∀ a ∈ T, (family i).val z a ∈ env[i]!

namespace BoxInputs
variable {S : Set ℂ} {α : Type} [TopologicalSpace α] {T : Set α} {env : Array CBox}

def get (p : BoxInputs S T env) (i : Nat) (hi : i < env.size) : BoxModel S T env[i]! :=
  ⟨p.family i,p.mem i hi⟩

def Realizes (p : BoxInputs S T env) (z : ℂ) (a : α) (xs : List ℝ) : Prop :=
  xs.length = env.size ∧ ∀ i < env.size, (p.family i).val z a = ((xs[i]?.getD 0:ℝ):ℂ)

lemma real_mem (p : BoxInputs S T env) {z : ℂ} (hz : z ∈ S)
    {a : α} (ha : a ∈ T) {xs : List ℝ} (hx : p.Realizes z a xs) :
    ∀ i < env.size, ((xs[i]?.getD 0:ℝ):ℂ) ∈ env[i]! := by
  intro i hi
  rw [← hx.2 i hi]
  exact p.mem i hi z hz a ha

lemma real_sound {c : Ctx} (hc : c.Valid) {fuel : Nat}
    {e : Expr} {V : CBox} (hs : e.scoped env.size = true)
    (h : boundC fuel c e env = some V) (p : BoxInputs S T env)
    {z : ℂ} (hz : z ∈ S) {a : α} (ha : a ∈ T)
    {xs : List ℝ} (hx : p.Realizes z a xs) : e.Converges xs ∧ (e.real xs:ℂ) ∈ V :=
  boundC_real_sound hc hs hx.1 (p.real_mem hz ha hx) h

def reindex {β : Type} [TopologicalSpace β] {U : Set β}
    (p : BoxInputs S T env) (g : β → α) (hg : ContinuousOn g U) (hm : MapsTo g U T) :
    BoxInputs S U env where
  family i := (p.family i).reindex g hg hm
  mem i hi z hz a ha := p.mem i hi z hz (g a) (hm ha)

lemma reindex_realizes {β : Type} [TopologicalSpace β] {U : Set β}
    (p : BoxInputs S T env) (g : β → α) (hg : ContinuousOn g U) (hm : MapsTo g U T)
    {z : ℂ} {a : β} {xs : List ℝ} (hx : p.Realizes z (g a) xs) :
    (p.reindex g hg hm).Realizes z a xs := hx

def push (p : BoxInputs S T env) {Y : CBox} (y : BoxModel S T Y) :
    BoxInputs S T (env.push Y) where
  family i := if i < env.size then p.family i else y.family
  mem i hi z hz a ha := by
    by_cases hin : i < env.size
    · have hip : i < (env.push Y).size := hi
      simpa only [hin,↓reduceIte,getElem!_pos (env.push Y) i hip,Array.getElem_push_lt hin,
        getElem!_pos env i hin] using p.mem i hin z hz a ha
    · have he : i = env.size := by simp only [Array.size_push] at hi; omega
      subst i
      simpa only [hin,↓reduceIte,getElem!_pos (env.push Y) env.size (by simp),Array.getElem_push_eq]
        using y.mem z hz a ha

lemma push_realizes (p : BoxInputs S T env) {Y : CBox} (y : BoxModel S T Y)
    {z : ℂ} {a : α} {xs : List ℝ} (hx : p.Realizes z a xs) {x : ℝ}
    (hy : y.family.val z a = (x:ℂ)) : (p.push y).Realizes z a (xs++[x]) := by
  refine ⟨by simp [hx.1],?_⟩
  intro i hi
  by_cases hin : i < env.size
  · simpa only [push,hin,↓reduceIte,getElem!_pos (env.push Y) i hi,Array.getElem_push_lt hin,
      getElem!_pos env i hin,List.getElem?_append,hx.1,hin] using hx.2 i hin
  · have he : i = env.size := by simp only [Array.size_push] at hi; omega
    subst i
    simpa [push,hx.1] using hy

def toScale (p : BoxInputs S T env) : ScaleInputs S T (env.map scaleConst) where
  family := p.family
  mem i hi z hz a ha := by
    have hin : i < env.size := by simpa using hi
    simpa only [getElem!_pos (env.map scaleConst) i hi,Array.getElem_map,getElem!_pos env i hin,scaleConst]
      using p.mem i hin z hz a ha

lemma toScale_realizes (p : BoxInputs S T env) (t : α → ℝ)
    {z : ℂ} {a : α} {xs : List ℝ} (hx : p.Realizes z a xs) :
    p.toScale.Realizes t z a xs := by
  refine ⟨by simpa using hx.1,?_⟩
  intro i hi
  have hin : i < env.size := by simpa using hi
  simpa only [toScale,getElem!_pos (env.map scaleConst) i hi,Array.getElem_map,
    weight,scaleConst,Rat.cast_zero,Real.rpow_zero,pow_zero,mul_one,Complex.ofReal_one,one_mul]
    using hx.2 i hin

end BoxInputs
end Lynth.Interval.Integral.Nested.AnalyticWork

namespace Lynth.Interval.Integral.Nested.AnalyticWork
open Intgrl Fns MeasureTheory Set Metric
open scoped Topology
open private unit from Lynth.Interval.Integral.NestedBounds

lemma finite_value_affine {k : NDomain} (hk : k.finite = true) {a b : ℝ}
    (horder : k ≠ .interval → a ≤ b) (f : ℝ → ℝ) :
    k.value f a b = ∫ u in (0:ℝ)..1, (b-a)*f (a+(b-a)*u) := by
  have he : k.value f a b = ∫ x in a..b, f x := by
    cases k <;> simp only [NDomain.finite,Bool.false_eq_true] at hk
    · rfl
    all_goals
      have hab : a ≤ b := horder (by intro h; cases h)
      simp only [NDomain.value,intervalIntegral.integral_of_le hab,
        integral_Icc_eq_integral_Ioc,integral_Ico_eq_integral_Ioc,← integral_Ioc_eq_integral_Ioo]
  rw [he]
  rcases eq_or_ne (b-a) 0 with h | h
  · have hb : b = a := by linarith
    subst b; simp
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_add_mul _ h]
  simp only [mul_zero,add_zero,mul_one,add_sub_cancel,smul_eq_mul]
  field_simp

namespace ScaleModel
variable {S : Set ℂ} {α : Type} [TopologicalSpace α] {T : Set α}

def reindex {β : Type} [TopologicalSpace β] {U : Set β} {A : Scale}
    (f : ScaleModel S T A) (g : β → α) (hg : ContinuousOn g U) (hm : MapsTo g U T) :
    ScaleModel S U A :=
  ⟨f.family.reindex g hg hm,fun z hz a ha => f.mem z hz (g a) (hm ha)⟩

noncomputable def mean [FirstCountableTopology α] {A : Scale}
    (f : ScaleModel S (T ×ˢ Icc (0:ℝ) 1) A) : ScaleModel S T A :=
  let b : BoxModel S (T ×ˢ Icc (0:ℝ) 1) A.coeff := ⟨f.family,f.mem⟩
  ⟨b.mean.family,b.mean.mem⟩

lemma mean_actual [FirstCountableTopology α] {A : Scale}
    (f : ScaleModel S (T ×ˢ Icc (0:ℝ) 1) A) (t : α → ℝ) (z : ℂ) (a : α) :
    f.mean.actual t z a = ∫ u in (0:ℝ)..1, f.actual (t ∘ Prod.fst) z (a,u) := by
  change (weight A (t a):ℂ)*(BoxModel.mean ⟨f.family,f.mem⟩).family.val z a = _
  rw [BoxModel.mean_val,← intervalIntegral.integral_const_mul]
  rfl

noncomputable def unitModel : ScaleModel S (T ×ˢ Icc (0:ℝ) 1) (scaleConst (CBox.ofReal unit)) :=
  (show BoxModel S (T ×ˢ Icc (0:ℝ) 1) (CBox.ofReal unit) from
    ⟨UniformFamily.const (fun p : α × ℝ => (p.2:ℂ))
      (Complex.continuous_ofReal.comp continuous_snd).continuousOn 1 zero_le_one
      (fun p hp => by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp.2.1] using hp.2.2),
      fun z hz p hp => CBox.mem_ofReal (Ival.mem_ofRats (by simpa using hp.2.1) (by simpa using hp.2.2))⟩).toScale

lemma unitModel_actual (t : (α × ℝ) → ℝ) (z : ℂ) (a : α × ℝ) :
    (unitModel (S := S) (T := T)).actual t z a = (a.2:ℂ) :=
  BoxModel.toScale_actual _ _ _ _

end ScaleModel
end Lynth.Interval.Integral.Nested.AnalyticWork
