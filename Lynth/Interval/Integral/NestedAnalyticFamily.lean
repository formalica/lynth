module

import all Lynth.Interval.Integral.Math.NestedAnalyticEnvelope
import all Lynth.Interval.Integral.NestedAnalyticPrimitive
import all Lynth.Interval.Integral.NestedRangeModel

/-! Uniformly bounded analytic families with continuous auxiliary parameters. -/

namespace Lynth.Interval.Integral.Nested.AnalyticWork
open Intgrl MeasureTheory Set Metric
open scoped Topology

structure UniformFamily (S : Set ℂ) {α : Type} [TopologicalSpace α] (T : Set α) where
  val : ℂ → α → ℂ
  radius : ℝ
  radius_pos : 0 < radius
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  continuous : ContinuousOn (fun p : ℂ × α => val p.1 p.2) (thickening radius S ×ˢ T)
  analytic : ∀ a ∈ T, AnalyticOnNhd ℂ (fun z => val z a) (thickening radius S)
  norm_le : ∀ z ∈ thickening radius S, ∀ a ∈ T, ‖val z a‖ ≤ bound

namespace UniformFamily
variable {S : Set ℂ} {α : Type} [TopologicalSpace α] {T : Set α}

lemma norm_le_on (f : UniformFamily S T) {z : ℂ} (hz : z ∈ S) {a : α} (ha : a ∈ T) :
    ‖f.val z a‖ ≤ f.bound :=
  f.norm_le z (self_subset_thickening f.radius_pos S hz) a ha

def restrict (f : UniformFamily S T) (r : ℝ) (hr : 0 < r) (hle : r ≤ f.radius) :
    UniformFamily S T where
  val := f.val
  radius := r
  radius_pos := hr
  bound := f.bound
  bound_nonneg := f.bound_nonneg
  continuous := f.continuous.mono (Set.prod_mono (thickening_mono hle S) Subset.rfl)
  analytic a ha := (f.analytic a ha).mono (thickening_mono hle S)
  norm_le z hz a ha := f.norm_le z (thickening_mono hle S hz) a ha

def const (c : α → ℂ) (hc : ContinuousOn c T) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ a ∈ T, ‖c a‖ ≤ C) : UniformFamily S T where
  val _ a := c a
  radius := 1
  radius_pos := zero_lt_one
  bound := C
  bound_nonneg := hC
  continuous := hc.comp continuous_snd.continuousOn (fun p hp => hp.2)
  analytic a ha := analyticOnNhd_const
  norm_le z hz a ha := hb a ha

def add (f g : UniformFamily S T) : UniformFamily S T where
  val z a := f.val z a+g.val z a
  radius := min f.radius g.radius
  radius_pos := lt_min f.radius_pos g.radius_pos
  bound := f.bound+g.bound
  bound_nonneg := add_nonneg f.bound_nonneg g.bound_nonneg
  continuous := (f.continuous.mono (Set.prod_mono (thickening_mono (min_le_left _ _) S) Subset.rfl)).add
    (g.continuous.mono (Set.prod_mono (thickening_mono (min_le_right _ _) S) Subset.rfl))
  analytic a ha := ((f.analytic a ha).mono (thickening_mono (min_le_left _ _) S)).add
    ((g.analytic a ha).mono (thickening_mono (min_le_right _ _) S))
  norm_le z hz a ha := (norm_add_le _ _).trans (add_le_add
    (f.norm_le z (thickening_mono (min_le_left _ _) S hz) a ha)
    (g.norm_le z (thickening_mono (min_le_right _ _) S hz) a ha))

def mul (f g : UniformFamily S T) : UniformFamily S T where
  val z a := f.val z a*g.val z a
  radius := min f.radius g.radius
  radius_pos := lt_min f.radius_pos g.radius_pos
  bound := f.bound*g.bound
  bound_nonneg := mul_nonneg f.bound_nonneg g.bound_nonneg
  continuous := (f.continuous.mono (Set.prod_mono (thickening_mono (min_le_left _ _) S) Subset.rfl)).mul
    (g.continuous.mono (Set.prod_mono (thickening_mono (min_le_right _ _) S) Subset.rfl))
  analytic a ha := ((f.analytic a ha).mono (thickening_mono (min_le_left _ _) S)).mul
    ((g.analytic a ha).mono (thickening_mono (min_le_right _ _) S))
  norm_le z hz a ha := by
    rw [norm_mul]
    exact mul_le_mul
      (f.norm_le z (thickening_mono (min_le_left _ _) S hz) a ha)
      (g.norm_le z (thickening_mono (min_le_right _ _) S hz) a ha) (norm_nonneg _) f.bound_nonneg

def neg (f : UniformFamily S T) : UniformFamily S T where
  val z a := -f.val z a
  radius := f.radius
  radius_pos := f.radius_pos
  bound := f.bound
  bound_nonneg := f.bound_nonneg
  continuous := f.continuous.neg
  analytic a ha := (f.analytic a ha).neg
  norm_le z hz a ha := by simpa only [norm_neg] using f.norm_le z hz a ha

lemma uniform_near (f : UniformFamily S T) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, δ ≤ f.radius ∧ ∀ z ∈ thickening δ S, ∀ a ∈ T,
      ∃ w ∈ S, dist (f.val z a) (f.val w a) < η := by
  let K := f.bound/(f.radius/2)
  have hK : 0 ≤ K := div_nonneg f.bound_nonneg (by linarith [f.radius_pos])
  let δ := min (f.radius/4) (η/(K+1))
  have hd : 0 < δ := lt_min (by linarith [f.radius_pos]) (div_pos hη (by linarith))
  refine ⟨δ,hd,(min_le_left _ _).trans (by linarith [f.radius_pos]),?_⟩
  intro z hz a ha
  obtain ⟨w,hw,hzw⟩ := mem_thickening_iff.mp hz
  have hzw4 : dist z w < f.radius/4 := hzw.trans_le (min_le_left _ _)
  have hsmall : closedBall w (f.radius/4) ⊆ thickening f.radius S := by
    intro u hu
    apply mem_thickening_iff.mpr
    exact ⟨w,hw,(mem_closedBall.mp hu).trans_lt (by linarith [f.radius_pos])⟩
  have hder : ∀ u ∈ closedBall w (f.radius/4),
      ‖fderiv ℂ (fun z => f.val z a) u‖ ≤ K := by
    intro u hu
    have hsub : closedBall u (f.radius/2) ⊆ thickening f.radius S := by
      intro v hv
      apply mem_thickening_iff.mpr
      refine ⟨w,hw,?_⟩
      have hh := dist_triangle v u w
      have hv' := mem_closedBall.mp hv
      have hu' := mem_closedBall.mp hu
      linarith [f.radius_pos]
    exact norm_fderiv_le_of_closedBall (by linarith [f.radius_pos]) isOpen_thickening
      (f.analytic a ha).differentiableOn hsub
      (fun v hv => f.norm_le v (hsub hv) a ha)
  have hmean := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun u hu => (f.analytic a ha u (hsmall hu)).differentiableAt) hder
    (convex_closedBall w (f.radius/4))
    (mem_closedBall_self (by linarith [f.radius_pos])) hzw4.le
  refine ⟨w,hw,?_⟩
  have hη' : dist z w < η/(K+1) := hzw.trans_le (min_le_right _ _)
  have hm : dist z w*(K+1) < η := (lt_div_iff₀ (by linarith)).mp hη'
  have hm' : K*dist z w < η := by nlinarith [dist_nonneg (x := z) (y := w)]
  exact (show dist (f.val z a) (f.val w a) ≤ K*dist z w by
    simpa only [dist_eq_norm] using hmean).trans_lt hm'

lemma comp {D : Set ℂ} (hD : IsClosed D) (f : UniformFamily S T)
    (hf : ∀ z ∈ S, ∀ a ∈ T, f.val z a ∈ D) {φ : ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ D) :
    ∃ g : UniformFamily S T, ∀ z a, g.val z a = φ (f.val z a) := by
  let K := D ∩ closedBall (0:ℂ) f.bound
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) f.bound).inter_left hD
  let Ω := {z : ℂ | AnalyticAt ℂ φ z}
  have hΩ : IsOpen Ω := isOpen_analyticAt ℂ φ
  have hKD : K ⊆ D := inter_subset_left
  have hKΩ : K ⊆ Ω := fun z hz => hφ z hz.1
  have hφc : ContinuousOn φ Ω := fun z hz => hz.continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (hφc.mono hKΩ)
  let V := Ω ∩ φ ⁻¹' ball (0:ℂ) (|C|+1)
  have hVo : IsOpen V := hφc.isOpen_inter_preimage hΩ isOpen_ball
  have hKV : K ⊆ V := by
    intro z hz
    refine ⟨hKΩ hz,?_⟩
    change dist (φ z) 0 < |C|+1
    rw [dist_zero_right]
    linarith [hC z hz,le_abs_self C]
  obtain ⟨η,hη,hηV⟩ := hK.exists_thickening_subset_open hVo hKV
  obtain ⟨δ,hδ,hδr,hclose⟩ := f.uniform_near hη
  have hmaps : ∀ z ∈ thickening δ S, ∀ a ∈ T, f.val z a ∈ V := by
    intro z hz a ha
    obtain ⟨w,hw,hdist⟩ := hclose z hz a ha
    apply hηV
    apply mem_thickening_iff.mpr
    refine ⟨f.val w a,⟨hf w hw a ha,?_⟩,hdist⟩
    simpa only [mem_closedBall,dist_zero_right] using f.norm_le_on hw ha
  refine ⟨{
    val := fun z a => φ (f.val z a)
    radius := δ
    radius_pos := hδ
    bound := |C|+1
    bound_nonneg := by positivity
    continuous := (hφc.mono inter_subset_left).comp
      (f.continuous.mono (Set.prod_mono (thickening_mono hδr S) Subset.rfl))
      (fun p hp => hmaps p.1 hp.1 p.2 hp.2)
    analytic := fun a ha z hz => ((hmaps z hz a ha).1).comp
      (f := fun z => f.val z a) (f.analytic a ha z (thickening_mono hδr S hz))
    norm_le := fun z hz a ha => by
      have hh := (hmaps z hz a ha).2
      change dist (φ (f.val z a)) 0 < |C|+1 at hh
      exact (by simpa only [dist_zero_right] using hh.le)
  },fun _ _ => rfl⟩

def reindex {β : Type} [TopologicalSpace β] {V : Set β}
    (f : UniformFamily S T) (g : β → α) (hg : ContinuousOn g V) (hgt : MapsTo g V T) :
    UniformFamily S V where
  val z b := f.val z (g b)
  radius := f.radius
  radius_pos := f.radius_pos
  bound := f.bound
  bound_nonneg := f.bound_nonneg
  continuous := f.continuous.comp (continuous_fst.continuousOn.prodMk
    (hg.comp continuous_snd.continuousOn (fun p hp => hp.2))) (fun p hp => ⟨hp.1,hgt hp.2⟩)
  analytic b hb := f.analytic (g b) (hgt hb)
  norm_le z hz b hb := f.norm_le z hz (g b) (hgt hb)

lemma real_constant (f : UniformFamily S T) (hS : Convex ℝ S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ interior S)
    (hre : ∀ z ∈ S, ∀ a ∈ T, (f.val z a).im = 0) :
    ∀ z ∈ S, ∀ a ∈ T, f.val z a = f.val z₀ a := by
  intro z hz a ha
  have hsub : interior S ⊆ thickening f.radius S :=
    interior_subset.trans (self_subset_thickening f.radius_pos S)
  obtain ⟨c,hc⟩ := ((f.analytic a ha).mono hsub).eq_const_of_im_eq_const
    (fun z hz => hre z (interior_subset hz) a ha) isOpen_interior
    ⟨⟨z₀,hz₀⟩,hS.interior.isPreconnected⟩
  have heq : (fun z => f.val z a) =ᶠ[nhds z₀] (fun _ => c) := by
    filter_upwards [isOpen_interior.mem_nhds hz₀] with w hw
    exact hc w hw
  have he := (f.analytic a ha).eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const (hS.thickening f.radius).isPreconnected (hsub hz₀) heq
  exact (he (self_subset_thickening f.radius_pos S hz)).trans (hc z₀ hz₀).symm

noncomputable def integralSet [FirstCountableTopology α]
    {J : Set ℝ} (hJ : MeasurableSet J) (f : UniformFamily S (T ×ˢ J))
    (k : ℝ → ℂ) (hk : IntegrableOn k J) : UniformFamily S T := by
  let U := thickening f.radius S
  let F : (ℂ × α) → ℝ → ℂ := fun p t => k t * f.val p.1 (p.2,t)
  let B : ℝ → ℝ := fun t => ‖k t‖*f.bound
  have hB : IntegrableOn B J := hk.norm.mul_const f.bound
  have hslice : ∀ p ∈ U ×ˢ T, AEStronglyMeasurable (F p) (volume.restrict J) := by
    intro p hp
    have hf : ContinuousOn (fun t => f.val p.1 (p.2,t)) J :=
      f.continuous.comp ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn)
        (fun t ht => ⟨hp.1,hp.2,ht⟩)
    exact hk.aestronglyMeasurable.mul (hf.aestronglyMeasurable hJ)
  have hbound : ∀ p ∈ U ×ˢ T, ∀ t ∈ J, ‖F p t‖ ≤ B t := by
    intro p hp t ht
    dsimp only [F,B]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (f.norm_le p.1 hp.1 (p.2,t) ⟨hp.2,ht⟩) (norm_nonneg _)
  have hFcont : ∀ t ∈ J, ContinuousOn (fun p => F p t) (U ×ˢ T) := by
    intro t ht
    apply continuousOn_const.mul
    exact f.continuous.comp ((continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn)
      (fun p hp => ⟨hp.1,hp.2,ht⟩)
  refine {
    val := fun z a => ∫ t in J, F (z,a) t
    radius := f.radius
    radius_pos := f.radius_pos
    bound := (∫ t in J, ‖k t‖)*f.bound
    bound_nonneg := mul_nonneg (integral_nonneg (fun _ => norm_nonneg _)) f.bound_nonneg
    continuous := ?_
    analytic := ?_
    norm_le := ?_
  }
  · exact continuousOn_of_dominated hslice
      (fun p hp => ae_restrict_of_forall_mem hJ (fun t ht => hbound p hp t ht)) hB
      (ae_restrict_of_forall_mem hJ (fun t ht => hFcont t ht))
  · intro a ha
    exact (analytic_setIntegral_of_integrable_envelope isOpen_thickening hJ
      (fun t ht => analyticOnNhd_const.mul (f.analytic (a,t) ⟨ha,ht⟩))
      (fun z hz => hslice (z,a) ⟨hz,ha⟩) hB
      (fun z hz t ht => hbound (z,a) ⟨hz,ha⟩ t ht)).1
  · intro z hz a ha
    have hh := norm_integral_le_of_norm_le hB
      (ae_restrict_of_forall_mem hJ (fun t ht => hbound (z,a) ⟨hz,ha⟩ t ht))
    simpa only [B,integral_mul_const] using hh

lemma integralSet_val [FirstCountableTopology α]
    {J : Set ℝ} (hJ : MeasurableSet J) (f : UniformFamily S (T ×ˢ J))
    (k : ℝ → ℂ) (hk : IntegrableOn k J) (z : ℂ) (a : α) :
    (integralSet hJ f k hk).val z a = ∫ t in J, k t*f.val z (a,t) := rfl

end UniformFamily
end Lynth.Interval.Integral.Nested.AnalyticWork
