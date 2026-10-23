module

import all Lynth.Interval.Integral.Math.NestedEnvelope

/-! Analytic parameter integrals with integrable envelopes and measurable slices. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Intgrl
theorem aestronglyMeasurable_fderiv_of_slices
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] {μ : Measure ℝ}
    {h : ℝ → E → G} {z : E} {r : ℝ} (hr : 0 < r)
    (hd : ∀ᵐ t ∂μ, DifferentiableAt ℂ (h t) z)
    (hm : ∀ w ∈ Metric.ball z r, AEStronglyMeasurable (fun t => h t w) μ) :
    AEStronglyMeasurable (fun t => fderiv ℂ (h t) z) μ := by
  classical
  set b := Module.finBasis ℂ E
  let ι := Fin (Module.finrank ℂ E)
  let c : ι → E →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hΦ : ∀ L : E →L[ℂ] G, ∑ i, (c i).smulRight (L (b i)) = L := by
    intro L
    ext v
    simp only [c, FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    calc _ = L (∑ i, b.repr v i • b i) := by rw [map_sum]; simp only [map_smul]; rfl
      _ = L v := by rw [b.sum_repr]
  set K : ℝ := ∑ i, ‖b i‖ + 1
  have hK : 0 < K := by positivity
  set ε : ℝ := r / (2 * K)
  have hε : 0 < ε := by positivity
  let δ : ℕ → ℂ := fun k => ((ε / (k + 1) : ℝ) : ℂ)
  have hδ0 : ∀ k, δ k ≠ 0 := fun k => by
    simp only [δ, ne_eq, Complex.ofReal_eq_zero]; positivity
  have hδlim : Tendsto δ atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hδ0⟩
    have h1 : Tendsto (fun k : ℕ => ((ε * (1 / ((k:ℝ) + 1)) : ℝ) : ℂ)) atTop
        (𝓝 ((ε * 0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε)
    simp only [mul_zero, Complex.ofReal_zero] at h1
    convert h1 using 2 with k
    simp [δ, div_eq_mul_inv]
  have hmem : ∀ k i, z + δ k • b i ∈ Metric.ball z r := by
    intro k i
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have h1 : ‖δ k‖ ≤ ε := by
      show ‖((ε / (k + 1) : ℝ) : ℂ)‖ ≤ ε
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_le_self hε.le (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
    have h2 : ‖b i‖ ≤ K := by
      have := Finset.single_le_sum (f := fun j => ‖b j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ i)
      linarith
    calc ‖δ k‖ * ‖b i‖ ≤ ε * K := by gcongr
      _ = r / 2 := by simp only [ε]; field_simp
      _ < r := by linarith
  let A : ℕ → ℝ → E →L[ℂ] G := fun k t =>
    ∑ i, (c i).smulRight ((δ k)⁻¹ • (h t (z + δ k • b i) - h t z))
  refine aestronglyMeasurable_of_tendsto_ae (f := A) atTop (fun k => ?_) ?_
  · refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    refine (ContinuousLinearMap.smulRightL ℂ E G (c i)).continuous.comp_aestronglyMeasurable ?_
    exact ((hm _ (hmem k i)).sub (hm z (Metric.mem_ball_self hr))).const_smul _
  · filter_upwards [hd] with t ht
    rw [← hΦ (fderiv ℂ (h t) z)]
    refine tendsto_finsetSum _ fun i _ => ?_
    refine ((ContinuousLinearMap.smulRightL ℂ E G (c i)).continuous.tendsto _).comp ?_
    have hder : HasDerivAt (fun s : ℂ => h t (z + s • b i)) (fderiv ℂ (h t) z (b i)) 0 := by
      have h1 : HasDerivAt (fun s : ℂ => z + s • b i) (b i) 0 := by
        simpa using ((hasDerivAt_id (0:ℂ)).smul_const (b i)).const_add z
      have ht' : HasFDerivAt (h t) (fderiv ℂ (h t) z) (z + (0:ℂ) • b i) := by
        simpa using ht.hasFDerivAt
      exact ht'.comp_hasDerivAt (0:ℂ) h1
    have := (hasDerivAt_iff_tendsto_slope.1 hder).comp hδlim
    refine this.congr fun k => ?_
    simp [Function.comp, slope_def_module]

/-- Iterated parameter derivatives of analytic slices are measurable in the
real variable. -/
theorem aestronglyMeasurable_iteratedFDeriv_of_slices
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) {F : E → ℝ → ℂ} {S : Set ℝ} (hS : MeasurableSet S)
    (hF : ∀ t ∈ S, AnalyticOnNhd ℂ (fun z => F z t) U)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) (volume.restrict S)) (n : ℕ) :
    ∀ z ∈ U, AEStronglyMeasurable
      (fun t => iteratedFDeriv ℂ n (fun z => F z t) z) (volume.restrict S) := by
  induction n with
  | zero =>
    intro z hz
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 ℂ E ℂ).symm.continuous.comp_aestronglyMeasurable
      (hmeas z hz)
  | succ n ih =>
    intro z hz
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    refine (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (n + 1) => E) ℂ).symm.continuous
      |>.comp_aestronglyMeasurable ?_
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z hz
    refine aestronglyMeasurable_fderiv_of_slices hr ?_ (fun w hw => ih w (hrU hw))
    rw [ae_restrict_iff' hS]
    exact Eventually.of_forall fun t ht =>
      ((hF t ht).iteratedFDeriv n z hz).differentiableAt

/-- New analytic core for endpoint envelopes: holomorphic parameter slices,
measurable real slices, and one integrable bound valid throughout U imply an
analytic integral. Finite dimensional parameter spaces include every finite
collection of outer bound variables used by the nested evaluator. -/
theorem analytic_setIntegral_of_integrable_envelope
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) {F : E → ℝ → ℂ} {g : ℝ → ℝ}
    {S : Set ℝ} (hS : MeasurableSet S)
    (hF : ∀ t ∈ S, AnalyticOnNhd ℂ (fun z => F z t) U)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) (volume.restrict S))
    (hg : IntegrableOn g S)
    (hbound : ∀ z ∈ U, ∀ t ∈ S, ‖F z t‖ ≤ g t) :
    AnalyticOnNhd ℂ (fun z => ∫ t in S, F z t) U ∧
      ∀ z ∈ U, IntegrableOn (F z) S := by
  refine ⟨?_,?_⟩
  · intro z0 hz0
    obtain ⟨R,hR,hRU⟩ := Metric.isOpen_iff.1 hU z0 hz0
    exact analyticAt_setIntegral_of_bound (f := F) (z0 := z0) (R := R)
      hS hg hR (fun t ht => (hF t ht).mono hRU)
      (fun t ht z hz => hbound z (hRU hz) t ht)
      (fun n => aestronglyMeasurable_iteratedFDeriv_of_slices hU hS hF hmeas n z0 hz0)
  · intro z hz
    refine Integrable.mono' hg (hmeas z hz) ?_
    exact (ae_restrict_iff' hS).mpr (Eventually.of_forall fun t ht => hbound z hz t ht)

end Intgrl
