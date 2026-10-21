import Mathlib

/-!
P2: proof-producing divergence, entirely standalone.
No quadrature timeout or non-finite enclosure is evidence of divergence.
Basic reciprocal cases already have Mathlib lemmas; these comparisons
cover products and changes of variables without hard-coded integral values.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Intgrl

theorem not_integrable_endpoint_of_inv_lower {f : ℝ → ℝ} {b C : ℝ}
    (hb : 0 < b) (hC : 0 < C)
    (hbound : ∀ t ∈ Set.Ioo 0 b, C / t ≤ |f t|) :
    ¬ IntegrableOn f (Set.Ioo 0 b) volume := by
  intro hf
  have h1 : IntegrableOn (fun t : ℝ => C / t) (Set.Ioo 0 b) volume := by
    refine Integrable.mono' hf.norm ?_ ?_
    · exact (continuousOn_const.div continuousOn_id
        (fun t ht => ht.1.ne')).aestronglyMeasurable measurableSet_Ioo
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (div_pos hC ht.1)]
      simpa [Real.norm_eq_abs] using hbound t ht
  have h2 : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioo 0 b) volume := by
    have := h1.const_mul C⁻¹
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioo
    field_simp
  have h3 : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 0 b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hb.le]
    exact h2
  rw [intervalIntegrable_inv_iff] at h3
  rcases h3 with h3 | h3
  · exact hb.ne h3
  · exact h3 (Set.left_mem_uIcc)

theorem not_integrable_tail_of_inv_lower {f : ℝ → ℝ} {R C : ℝ}
    (hR : 0 < R) (hC : 0 < C)
    (hbound : ∀ t ∈ Set.Ioi R, C / t ≤ |f t|) :
    ¬ IntegrableOn f (Set.Ioi R) volume := by
  intro hf
  have h1 : IntegrableOn (fun t : ℝ => C / t) (Set.Ioi R) volume := by
    refine Integrable.mono' hf.norm ?_ ?_
    · exact (continuousOn_const.div continuousOn_id
        (fun t ht => (hR.trans ht).ne')).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (div_pos hC (hR.trans ht))]
      simpa [Real.norm_eq_abs] using hbound t ht
  have h2 : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioi R) volume := by
    have := h1.const_mul C⁻¹
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
    field_simp
  exact not_integrableOn_Ioi_inv h2

theorem not_intervalIntegrable_tan :
    ¬ IntervalIntegrable Real.tan volume 0 (Real.pi / 2) := by
  set c : ℝ := Real.pi / 2
  have hcos : Tendsto Real.cos (𝓝[≠] c) (𝓝[≠] 0) := by
    have := (Real.hasDerivAt_cos c).tendsto_nhdsNE (by simp [c])
    simpa [c] using this
  have hne : ∀ᶠ x in 𝓝[≠] c, Real.cos x ≠ 0 :=
    hcos.eventually (self_mem_nhdsWithin)
  have A : ∀ᶠ x in 𝓝[≠] c,
      HasDerivAt (fun x => Real.log (Real.cos x)) (-Real.tan x) x := by
    filter_upwards [hne] with x hx
    have := (Real.hasDerivAt_cos x).log hx
    convert this using 1
    rw [Real.tan_eq_sin_div_cos]
    ring
  have B : Tendsto (fun x => ‖Real.log (Real.cos x)‖) (𝓝[≠] c) atTop :=
    tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsNE_zero.comp hcos)
  have hderiv : deriv (fun x => Real.log (Real.cos x)) =O[𝓝[≠] c] Real.tan := by
    have h1 : deriv (fun x => Real.log (Real.cos x)) =ᶠ[𝓝[≠] c] fun x => -Real.tan x :=
      A.mono fun x hx => hx.deriv
    exact (Asymptotics.isBigO_refl Real.tan _).neg_left.congr' h1.symm
      (EventuallyEq.refl _ _)
  exact not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured
    (A.mono fun x hx => hx.differentiableAt) B hderiv
    (by positivity) (Set.right_mem_uIcc)

/-- A positive integral of the norm on every period rules out absolute integrability. -/
theorem not_integrable_periodic_tail {f : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T) (hperiodic : Function.Periodic f T)
    (hint : IntervalIntegrable f volume 0 T)
    (hpositive : 0 < ∫ t in (0 : ℝ)..T, |f t|) (R : ℝ) :
    ¬ IntegrableOn f (Set.Ioi R) volume := by
  have _hint := hint
  intro hf
  set c := ∫ t in (0 : ℝ)..T, |f t|
  have habs : Function.Periodic (fun t => |f t|) T := fun t => by simp [hperiodic t]
  have hfa : IntegrableOn (fun t => |f t|) (Set.Ioi R) volume := hf.abs
  have hII : ∀ u v, R ≤ u → u ≤ v → IntervalIntegrable (fun t => |f t|) volume u v := by
    intro u v hu huv
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le huv]
    exact hfa.mono_set fun t ht => lt_of_le_of_lt hu ht.1
  have hsum : ∀ N : ℕ, ∫ t in R..R + N * T, |f t| = N * c := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hNT : 0 ≤ (N : ℝ) * T := by positivity
      have h1 : IntervalIntegrable (fun t => |f t|) volume R (R + N * T) := hII _ _ le_rfl (by linarith)
      have h2 : IntervalIntegrable (fun t => |f t|) volume (R + N * T) (R + N * T + T) :=
        hII _ _ (by linarith) (by linarith)
      rw [show R + ((N + 1 : ℕ) : ℝ) * T = R + N * T + T by push_cast; ring,
        ← intervalIntegral.integral_add_adjacent_intervals h1 h2, ih,
        habs.intervalIntegral_add_eq (R + N * T) 0, zero_add]
      push_cast; ring
  have hle : ∀ N : ℕ, (N : ℝ) * c ≤ ∫ t in Set.Ioi R, |f t| := by
    intro N
    rw [← hsum N, intervalIntegral.integral_of_le (by have := N.cast_nonneg (α := ℝ); nlinarith)]
    exact setIntegral_mono_set hfa (Eventually.of_forall fun t => abs_nonneg _)
      (Set.Ioc_subset_Ioi_self).eventuallyLE
  obtain ⟨N, hN⟩ := exists_nat_gt ((∫ t in Set.Ioi R, |f t|) / c)
  have := hle N
  rw [div_lt_iff₀ hpositive] at hN
  linarith

end Intgrl
