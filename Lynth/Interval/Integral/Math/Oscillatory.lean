module

import Mathlib

/-! Cancellation bounds near a reciprocal-phase endpoint. This theorem is
independent of the interval implementation and is mirrored in /tmp/intgrl. -/

namespace Intgrl

/-- Substitution followed by integration by parts gains one power of the
endpoint compared with the pointwise bound. The value at zero is immaterial. -/
theorem reciprocal_sin_endpoint (n : ℕ) {ω δ : ℝ} (hω : ω ≠ 0) (hδ : 0 ≤ δ) :
    IntervalIntegrable (fun x : ℝ => x^n * Real.sin (ω/x))
      MeasureTheory.volume 0 δ ∧
      |(∫ x in (0 : ℝ)..δ, x^n * Real.sin (ω/x))| ≤ 2*δ^(n+2)/|ω| := by
  have hωa : 0 < |ω| := abs_pos.2 hω
  have bdd : ∀ g : ℝ → ℝ, ∀ M : ℝ, Measurable g → (∀ x ∈ Set.Icc 0 δ, |g x| ≤ M) →
      IntervalIntegrable g MeasureTheory.volume 0 δ := by
    intro g M hg hb
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hδ]
    refine MeasureTheory.Measure.integrableOn_of_bounded (M := M) ?_ hg.aestronglyMeasurable ?_
    · simp [Real.volume_Icc]
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall fun x hx => by rw [Real.norm_eq_abs]; exact hb x hx
  set g : ℝ → ℝ := fun x => x^n * Real.sin (ω/x) with hg
  set h : ℝ → ℝ := fun x => (n+2) * x^(n+1) * Real.cos (ω/x) / ω with hh
  set F : ℝ → ℝ := fun x => x^(n+2) * Real.cos (ω/x) / ω with hF
  have hgi : IntervalIntegrable g MeasureTheory.volume 0 δ := by
    apply bdd g (δ^n) (by fun_prop)
    intro x hx
    calc |g x| = |x|^n * |Real.sin (ω/x)| := by simp [g, abs_mul, abs_pow]
      _ ≤ δ^n * 1 := by
        gcongr
        · rw [abs_of_nonneg hx.1]; exact hx.2
        · exact Real.abs_sin_le_one _
      _ = _ := mul_one _
  have hhabs : ∀ x ∈ Set.Icc 0 δ, |h x| ≤ (n+2) * x^(n+1) / |ω| := by
    intro x hx
    calc |h x| = (n+2) * x^(n+1) * |Real.cos (ω/x)| / |ω| := by
          simp only [h, abs_div, abs_mul, abs_pow, abs_of_nonneg hx.1,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ n+2)]
      _ ≤ (n+2) * x^(n+1) * 1 / |ω| := by
          have := hx.1
          gcongr; exact Real.abs_cos_le_one _
      _ = _ := by ring
  have hhi : IntervalIntegrable h MeasureTheory.volume 0 δ := by
    apply bdd h ((n+2) * δ^(n+1) / |ω|) (by fun_prop)
    intro x hx
    refine (hhabs x hx).trans ?_
    have := hx.1
    gcongr; exact hx.2
  have hFcont : ContinuousOn F (Set.Icc 0 δ) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h0 | h0
    · subst h0
      apply ContinuousAt.continuousWithinAt
      rw [ContinuousAt]
      have hF0 : F 0 = 0 := by simp [F]
      rw [hF0]
      have hb : ∀ y, |F y| ≤ |y|^(n+2) / |ω| := by
        intro y; simp only [F, abs_div, abs_mul, abs_pow]
        gcongr
        calc |y|^(n+2) * |Real.cos (ω/y)| ≤ |y|^(n+2) * 1 := by
              gcongr; exact Real.abs_cos_le_one _
          _ = _ := mul_one _
      have ht : Filter.Tendsto (fun y : ℝ => |y|^(n+2) / |ω|) (nhds 0) (nhds 0) := by
        have : Continuous (fun y : ℝ => |y|^(n+2) / |ω|) := by fun_prop
        simpa using this.tendsto 0
      exact squeeze_zero_norm (fun y => by rw [Real.norm_eq_abs]; exact hb y) ht
    · apply ContinuousAt.continuousWithinAt
      have : x ≠ 0 := h0.ne'
      fun_prop (disch := assumption)
  have hderiv : ∀ x ∈ Set.Ioo 0 δ, HasDerivAt F (h x + g x) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h1 : HasDerivAt (fun x => ω / x) (-(ω) / x^2) x := by
      have := (hasDerivAt_inv hx0).const_mul ω
      convert this using 1
      · ext y; simp [div_eq_mul_inv]
      · field_simp
    have h2 := ((hasDerivAt_pow (n+2) x).mul (h1.cos)).div_const ω
    convert h2 using 1
    simp only [h, g]
    field_simp
    push_cast
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδ hFcont hderiv
    (hhi.add hgi)
  rw [intervalIntegral.integral_add hhi hgi] at hFTC
  have hF0 : F 0 = 0 := by simp [F]
  rw [hF0, sub_zero] at hFTC
  refine ⟨hgi, ?_⟩
  have hgeq : (∫ x in (0:ℝ)..δ, g x) = F δ - ∫ x in (0:ℝ)..δ, h x := by linarith
  change |∫ x in (0:ℝ)..δ, g x| ≤ _
  rw [hgeq]
  have hFd : |F δ| ≤ δ^(n+2) / |ω| := by
    simp only [F, abs_div, abs_mul, abs_pow, abs_of_nonneg hδ]
    gcongr
    calc δ^(n+2) * |Real.cos (ω/δ)| ≤ δ^(n+2) * 1 := by
          gcongr; exact Real.abs_cos_le_one _
      _ = _ := mul_one _
  have hhint : |∫ x in (0:ℝ)..δ, h x| ≤ δ^(n+2) / |ω| := by
    refine (intervalIntegral.abs_integral_le_integral_abs hδ).trans ?_
    have hm : (∫ x in (0:ℝ)..δ, |h x|) ≤ ∫ x in (0:ℝ)..δ, (n+2) * x^(n+1) / |ω| := by
      apply intervalIntegral.integral_mono_on hδ hhi.abs
      · exact (by fun_prop : Continuous fun x : ℝ => (n+2) * x^(n+1) / |ω|).intervalIntegrable _ _
      · exact hhabs
    refine hm.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    field_simp
    push_cast; ring
  calc |F δ - ∫ x in (0:ℝ)..δ, h x| ≤ |F δ| + |∫ x in (0:ℝ)..δ, h x| := abs_sub _ _
    _ ≤ δ^(n+2) / |ω| + δ^(n+2) / |ω| := add_le_add hFd hhint
    _ = _ := by ring

end Intgrl
