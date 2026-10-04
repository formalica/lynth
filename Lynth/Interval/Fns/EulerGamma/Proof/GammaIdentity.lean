import Lynth.Interval.Fns.EulerGamma.Proof.PowerSeries
import Lynth.Interval.Fns.EulerGamma.Proof.BesselK0Limit

/-!
# The Brent–McMillan identity `γ = S(x)/I(x) - log x - K0(x)/I(x)`
-/

open Real MeasureTheory Set Filter Topology

namespace BM

lemma eq_of_deriv_zero_of_tendsto {f : ℝ → ℝ} {L : ℝ} (h : ∀ x : ℝ, 0 < x → HasDerivAt f 0 x)
    (hl : Tendsto f (𝓝[>] 0) (𝓝 L)) : ∀ x : ℝ, 0 < x → f x = L := by
  obtain ⟨c, hc⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero (isPreconnected_Ioi)
    (fun x hx => (h x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (h x hx).deriv)
  have h2 : Tendsto f (𝓝[>] 0) (𝓝 c) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall (fun x hx => (hc x hx).symm))
  have := tendsto_nhds_unique hl h2
  intro x hx; rw [hc x hx, this]

lemma II_pos (x : ℝ) : 0 < II x := by
  rw [II_eq]; exact bmB_pos _ (sq_nonneg x)

/-- `D(x) = I'(x)` -/
noncomputable def DI (x : ℝ) : ℝ := 2 * x * PS (dco bco) (x ^ 2)

lemma continuous_DI : Continuous DI := by
  have : ∀ x, HasDerivAt (fun x => PS (dco bco) (x ^ 2)) _ x :=
    fun x => hasDerivAt_comp_sq entire_bco.dco x
  have hc : Continuous (fun x => PS (dco bco) (x ^ 2)) :=
    continuous_iff_continuousAt.mpr (fun x => (this x).continuousAt)
  unfold DI; fun_prop

lemma tendsto_x_mul_K0 : Tendsto (fun x => x * K0 x) (𝓝[>] 0) (𝓝 0) := by
  have h1 := tendsto_K0_add_log
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds |>.congr (fun _ => rfl)
  have hxlog : Tendsto (fun x : ℝ => x * Real.log x) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have := (hid.mul h1).sub hxlog
  simp only [zero_mul, sub_zero] at this
  refine this.congr (fun x => ?_)
  ring

/-- the Wronskian `x (I K0' - I' K0) = -1`, written as `L I + x I' K0 = 1` -/
lemma wronskian (x : ℝ) (hx : 0 < x) : LL x * II x + I1 x * K0 x = 1 := by
  set W := fun x => LL x * II x + I1 x * K0 x
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt W 0 x := by
    intro x hx
    have := ((hasDerivAt_LL hx).mul (hasDerivAt_II x)).add
      ((hasDerivAt_I1 x).mul (hasDerivAt_K0 hx))
    convert this using 1
    rw [I1_eq]; field_simp; ring
  have hl : Tendsto W (𝓝[>] 0) (𝓝 1) := by
    have hII : Tendsto II (𝓝[>] 0) (𝓝 1) := by
      have : ContinuousAt II 0 := (hasDerivAt_II 0).continuousAt
      have := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      rwa [II_zero] at this
    have hD : Tendsto DI (𝓝[>] 0) (𝓝 0) := by
      have := (continuous_DI.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa [DI] using this
    have h2 := (tendsto_LL.mul hII).add (hD.mul tendsto_x_mul_K0)
    simp only [mul_one, mul_zero, add_zero] at h2
    refine h2.congr (fun x => ?_)
    simp only [W, I1_eq, DI]; ring
  exact eq_of_deriv_zero_of_tendsto hd hl x hx

theorem gamma_identity (x : ℝ) (hx : 0 < x) :
    eulerMascheroniConstant = bmA (x ^ 2) / bmB (x ^ 2) - log x - K0 x / bmB (x ^ 2) := by
  rw [← II_eq, ← SS_eq]
  set Φ := fun x => SS x / II x - Real.log x - K0 x / II x
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt Φ 0 x := by
    intro x hx
    have hI := II_pos x
    have := (((hasDerivAt_SS x).div (hasDerivAt_II x) hI.ne').sub (Real.hasDerivAt_log hx.ne')).sub
      ((hasDerivAt_K0 hx).div (hasDerivAt_II x) hI.ne')
    convert this using 1
    have hW := wronskian x hx
    have hS := S1_II_sub x
    rw [S1_eq, I1_eq] at hS
    rw [I1_eq] at hW
    field_simp
    linear_combination -hW - hS
  have hl : Tendsto Φ (𝓝[>] 0) (𝓝 eulerMascheroniConstant) := by
    have hII : Tendsto II (𝓝[>] 0) (𝓝 1) := by
      have : ContinuousAt II 0 := (hasDerivAt_II 0).continuousAt
      have := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      rwa [II_zero] at this
    have hSS : Tendsto SS (𝓝[>] 0) (𝓝 0) := by
      have : ContinuousAt SS 0 := (hasDerivAt_SS 0).continuousAt
      have := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      rwa [SS_zero] at this
    -- `(I(x) - 1) log x → 0`
    have hslope : Tendsto (fun x => (II x - 1) / x) (𝓝[>] 0) (𝓝 0) := by
      have h := (hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_II 0)).mono_left
        (nhdsWithin_mono _ (fun x (hx : 0 < x) => (ne_of_gt hx : x ≠ 0)))
      simp only [mul_zero, zero_mul] at h
      exact h.congr (fun x => by rw [slope_def_field, II_zero, sub_zero])
    have hxlog : Tendsto (fun x : ℝ => x * Real.log x) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    have hIlog : Tendsto (fun x => (II x - 1) * Real.log x) (𝓝[>] 0) (𝓝 0) := by
      have := hslope.mul hxlog
      rw [zero_mul] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : (x:ℝ) ≠ 0 := ne_of_gt hx
      field_simp
    have h := ((hSS.sub tendsto_K0_add_log).sub hIlog).div hII one_ne_zero
    simp only [zero_sub, neg_neg, sub_zero, div_one] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hI := (II_pos x).ne'
    simp only [Φ, Pi.div_apply]
    field_simp
    ring
  have := eq_of_deriv_zero_of_tendsto hd hl x hx
  simp only [Φ] at this
  rw [← this]

end BM
