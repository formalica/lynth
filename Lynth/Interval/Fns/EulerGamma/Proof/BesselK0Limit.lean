import Lynth.Interval.Fns.EulerGamma.Proof.BesselK0

/-!
# The limit `K0 x + log x → -γ` as `x → 0⁺`
-/

open Real MeasureTheory Set Filter Topology

namespace BM

lemma integral_exp_neg_mul_log :
    ∫ t in Ioi (0:ℝ), Real.log t * exp (-t) = -eulerMascheroniConstant := by
  have h1 := Complex.hasDerivAt_GammaIntegral (s := 1) (by simp)
  have h2 : HasDerivAt Complex.GammaIntegral (-(eulerMascheroniConstant : ℂ)) 1 := by
    refine Complex.hasDerivAt_Gamma_one.congr_of_eventuallyEq ?_
    have : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [this] with s hs
    exact (Complex.Gamma_eq_integral hs).symm
  have h := h1.unique h2
  simp only [sub_self, Complex.cpow_zero, one_mul] at h
  simp_rw [← Complex.ofReal_mul] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun t => Real.log t * exp (-t)) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_exp_neg_mul_log]
  have := Real.one_half_lt_eulerMascheroniConstant
  intro h; linarith

/-- `E(x) = ∫_0^∞ exp(-x e^v) dv` -/
noncomputable def EE (x : ℝ) : ℝ := ∫ v in Ioi 0, exp (-(x * exp v))

lemma integrableOn_EE {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun v => exp (-(x * exp v))) (Ioi 0) := by
  refine (exp_neg_integrableOn_Ioi 0 hx).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun v => exp (-(x * exp v))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (fun v hv => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := Real.add_one_le_exp v
    nlinarith

lemma K0_sub_EE {x : ℝ} (hx : 0 < x) : |K0 x - EE x| ≤ x := by
  have hK := (Kf_integrable 0 hx)
  simp only [pow_zero, one_mul] at hK
  have hE := integrableOn_EE hx
  rw [K0, EE, ← integral_sub hK hE]
  have hneg : ∫ v in Ioi 0, exp (-(2 * x * cosh v)) - exp (-(x * exp v))
      = -∫ v in Ioi 0, exp (-(x * exp v)) - exp (-(2 * x * cosh v)) := by
    rw [← integral_neg]; congr 1; ext v; ring
  rw [hneg, abs_neg]
  have hpt : ∀ v ∈ Ioi (0:ℝ), 0 ≤ exp (-(x * exp v)) - exp (-(2 * x * cosh v)) ∧
      exp (-(x * exp v)) - exp (-(2 * x * cosh v)) ≤ x * exp (-1 * v) := by
    intro v _
    have hc : 2 * x * cosh v = x * exp v + x * exp (-v) := by rw [Real.cosh_eq]; ring
    rw [hc, neg_add, Real.exp_add]
    have h1 : exp (-(x * exp (-v))) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := Real.exp_pos (-v); nlinarith
    have h2 : 1 - x * exp (-v) ≤ exp (-(x * exp (-v))) := by
      have := Real.add_one_le_exp (-(x * exp (-v))); linarith
    have h3 : exp (-(x * exp v)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := Real.exp_pos v; nlinarith
    have h4 := Real.exp_pos (-(x * exp v))
    rw [neg_one_mul]
    constructor
    · nlinarith
    · have : 0 ≤ x * exp (-v) := by positivity
      nlinarith
  have h0 : 0 ≤ ∫ v in Ioi 0, exp (-(x * exp v)) - exp (-(2 * x * cosh v)) :=
    setIntegral_nonneg measurableSet_Ioi (fun v hv => (hpt v hv).1)
  rw [abs_of_nonneg h0]
  calc ∫ v in Ioi 0, exp (-(x * exp v)) - exp (-(2 * x * cosh v))
      ≤ ∫ v in Ioi 0, x * exp (-1 * v) :=
        setIntegral_mono_on (hE.sub hK) ((exp_neg_integrableOn_Ioi 0 (by norm_num)).const_mul x)
          measurableSet_Ioi (fun v hv => (hpt v hv).2)
    _ = x := by
        simp_rw [neg_one_mul]
        rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

lemma EE_eq {x : ℝ} (hx : 0 < x) : EE x = ∫ u in Ioi x, exp (-u) / u := by
  have himg : (fun v => x * exp v) '' Ioi 0 = Ioi x := by
    ext u
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have := Real.one_lt_exp_iff.mpr hv
      nlinarith
    · intro hu
      refine ⟨Real.log (u / x), Real.log_pos ((one_lt_div hx).mpr hu), ?_⟩
      rw [Real.exp_log (div_pos (by linarith) hx)]; field_simp
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (f' := fun v => x * exp v)
    (fun v _ => ((Real.hasDerivAt_exp v).const_mul x).hasDerivWithinAt)
    (fun a _ b _ h => by simpa [hx.ne'] using h)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
  simp only [smul_eq_mul]
  rw [abs_of_pos (by positivity)]
  field_simp

lemma EE_ibp {x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi x, exp (-u) / u = -(exp (-x) * Real.log x) + ∫ u in Ioi x, Real.log u * exp (-u) := by
  have hu : ∀ t ∈ Ioi x, HasDerivAt (fun t => exp (-t)) (-exp (-t)) t := by
    intro t _
    have := (hasDerivAt_neg t).exp
    convert this using 1; ring
  have hv : ∀ t ∈ Ioi x, HasDerivAt Real.log t⁻¹ t := by
    intro t ht
    exact Real.hasDerivAt_log (by have : x < t := ht; linarith)
  have huv' : IntegrableOn ((fun t => exp (-t)) * fun t => t⁻¹) (Ioi x) := by
    refine ((exp_neg_integrableOn_Ioi x (by norm_num : (0:ℝ) < 1)).const_mul x⁻¹).mono' ?_ ?_
    · exact ((by fun_prop : Continuous fun t => exp (-t)).continuousOn.mul
        (continuousOn_inv₀.mono (fun t (ht : x < t) =>
          mem_compl_singleton_iff.mpr (by linarith : (0:ℝ) < t).ne'))).aestronglyMeasurable
          measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (fun t ht => ?_))
      have ht' : x < t := ht
      have ht0 : 0 < t := by linarith
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc exp (-t) * t⁻¹ ≤ exp (-t) * x⁻¹ := by gcongr
        _ = x⁻¹ * exp (-1 * t) := by rw [neg_one_mul, mul_comm]
  have hu'v : IntegrableOn ((fun t => -exp (-t)) * Real.log) (Ioi x) := by
    have := (integrableOn_log_mul_exp_neg.mono_set (Ioi_subset_Ioi hx.le)).neg
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, Pi.neg_apply]; ring
  have h0 : Tendsto ((fun t => exp (-t)) * Real.log) (𝓝[>] x) (𝓝 (exp (-x) * Real.log x)) := by
    have : ContinuousAt ((fun t => exp (-t)) * Real.log) x :=
      ((by fun_prop : Continuous fun t => exp (-t)).continuousAt).mul
        (Real.continuousAt_log hx.ne')
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto ((fun t => exp (-t)) * Real.log) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    refine squeeze_zero' ?_ ?_ h
    · filter_upwards [eventually_ge_atTop 1] with t ht
      simp only [Pi.mul_apply]
      have := Real.log_nonneg ht
      positivity
    · filter_upwards [eventually_ge_atTop 1] with t ht
      simp only [Pi.mul_apply, pow_one]
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < t)
      have := Real.exp_pos (-t)
      nlinarith
  have := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  simp only [div_eq_mul_inv]
  rw [this]
  have e : ∫ t in Ioi x, -exp (-t) * Real.log t = -∫ t in Ioi x, Real.log t * exp (-t) := by
    rw [← integral_neg]; congr 1; ext t; ring
  rw [e]; ring

lemma tendsto_setIntegral_Ioi_log :
    Tendsto (fun x => ∫ u in Ioi x, Real.log u * exp (-u)) (𝓝[>] 0)
      (𝓝 (-eulerMascheroniConstant)) := by
  set f := fun u : ℝ => Real.log u * exp (-u)
  have hf := integrableOn_log_mul_exp_neg
  have hII : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (hf.mono_set Ioc_subset_Ioi_self)
  have hcont := intervalIntegral.continuousOn_primitive_interval' hII
    (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 1)
  have hc0 : ContinuousWithinAt (fun b => ∫ u in (0:ℝ)..b, f u) (Icc 0 1) 0 := by
    have := hcont 0 (left_mem_uIcc)
    rwa [uIcc_of_le zero_le_one] at this
  have hG : Tendsto (fun b => ∫ u in (0:ℝ)..b, f u) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun b => ∫ u in (0:ℝ)..b, f u) (𝓝[Icc 0 1] 0) (𝓝 0) := by
      have := hc0.tendsto; simpa using this
    refine h1.mono_left ?_
    have : Icc (0:ℝ) 1 ∈ 𝓝[>] 0 := by
      apply mem_nhdsWithin.mpr
      refine ⟨Iio 1, isOpen_Iio, by norm_num, fun x hx => ⟨le_of_lt hx.2, le_of_lt hx.1⟩⟩
    exact nhdsWithin_le_iff.mpr this
  have heq : ∀ᶠ x in 𝓝[>] (0:ℝ), ∫ u in Ioi x, f u
      = (-eulerMascheroniConstant) - ∫ u in (0:ℝ)..x, f u := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0:ℝ) ≤ x := le_of_lt hx
    rw [← integral_exp_neg_mul_log, intervalIntegral.integral_of_le hx',
      ← Ioc_union_Ioi_eq_Ioi hx', setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hx'))]
    ring
  have := hG.const_sub (-eulerMascheroniConstant)
  rw [sub_zero] at this
  exact this.congr' (heq.mono fun x hx => hx.symm)

lemma tendsto_K0_add_log :
    Tendsto (fun x => K0 x + Real.log x) (𝓝[>] 0) (𝓝 (-eulerMascheroniConstant)) := by
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds |>.congr (fun _ => rfl)
  have hxlog : Tendsto (fun x : ℝ => x * Real.log x) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have T1 : Tendsto (fun x => K0 x - EE x) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hid
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact K0_sub_EE hx
  have T2 : Tendsto (fun x => (1 - exp (-x)) * Real.log x) (𝓝[>] 0) (𝓝 0) := by
    have hn : Tendsto (fun x : ℝ => ‖x * Real.log x‖) (𝓝[>] 0) (𝓝 0) := by
      simpa using hxlog.norm
    refine squeeze_zero_norm' ?_ hn
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0:ℝ) < x := hx
    have h1 := Real.add_one_le_exp (-x)
    have h2 : exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (x),
      abs_of_nonneg (by linarith : 0 ≤ 1 - exp (-x)), abs_of_pos hx']
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have T3 := tendsto_setIntegral_Ioi_log
  have hsum := (T1.add T2).add T3
  rw [zero_add, zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : (0:ℝ) < x := hx
  have := EE_ibp hx'
  rw [← EE_eq hx'] at this
  rw [this]; ring

end BM
