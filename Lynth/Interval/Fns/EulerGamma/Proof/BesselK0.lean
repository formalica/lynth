import Lynth.Interval.Fns.EulerGamma.Proof.Notation

/-!
# Analytic properties of `K0 x = ∫_0^∞ exp(-2x cosh v) dv`
-/

open Real MeasureTheory Set Filter Topology

namespace BM

/-- `Kf j x = ∫_0^∞ cosh(v)^j exp(-2x cosh v) dv` -/
noncomputable def Kf (j : ℕ) (x : ℝ) : ℝ := ∫ v in Ioi 0, cosh v ^ j * exp (-(2 * x * cosh v))

lemma K0_eq_Kf (x : ℝ) : K0 x = Kf 0 x := by
  unfold K0 Kf; simp

lemma pow_mul_exp_neg_le (j : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    t ^ j * exp (-(a * t)) ≤ j.factorial / a ^ j := by
  have h := Real.pow_div_factorial_le_exp (a * t) (by positivity) j
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  rw [div_le_iff₀ hf] at h
  rw [le_div_iff₀ (by positivity)]
  calc t ^ j * exp (-(a * t)) * a ^ j = (a * t) ^ j * exp (-(a * t)) := by ring
    _ ≤ (exp (a * t) * j.factorial) * exp (-(a * t)) := by gcongr
    _ = j.factorial := by rw [mul_comm (exp _), mul_assoc, ← Real.exp_add]; simp

lemma cosh_pow_exp_le (j : ℕ) {c : ℝ} (hc : 0 < c) (v : ℝ) (hv : 0 ≤ v) :
    cosh v ^ j * exp (-(c * cosh v)) ≤ (j.factorial / (c / 2) ^ j) * exp (-(c / 2) * v) := by
  have h1 := pow_mul_exp_neg_le j (a := c / 2) (by positivity) (cosh_pos v).le
  have hcv : v ≤ cosh v := by
    have := Real.quadratic_le_exp_of_nonneg hv
    have := Real.exp_pos (-v)
    rw [Real.cosh_eq]; nlinarith [sq_nonneg (v - 1)]
  have h2 : exp (-(c / 2 * cosh v)) ≤ exp (-(c / 2) * v) := by
    apply Real.exp_le_exp.mpr; nlinarith
  calc cosh v ^ j * exp (-(c * cosh v))
      = (cosh v ^ j * exp (-(c / 2 * cosh v))) * exp (-(c / 2 * cosh v)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ (j.factorial / (c / 2) ^ j) * exp (-(c / 2) * v) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)

lemma integrableOn_cosh_pow_exp (j : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun v => cosh v ^ j * exp (-(c * cosh v))) (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 (by positivity : 0 < c / 2)).const_mul
    (j.factorial / (c / 2) ^ j)).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun v => cosh v ^ j * exp (-(c * cosh v))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (fun v hv => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := cosh_pos v; positivity)]
    exact cosh_pow_exp_le j hc v (le_of_lt hv)

lemma hasDerivAt_Kf (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (Kf j) (-2 * Kf (j + 1) x) x := by
  have hball : Metric.ball x (x / 2) ∈ 𝓝 x := Metric.ball_mem_nhds x (by positivity)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun x v => cosh v ^ j * exp (-(2 * x * cosh v)))
    (F' := fun x v => cosh v ^ j * (exp (-(2 * x * cosh v)) * (-(2 * cosh v))))
    (bound := fun v => 2 * (cosh v ^ (j + 1) * exp (-(x * cosh v)))) hball
    (Eventually.of_forall (fun x => by fun_prop))
    (by
      have := integrableOn_cosh_pow_exp j (c := 2 * x) (by positivity)
      simp only [mul_assoc] at this ⊢
      exact this)
    (by fun_prop)
    (Eventually.of_forall (fun v x' hx' => by
      have hx'' : x / 2 < x' := by
        have := (Metric.mem_ball.mp hx'); rw [Real.dist_eq, abs_lt] at this; linarith
      have hc := cosh_pos v
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity),
        abs_of_pos (Real.exp_pos _), abs_neg, abs_of_pos (by positivity)]
      have : exp (-(2 * x' * cosh v)) ≤ exp (-(x * cosh v)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      calc cosh v ^ j * (exp (-(2 * x' * cosh v)) * (2 * cosh v))
          = 2 * (cosh v ^ (j + 1) * exp (-(2 * x' * cosh v))) := by ring
        _ ≤ 2 * (cosh v ^ (j + 1) * exp (-(x * cosh v))) := by gcongr))
    ((integrableOn_cosh_pow_exp (j + 1) hx).const_mul 2)
    (Eventually.of_forall (fun v x' _ => by
      have h1 : HasDerivAt (fun x => -(2 * x * cosh v)) (-(2 * cosh v)) x' := by
        have := (((hasDerivAt_id x').const_mul 2).mul_const (cosh v)).neg
        convert this using 1 <;> first | rfl | ring
      exact (h1.exp).const_mul _))
  unfold Kf
  convert key.2 using 1
  rw [← integral_const_mul]
  congr 1; ext v; ring

/-- `L x = 2x ∫ cosh v exp(-2x cosh v) dv = -x K0'(x)` -/
noncomputable def LL (x : ℝ) : ℝ := 2 * x * Kf 1 x

lemma hasDerivAt_K0 {x : ℝ} (hx : 0 < x) : HasDerivAt K0 (-(LL x / x)) x := by
  have := hasDerivAt_Kf 0 hx
  have e : K0 = Kf 0 := funext K0_eq_Kf
  rw [e]; convert this using 1
  unfold LL; field_simp

lemma sinh_exp_tendsto {x : ℝ} (hx : 0 < x) (j : ℕ) :
    Tendsto (fun v => cosh v ^ j * exp (-(2 * x * cosh v))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun v => 2 * x * cosh v) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) (tendsto_atTop_mono (fun v => by
      rw [Real.cosh_eq]; have := Real.exp_pos (-v); linarith)
      (Real.tendsto_exp_atTop.atTop_div_const (by norm_num : (0:ℝ) < 2)))
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp h1
  have h3 := h2.const_mul ((2 * x)⁻¹ ^ j)
  rw [mul_zero] at h3
  refine h3.congr (fun v => ?_)
  simp only [Function.comp]
  have : (2 * x) ≠ 0 := by positivity
  rw [mul_pow]; field_simp
  rw [← mul_pow, one_div_mul_cancel this, one_pow]

/-- `∫_0^∞ (2 cosh v - 4x sinh² v) exp(-2x cosh v) dv = 0` -/
lemma ibp_identity {x : ℝ} (hx : 0 < x) :
    ∫ v in Ioi 0, (2 * cosh v - 4 * x * sinh v ^ 2) * exp (-(2 * x * cosh v)) = 0 := by
  have hderiv : ∀ v ∈ Ici (0:ℝ), HasDerivAt (fun v => 2 * sinh v * exp (-(2 * x * cosh v)))
      ((2 * cosh v - 4 * x * sinh v ^ 2) * exp (-(2 * x * cosh v))) v := by
    intro v _
    have h2 : HasDerivAt (fun v => -(2 * x * cosh v)) (-(2 * x * sinh v)) v := by
      have := ((Real.hasDerivAt_cosh v).const_mul (2 * x)).neg; convert this using 1
    have := ((Real.hasDerivAt_sinh v).const_mul 2).mul h2.exp
    convert this using 1; ring
  have hint : IntegrableOn (fun v => (2 * cosh v - 4 * x * sinh v ^ 2) * exp (-(2 * x * cosh v)))
      (Ioi 0) := by
    have h1 := (integrableOn_cosh_pow_exp 1 (c := 2 * x) (by positivity)).const_mul 2
    have h2 := (integrableOn_cosh_pow_exp 2 (c := 2 * x) (by positivity)).const_mul (4 * x)
    have h0 := (integrableOn_cosh_pow_exp 0 (c := 2 * x) (by positivity)).const_mul (4 * x)
    refine IntegrableOn.congr_fun ((h1.sub h2).add h0) (fun v _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Pi.sub_apply]
    have := Real.cosh_sq v
    rw [show sinh v ^ 2 = cosh v ^ 2 - 1 by linarith]; ring_nf
  have hlim : Tendsto (fun v => 2 * sinh v * exp (-(2 * x * cosh v))) atTop (𝓝 0) := by
    have h := (sinh_exp_tendsto hx 1).const_mul 2
    rw [mul_zero] at h
    refine squeeze_zero' ?_ ?_ h
    · filter_upwards [eventually_ge_atTop 0] with v hv
      have := Real.sinh_nonneg_iff.mpr hv
      positivity
    · filter_upwards with v
      have := (Real.sinh_lt_cosh v).le
      have := Real.exp_pos (-(2 * x * cosh v))
      rw [pow_one]
      nlinarith
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [this]; simp

lemma Kf_integrable (j : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun v => cosh v ^ j * exp (-(2 * x * cosh v))) (Ioi 0) := by
  simpa [mul_assoc] using integrableOn_cosh_pow_exp j (c := 2 * x) (by positivity)

lemma hasDerivAt_LL {x : ℝ} (hx : 0 < x) : HasDerivAt LL (-(4 * x * K0 x)) x := by
  have h := ((hasDerivAt_id x).const_mul 2).mul (hasDerivAt_Kf 1 hx)
  unfold LL
  convert h using 1
  · funext y; simp [id]
  have hibp := ibp_identity hx
  have e : ∫ v in Ioi 0, (2 * cosh v - 4 * x * sinh v ^ 2) * exp (-(2 * x * cosh v))
      = 2 * Kf 1 x - 4 * x * Kf 2 x + 4 * x * Kf 0 x := by
    unfold Kf
    have hc : ∀ v, (2 * cosh v - 4 * x * sinh v ^ 2) * exp (-(2 * x * cosh v))
        = 2 * (cosh v ^ 1 * exp (-(2 * x * cosh v))) - 4 * x * (cosh v ^ 2 * exp (-(2 * x * cosh v)))
          + 4 * x * (cosh v ^ 0 * exp (-(2 * x * cosh v))) := by
      intro v
      have := Real.cosh_sq v
      rw [show sinh v ^ 2 = cosh v ^ 2 - 1 by linarith]; ring
    simp_rw [hc]
    have i1 : Integrable (fun v => 2 * (cosh v ^ 1 * exp (-(2 * x * cosh v))))
        (volume.restrict (Ioi 0)) := (Kf_integrable 1 hx).const_mul _
    have i2 : Integrable (fun v => 4 * x * (cosh v ^ 2 * exp (-(2 * x * cosh v))))
        (volume.restrict (Ioi 0)) := (Kf_integrable 2 hx).const_mul _
    have i0 : Integrable (fun v => 4 * x * (cosh v ^ 0 * exp (-(2 * x * cosh v))))
        (volume.restrict (Ioi 0)) := (Kf_integrable 0 hx).const_mul _
    have i12 : Integrable (fun v => 2 * (cosh v ^ 1 * exp (-(2 * x * cosh v)))
        - 4 * x * (cosh v ^ 2 * exp (-(2 * x * cosh v)))) (volume.restrict (Ioi 0)) := i1.sub i2
    rw [integral_add i12 i0, integral_sub i1 i2,
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [K0_eq_Kf]; simp only [id]
  linarith

lemma LL_sub_bound {x : ℝ} (hx : 0 < x) : |LL x - exp (-(2 * x))| ≤ 2 * x := by
  -- `∫ 2x sinh v e^{-2x cosh v} = e^{-2x}`
  have hderiv : ∀ v ∈ Ici (0:ℝ), HasDerivAt (fun v => -exp (-(2 * x * cosh v)))
      (2 * x * sinh v * exp (-(2 * x * cosh v))) v := by
    intro v _
    have h2 : HasDerivAt (fun v => -(2 * x * cosh v)) (-(2 * x * sinh v)) v := by
      have := ((Real.hasDerivAt_cosh v).const_mul (2 * x)).neg; convert this using 1
    have := h2.exp.neg
    convert this using 1; ring
  have hE : IntegrableOn (fun v => 2 * x * (exp (-v) * exp (-(2 * x * cosh v)))) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0:ℝ) < 1)).const_mul (2 * x)).mono' ?_ ?_
    · exact (by fun_prop : Continuous fun v =>
        2 * x * (exp (-v) * exp (-(2 * x * cosh v)))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (fun v hv => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : exp (-(2 * x * cosh v)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; have := cosh_pos v; nlinarith
      have h1 : exp (-v) * exp (-(2 * x * cosh v)) ≤ exp (-1 * v) := by
        rw [neg_one_mul]
        calc exp (-v) * exp (-(2 * x * cosh v)) ≤ exp (-v) * 1 := by gcongr
          _ = exp (-v) := mul_one _
      gcongr
  have hC := (Kf_integrable 1 hx).const_mul (2 * x)
  have hS : IntegrableOn (fun v => 2 * x * sinh v * exp (-(2 * x * cosh v))) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hC.sub hE) (fun v _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    rw [Real.sinh_eq, Real.cosh_eq]; ring
  have hlim : Tendsto (fun v => -exp (-(2 * x * cosh v))) atTop (𝓝 0) := by
    have := (sinh_exp_tendsto hx 0).neg
    simpa using this
  have hSint := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hS hlim
  simp only [Real.cosh_zero, mul_one, neg_neg, zero_sub] at hSint
  have hsplit : LL x = (∫ v in Ioi 0, 2 * x * sinh v * exp (-(2 * x * cosh v)))
      + ∫ v in Ioi 0, 2 * x * (exp (-v) * exp (-(2 * x * cosh v))) := by
    rw [← integral_add hS hE, LL, Kf, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
    rw [Real.sinh_eq, Real.cosh_eq]; ring
  rw [hsplit, hSint]
  simp only [add_sub_cancel_left]
  have h0 : 0 ≤ ∫ v in Ioi 0, 2 * x * (exp (-v) * exp (-(2 * x * cosh v))) :=
    setIntegral_nonneg measurableSet_Ioi (fun v _ => by positivity)
  rw [abs_of_nonneg h0]
  have h1 : ∫ v in Ioi 0, 2 * x * (exp (-v) * exp (-(2 * x * cosh v)))
      ≤ ∫ v in Ioi 0, 2 * x * exp (-1 * v) := by
    refine setIntegral_mono_on hE ((exp_neg_integrableOn_Ioi 0 (by norm_num)).const_mul _)
      measurableSet_Ioi (fun v hv => ?_)
    have : exp (-(2 * x * cosh v)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := cosh_pos v; nlinarith
    rw [neg_one_mul]
    have := Real.exp_pos (-v)
    have : exp (-v) * exp (-(2 * x * cosh v)) ≤ exp (-v) := by nlinarith
    gcongr
  have h2 : ∫ v in Ioi 0, 2 * x * exp (-1 * v) = 2 * x := by
    simp_rw [neg_one_mul]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  linarith

lemma tendsto_LL : Tendsto LL (𝓝[>] 0) (𝓝 1) := by
  have h1 : Tendsto (fun x => exp (-(2 * x))) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have h : Tendsto (fun x : ℝ => exp (-(2 * x))) (𝓝 0) (𝓝 1) := by
      have := (by fun_prop : Continuous (fun x : ℝ => exp (-(2 * x)))).tendsto 0
      simpa using this
    exact h.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun x : ℝ => 2 * x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => 2 * x) (𝓝 0) (𝓝 0) := by
      have := (by fun_prop : Continuous (fun x : ℝ => 2 * x)).tendsto 0
      simpa using this
    exact h.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun x => LL x - exp (-(2 * x))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact LL_sub_bound hx
  simpa using h3.add h1

end BM
