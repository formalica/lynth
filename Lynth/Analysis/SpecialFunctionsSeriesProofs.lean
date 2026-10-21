import Lynth.Analysis.SpecialFunctions

/-! Convergence, analyticity and real/complex compatibility lemmas for the
power series defining the special functions. Ported from the supplied proof
archive; the existing function definitions remain in `SpecialFunctions`. -/

open Filter Topology

namespace SpecialFunctions

theorem coefficient_nonneg (kind : SeriesKind) (k : ℕ) : 0 ≤ coefficient kind k := by
  induction k with
  | zero => simp [coefficient]
  | succ k ih =>
    simp only [coefficient]
    positivity

theorem num_mul_le_den (kind : SeriesKind) (k : ℕ) :
    (kind.num k : ℚ) * (k + 1) ≤ kind.den k := by
  cases kind <;> simp only [SeriesKind.num, SeriesKind.den] <;> push_cast <;> nlinarith

theorem den_pos (kind : SeriesKind) (k : ℕ) : (0 : ℚ) < kind.den k := by
  cases kind <;> simp only [SeriesKind.den] <;> positivity

theorem coefficient_le (kind : SeriesKind) (k : ℕ) :
    coefficient kind k ≤ 1 / k.factorial := by
  induction k with
  | zero => simp [coefficient]
  | succ k ih =>
    simp only [coefficient]
    have h1 := num_mul_le_den kind k
    have h2 := den_pos kind k
    have h0 := coefficient_nonneg kind k
    rw [Nat.factorial_succ, Nat.cast_mul, mul_div_assoc]
    calc coefficient kind k * ((kind.num k : ℚ) / kind.den k)
        ≤ 1 / k.factorial * (1 / (k + 1)) := by
          apply mul_le_mul ih _ (by positivity) (by positivity)
          rw [div_le_div_iff₀ h2 (by positivity)]
          linarith
      _ = 1 / ((k + 1 : ℕ) * k.factorial) := by push_cast; field_simp

theorem coefficient_abs_le (kind : SeriesKind) (k : ℕ) :
    |(coefficient kind k : ℝ)| ≤ 1 / k.factorial := by
  rw [abs_of_nonneg (by exact_mod_cast coefficient_nonneg kind k)]
  have h2 : ((coefficient kind k : ℚ) : ℝ) ≤ ((1 / (k.factorial : ℚ) : ℚ) : ℝ) :=
    Rat.cast_le.mpr (coefficient_le kind k)
  simpa using h2

theorem norm_coeff_mul_pow_le (kind : SeriesKind) (z : ℂ) (k : ℕ) :
    ‖(coefficient kind k : ℂ) * z ^ k‖ ≤ ‖z‖ ^ k / k.factorial := by
  rw [norm_mul, norm_pow]
  have : ‖(coefficient kind k : ℂ)‖ = |(coefficient kind k : ℝ)| := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [this]
  calc |(coefficient kind k : ℝ)| * ‖z‖ ^ k ≤ 1 / k.factorial * ‖z‖ ^ k := by
        gcongr; exact coefficient_abs_le kind k
    _ = _ := by ring

theorem summable_seriesC (kind : SeriesKind) (z : ℂ) :
    Summable (fun k => (coefficient kind k : ℂ) * z ^ k) :=
  Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖z‖)
    (norm_coeff_mul_pow_le kind z)

theorem summable_seriesR (kind : SeriesKind) (x : ℝ) :
    Summable (fun k => (coefficient kind k : ℝ) * x ^ k) := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖x‖) (fun k => ?_)
  rw [norm_mul, norm_pow, Real.norm_eq_abs (coefficient kind k : ℝ)]
  calc |(coefficient kind k : ℝ)| * ‖x‖ ^ k ≤ 1 / k.factorial * ‖x‖ ^ k := by
        gcongr; exact coefficient_abs_le kind k
    _ = _ := by ring

theorem seriesC_ofReal (kind : SeriesKind) (x : ℝ) :
    seriesC kind (x : ℂ) = (seriesR kind x : ℂ) := by
  rw [seriesC, seriesR, Complex.ofReal_tsum]
  push_cast
  rfl

theorem norm_seriesC_le (kind : SeriesKind) (z : ℂ) :
    ‖seriesC kind z‖ ≤ Real.exp ‖z‖ := by
  rw [seriesC, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  refine (norm_tsum_le_tsum_norm (summable_seriesC kind z).norm).trans ?_
  exact (summable_seriesC kind z).norm.tsum_le_tsum (norm_coeff_mul_pow_le kind z)
    (Real.summable_pow_div_factorial ‖z‖)

noncomputable def pS (kind : SeriesKind) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun k => (coefficient kind k : ℂ))

theorem pS_radius (kind : SeriesKind) : (pS kind).radius = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  refine (pS kind).le_radius_of_bound (Real.exp r) fun n => ?_
  have h1 : ‖pS kind n‖ ≤ 1 / n.factorial := by
    unfold pS
    rw [FormalMultilinearSeries.ofScalars_norm]
    have : ‖(coefficient kind n : ℂ)‖ = |(coefficient kind n : ℝ)| := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    rw [this]; exact coefficient_abs_le kind n
  calc ‖pS kind n‖ * (r : ℝ) ^ n ≤ 1 / n.factorial * (r : ℝ) ^ n := by gcongr
    _ = (r : ℝ) ^ n / n.factorial := by ring
    _ ≤ Real.exp r := Real.pow_div_factorial_le_exp _ r.2 n

theorem seriesC_eq_sum (kind : SeriesKind) : seriesC kind = (pS kind).sum := by
  funext z
  rw [seriesC, FormalMultilinearSeries.sum]
  congr 1
  funext k
  rw [pS, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm]

theorem analyticOnNhd_seriesC (kind : SeriesKind) :
    AnalyticOnNhd ℂ (seriesC kind) Set.univ := by
  intro z _
  have h := (pS kind).hasFPowerSeriesOnBall (by rw [pS_radius]; exact ENNReal.zero_lt_top)
  rw [pS_radius] at h
  rw [seriesC_eq_sum]
  exact h.analyticAt_of_mem (by simp)

theorem differentiable_seriesC (kind : SeriesKind) : Differentiable ℂ (seriesC kind) :=
  fun z => (analyticOnNhd_seriesC kind z (Set.mem_univ _)).differentiableAt

theorem continuous_seriesR (kind : SeriesKind) : Continuous (seriesR kind) := by
  have : seriesR kind = fun x : ℝ => (seriesC kind (x : ℂ)).re := by
    funext x; rw [seriesC_ofReal]; simp
  rw [this]
  exact Complex.continuous_re.comp ((differentiable_seriesC kind).continuous.comp
    Complex.continuous_ofReal)

theorem eta_factor_tendsto :
    Tendsto (fun s : ℂ => (1 - (2:ℂ)^(1-s)) / (s - 1)) (𝓝[≠] 1) (𝓝 (Real.log 2 : ℂ)) := by
  have hd : HasDerivAt (fun s : ℂ => 1 - (2:ℂ)^(1-s)) ((2:ℂ)^(1-(1:ℂ)) * Complex.log 2) 1 := by
    have h1 : HasDerivAt (fun s : ℂ => 1 - s) (-1) 1 := by
      simpa using (hasDerivAt_id (1:ℂ)).const_sub 1
    have h2 := h1.const_cpow (c := (2:ℂ)) (Or.inl (by norm_num))
    convert h2.const_sub 1 using 1
    ring
  have h := hd.tendsto_slope
  simp only [sub_self, Complex.cpow_zero, one_mul] at h
  rw [Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2), Complex.ofReal_ofNat]
  refine h.congr' ?_
  filter_upwards with s
  simp [slope_def_field]

theorem analyticAt_dirichletEta (s : ℂ) : AnalyticAt ℂ Complex.dirichletEta s := by
  have hdiff : ∀ w : ℂ, w ≠ 1 → DifferentiableAt ℂ Complex.dirichletEta w := by
    intro w hw
    have h : Complex.dirichletEta =ᶠ[𝓝 w] fun s => (1 - (2:ℂ)^(1-s)) * riemannZeta s := by
      filter_upwards [isOpen_ne.mem_nhds hw] with s hs
      simp [Complex.dirichletEta, hs]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ h
    refine DifferentiableAt.mul ?_ (differentiableAt_riemannZeta hw)
    refine (differentiableAt_const _).sub ?_
    exact ((differentiableAt_const 1).sub differentiableAt_id).const_cpow
      (Or.inl (by norm_num : (2:ℂ) ≠ 0))
  rcases eq_or_ne s 1 with rfl | hs
  · apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with w hw using hdiff w hw
    · apply continuousWithinAt_compl_self.mp
      rw [ContinuousWithinAt]
      have h1 : Complex.dirichletEta 1 = (Real.log 2 : ℂ) := by simp [Complex.dirichletEta]
      rw [h1]
      have h := eta_factor_tendsto.mul riemannZeta_residue_one
      rw [mul_one] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw' : w - 1 ≠ 0 := sub_ne_zero.2 hw
      simp only [Complex.dirichletEta, show w ≠ 1 from hw, ite_false]
      field_simp
  · exact DifferentiableOn.analyticAt (s := {w | w ≠ 1})
      (fun w hw => (hdiff w hw).differentiableWithinAt) (isOpen_ne.mem_nhds hs)

theorem riemannZeta_ofReal_im (x : ℝ) : (riemannZeta (x : ℂ)).im = 0 := by
  have h := riemannZeta_conj (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have h' := congrArg Complex.im h
  simp at h'
  linarith

theorem dirichletEta_ofReal (x : ℝ) :
    Complex.dirichletEta x = (Real.dirichletEta x : ℂ) := by
  rcases eq_or_ne x 1 with rfl | hx
  · simp [Complex.dirichletEta, Real.dirichletEta]
  have hx' : (x : ℂ) ≠ 1 := by exact_mod_cast hx
  simp only [Complex.dirichletEta, Real.dirichletEta, hx, hx', ite_false]
  have hz : riemannZeta (x : ℂ) = ((riemannZeta (x:ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [riemannZeta_ofReal_im]
  have h2 : (2:ℂ)^(1 - (x:ℂ)) = (((2:ℝ)^(1-x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by norm_num)]; push_cast; rfl
  rw [h2]; conv_lhs => rw [hz]
  push_cast; ring

theorem analyticAt_seriesC_comp (kind : SeriesKind) {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) : AnalyticAt ℂ (fun z => seriesC kind (f z)) z :=
  (analyticOnNhd_seriesC kind (f z) (Set.mem_univ _)).comp hf

theorem analyticOnNhd_erf : AnalyticOnNhd ℂ Complex.erf Set.univ := by
  intro z _
  unfold Complex.erf
  exact (analyticAt_const.mul analyticAt_id).mul
    (analyticAt_seriesC_comp _ ((analyticAt_id.pow 2).neg))

theorem analyticOnNhd_Si : AnalyticOnNhd ℂ Complex.Si Set.univ := by
  intro z _
  unfold Complex.Si
  exact analyticAt_id.mul (analyticAt_seriesC_comp _ ((analyticAt_id.pow 2).neg))

theorem analyticOnNhd_airyAi : AnalyticOnNhd ℂ Complex.airyAi Set.univ := by
  intro z _
  unfold Complex.airyAi
  exact (analyticAt_const.mul (analyticAt_seriesC_comp _ (analyticAt_id.pow 3))).add
    ((analyticAt_const.mul analyticAt_id).mul (analyticAt_seriesC_comp _ (analyticAt_id.pow 3)))

theorem erf_ofReal (x : ℝ) : Complex.erf x = (Real.erf x : ℂ) := by
  unfold Complex.erf Real.erf
  have h : -(x : ℂ) ^ 2 = ((-x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, seriesC_ofReal]; push_cast; ring

theorem Si_ofReal (x : ℝ) : Complex.Si x = (Real.Si x : ℂ) := by
  unfold Complex.Si Real.Si
  have h : -(x : ℂ) ^ 2 = ((-x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, seriesC_ofReal]; push_cast; ring

theorem airyAi_ofReal (x : ℝ) : Complex.airyAi x = (Real.airyAi x : ℂ) := by
  unfold Complex.airyAi Real.airyAi
  have h : (x : ℂ) ^ 3 = ((x ^ 3 : ℝ) : ℂ) := by push_cast; ring
  rw [h, seriesC_ofReal, seriesC_ofReal]; push_cast; ring

end SpecialFunctions

namespace Real

theorem continuous_erf : Continuous Real.erf := by
  unfold Real.erf
  have h := SpecialFunctions.continuous_seriesR .erf
  fun_prop

theorem continuous_Si : Continuous Real.Si := by
  unfold Real.Si
  have h := SpecialFunctions.continuous_seriesR .si
  fun_prop

theorem continuous_airyAi : Continuous Real.airyAi := by
  unfold Real.airyAi
  have h0 := SpecialFunctions.continuous_seriesR .airy0
  have h1 := SpecialFunctions.continuous_seriesR .airy1
  fun_prop

theorem measurable_dirichletEta : Measurable Real.dirichletEta := by
  apply measurable_of_continuousOn_compl_singleton 1
  have h : Set.EqOn Real.dirichletEta
      (fun s => (1 - (2 : ℝ) ^ (1 - s)) * (riemannZeta (s : ℂ)).re) {1}ᶜ := by
    intro s hs
    simp only [Real.dirichletEta, if_neg (show s ≠ 1 from hs)]
  refine ContinuousOn.congr ?_ h
  intro s hs
  apply ContinuousAt.continuousWithinAt
  have hs1 : (s : ℂ) ≠ 1 := by
    intro h1; exact hs (by exact_mod_cast h1)
  have hz : ContinuousAt (fun s : ℝ => riemannZeta (s : ℂ)) s :=
    (differentiableAt_riemannZeta hs1).continuousAt.comp Complex.continuous_ofReal.continuousAt
  have h2 : ContinuousAt (fun s : ℝ => (2 : ℝ) ^ (1 - s)) s :=
    (Real.continuousAt_const_rpow (by norm_num)).comp (by fun_prop)
  exact (continuousAt_const.sub h2).mul (Complex.continuous_re.continuousAt.comp hz)

end Real
