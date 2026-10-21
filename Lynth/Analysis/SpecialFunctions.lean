import Mathlib
import Lynth.Interval.Check.AiryBounds
import Lynth.Interval.Check.EtaProof

/-! Entire special functions, with independent real and complex definitions.
The power series are specifications; numerical evaluation uses integer kernels.
The Airy normalization certificate uses the verified interval Gamma implementation.
-/

namespace SpecialFunctions

inductive SeriesKind where
  | erf | si | airy0 | airy1
deriving BEq, DecidableEq, Repr, Inhabited

def SeriesKind.num : SeriesKind → ℕ → ℕ
  | .erf, k | .si, k => 2*k+1
  | .airy0, _ | .airy1, _ => 1

def SeriesKind.den : SeriesKind → ℕ → ℕ
  | .erf, k => (k+1)*(2*k+3)
  | .si, k => (2*k+2)*(2*k+3)^2
  | .airy0, k => (3*k+3)*(3*k+2)
  | .airy1, k => (3*k+3)*(3*k+4)

def coefficient (kind : SeriesKind) : ℕ → ℚ
  | 0 => 1
  | k+1 => coefficient kind k * kind.num k / kind.den k

noncomputable def seriesR (kind : SeriesKind) (x : ℝ) : ℝ :=
  ∑' k, (coefficient kind k : ℝ) * x^k

noncomputable def seriesC (kind : SeriesKind) (z : ℂ) : ℂ :=
  ∑' k, (coefficient kind k : ℂ) * z^k

noncomputable def airyA : ℝ := 1 / ((3 : ℝ)^(2/3 : ℝ) * Real.Gamma (2/3))
noncomputable def airyB : ℝ := -1 / ((3 : ℝ)^(1/3 : ℝ) * Real.Gamma (1/3))

end SpecialFunctions

namespace Real

noncomputable def erf (x : ℝ) : ℝ :=
  2 / Real.sqrt Real.pi * x * SpecialFunctions.seriesR .erf (-x^2)

/-- Sine integral, with its removable singularity at zero filled in. -/
noncomputable def Si (x : ℝ) : ℝ := x * SpecialFunctions.seriesR .si (-x^2)

/-- Entire continuation of the alternating zeta function; eta(1) = log 2. -/
noncomputable def dirichletEta (s : ℝ) : ℝ :=
  if s = 1 then Real.log 2 else (1 - (2 : ℝ)^(1-s)) * (riemannZeta (s : ℂ)).re

noncomputable def airyAi (x : ℝ) : ℝ :=
  SpecialFunctions.airyA * SpecialFunctions.seriesR .airy0 (x^3) +
    SpecialFunctions.airyB * x * SpecialFunctions.seriesR .airy1 (x^3)

end Real

namespace Complex

noncomputable def erf (z : ℂ) : ℂ :=
  (2 / Real.sqrt Real.pi : ℝ) * z * SpecialFunctions.seriesC .erf (-z^2)

noncomputable def Si (z : ℂ) : ℂ := z * SpecialFunctions.seriesC .si (-z^2)

noncomputable def dirichletEta (s : ℂ) : ℂ :=
  if s = 1 then (Real.log 2 : ℂ) else (1 - (2 : ℂ)^(1-s)) * riemannZeta s

noncomputable def airyAi (z : ℂ) : ℂ :=
  (SpecialFunctions.airyA : ℂ) * SpecialFunctions.seriesC .airy0 (z^3) +
    (SpecialFunctions.airyB : ℂ) * z * SpecialFunctions.seriesC .airy1 (z^3)

end Complex

section
/- Auxiliary proofs ported from SpecialFunctionsSeries.lean. -/

/-! Convergence, analyticity and real/complex compatibility of the power series
defining the special functions in `SpecialFunctionsDefs`. -/

open Filter Topology

namespace SpecialFunctions

private theorem coefficient_nonneg (kind : SeriesKind) (k : ℕ) : 0 ≤ coefficient kind k := by
  induction k with
  | zero => simp [coefficient]
  | succ k ih =>
    simp only [coefficient]
    positivity

private theorem num_mul_le_den (kind : SeriesKind) (k : ℕ) :
    (kind.num k : ℚ) * (k + 1) ≤ kind.den k := by
  cases kind <;> simp only [SeriesKind.num, SeriesKind.den] <;> push_cast <;> nlinarith

private theorem den_pos (kind : SeriesKind) (k : ℕ) : (0 : ℚ) < kind.den k := by
  cases kind <;> simp only [SeriesKind.den] <;> positivity

private theorem coefficient_le (kind : SeriesKind) (k : ℕ) :
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

private theorem coefficient_abs_le (kind : SeriesKind) (k : ℕ) :
    |(coefficient kind k : ℝ)| ≤ 1 / k.factorial := by
  rw [abs_of_nonneg (by exact_mod_cast coefficient_nonneg kind k)]
  have h2 : ((coefficient kind k : ℚ) : ℝ) ≤ ((1 / (k.factorial : ℚ) : ℚ) : ℝ) :=
    Rat.cast_le.mpr (coefficient_le kind k)
  simpa using h2

private theorem norm_coeff_mul_pow_le (kind : SeriesKind) (z : ℂ) (k : ℕ) :
    ‖(coefficient kind k : ℂ) * z ^ k‖ ≤ ‖z‖ ^ k / k.factorial := by
  rw [norm_mul, norm_pow]
  have : ‖(coefficient kind k : ℂ)‖ = |(coefficient kind k : ℝ)| := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [this]
  calc |(coefficient kind k : ℝ)| * ‖z‖ ^ k ≤ 1 / k.factorial * ‖z‖ ^ k := by
        gcongr; exact coefficient_abs_le kind k
    _ = _ := by ring

private theorem summable_seriesC (kind : SeriesKind) (z : ℂ) :
    Summable (fun k => (coefficient kind k : ℂ) * z ^ k) :=
  Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖z‖)
    (norm_coeff_mul_pow_le kind z)

private theorem summable_seriesR (kind : SeriesKind) (x : ℝ) :
    Summable (fun k => (coefficient kind k : ℝ) * x ^ k) := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖x‖) (fun k => ?_)
  rw [norm_mul, norm_pow, Real.norm_eq_abs (coefficient kind k : ℝ)]
  calc |(coefficient kind k : ℝ)| * ‖x‖ ^ k ≤ 1 / k.factorial * ‖x‖ ^ k := by
        gcongr; exact coefficient_abs_le kind k
    _ = _ := by ring

private theorem seriesC_ofReal (kind : SeriesKind) (x : ℝ) :
    seriesC kind (x : ℂ) = (seriesR kind x : ℂ) := by
  rw [seriesC, seriesR, Complex.ofReal_tsum]
  push_cast
  rfl

private theorem norm_seriesC_le (kind : SeriesKind) (z : ℂ) :
    ‖seriesC kind z‖ ≤ Real.exp ‖z‖ := by
  rw [seriesC, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  refine (norm_tsum_le_tsum_norm (summable_seriesC kind z).norm).trans ?_
  exact (summable_seriesC kind z).norm.tsum_le_tsum (norm_coeff_mul_pow_le kind z)
    (Real.summable_pow_div_factorial ‖z‖)

/-- The formal power series of `seriesC`. -/
private noncomputable def pS (kind : SeriesKind) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun k => (coefficient kind k : ℂ))

private theorem pS_radius (kind : SeriesKind) : (pS kind).radius = ⊤ := by
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

private theorem seriesC_eq_sum (kind : SeriesKind) : seriesC kind = (pS kind).sum := by
  funext z
  rw [seriesC, FormalMultilinearSeries.sum]
  congr 1
  funext k
  rw [pS, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm]

private theorem analyticOnNhd_seriesC (kind : SeriesKind) :
    AnalyticOnNhd ℂ (seriesC kind) Set.univ := by
  intro z _
  have h := (pS kind).hasFPowerSeriesOnBall (by rw [pS_radius]; exact ENNReal.zero_lt_top)
  rw [pS_radius] at h
  rw [seriesC_eq_sum]
  exact h.analyticAt_of_mem (by simp)

private theorem differentiable_seriesC (kind : SeriesKind) : Differentiable ℂ (seriesC kind) :=
  fun z => (analyticOnNhd_seriesC kind z (Set.mem_univ _)).differentiableAt

private theorem continuous_seriesR (kind : SeriesKind) : Continuous (seriesR kind) := by
  have : seriesR kind = fun x : ℝ => (seriesC kind (x : ℂ)).re := by
    funext x; rw [seriesC_ofReal]; simp
  rw [this]
  exact Complex.continuous_re.comp ((differentiable_seriesC kind).continuous.comp
    Complex.continuous_ofReal)


private theorem eta_factor_tendsto :
    Tendsto (fun s : ℂ => (1 - (2:ℂ)^(1-s)) / (s - 1)) (𝓝[≠] 1) (𝓝 (Real.log 2 : ℂ)) := by
  have hd : HasDerivAt (fun s : ℂ => 1 - (2:ℂ)^(1-s)) ((2:ℂ)^(1-(1:ℂ)) * Complex.log 2) 1 := by
    have h1 : HasDerivAt (fun s : ℂ => 1 - s) (-1) 1 := by
      simpa using (hasDerivAt_id (1:ℂ)).const_sub 1
    have h2 := h1.const_cpow (c := (2:ℂ)) (Or.inl (by norm_num))
    convert h2.const_sub 1 using 1
    ring
  have := hd.tendsto_slope
  simp only [sub_self, Complex.cpow_zero, one_mul] at this
  rw [Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2), Complex.ofReal_ofNat]
  refine this.congr' ?_
  filter_upwards with s
  simp [slope_def_field]

private theorem analyticAt_dirichletEta (s : ℂ) : AnalyticAt ℂ Complex.dirichletEta s := by
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
      have := eta_factor_tendsto.mul riemannZeta_residue_one
      rw [mul_one] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw' : w - 1 ≠ 0 := sub_ne_zero.2 hw
      simp only [Complex.dirichletEta, show w ≠ 1 from hw, ite_false]
      field_simp
  · exact DifferentiableOn.analyticAt (s := {w | w ≠ 1})
      (fun w hw => (hdiff w hw).differentiableWithinAt) (isOpen_ne.mem_nhds hs)

private theorem riemannZeta_ofReal_im (x : ℝ) : (riemannZeta (x : ℂ)).im = 0 := by
  have h := riemannZeta_conj (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  simp at this
  linarith

private theorem dirichletEta_ofReal (x : ℝ) :
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

private theorem analyticAt_seriesC_comp (kind : SeriesKind) {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) : AnalyticAt ℂ (fun z => seriesC kind (f z)) z :=
  (analyticOnNhd_seriesC kind (f z) (Set.mem_univ _)).comp hf

private theorem analyticOnNhd_erf : AnalyticOnNhd ℂ Complex.erf Set.univ := by
  intro z _
  unfold Complex.erf
  exact (analyticAt_const.mul analyticAt_id).mul
    (analyticAt_seriesC_comp _ ((analyticAt_id.pow 2).neg))

private theorem analyticOnNhd_Si : AnalyticOnNhd ℂ Complex.Si Set.univ := by
  intro z _
  unfold Complex.Si
  exact analyticAt_id.mul (analyticAt_seriesC_comp _ ((analyticAt_id.pow 2).neg))

private theorem analyticOnNhd_airyAi : AnalyticOnNhd ℂ Complex.airyAi Set.univ := by
  intro z _
  unfold Complex.airyAi
  exact (analyticAt_const.mul (analyticAt_seriesC_comp _ (analyticAt_id.pow 3))).add
    ((analyticAt_const.mul analyticAt_id).mul (analyticAt_seriesC_comp _ (analyticAt_id.pow 3)))

private theorem erf_ofReal (x : ℝ) : Complex.erf x = (Real.erf x : ℂ) := by
  unfold Complex.erf Real.erf
  have : -(x : ℂ) ^ 2 = ((-x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, seriesC_ofReal]; push_cast; ring

private theorem Si_ofReal (x : ℝ) : Complex.Si x = (Real.Si x : ℂ) := by
  unfold Complex.Si Real.Si
  have : -(x : ℂ) ^ 2 = ((-x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, seriesC_ofReal]; push_cast; ring

private theorem airyAi_ofReal (x : ℝ) : Complex.airyAi x = (Real.airyAi x : ℂ) := by
  unfold Complex.airyAi Real.airyAi
  have : (x : ℂ) ^ 3 = ((x ^ 3 : ℝ) : ℂ) := by push_cast; ring
  rw [this, seriesC_ofReal, seriesC_ofReal]; push_cast; ring

end SpecialFunctions

namespace Real

private theorem continuous_erf : Continuous Real.erf := by
  unfold Real.erf
  have := SpecialFunctions.continuous_seriesR .erf
  fun_prop

private theorem continuous_Si : Continuous Real.Si := by
  unfold Real.Si
  have := SpecialFunctions.continuous_seriesR .si
  fun_prop

private theorem continuous_airyAi : Continuous Real.airyAi := by
  unfold Real.airyAi
  have := SpecialFunctions.continuous_seriesR .airy0
  have := SpecialFunctions.continuous_seriesR .airy1
  fun_prop

private theorem measurable_dirichletEta : Measurable Real.dirichletEta := by
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


end

section
/- Auxiliary proofs ported from SpecialFunctionsErf.lean. -/

/-! Derivatives of the error function and of the sine integral, and the
real-axis consequences used by the special-function contracts. -/

open Filter Topology MeasureTheory

namespace SpecialFunctions

private theorem hasDerivAt_oddSeries (b : ℕ → ℂ) (hb : ∀ k, ‖b k‖ * (2 * k + 1) ≤ 1 / k.factorial)
    (z : ℂ) :
    HasDerivAt (fun z => ∑' k, b k * z ^ (2 * k + 1))
      (∑' k, b k * (2 * k + 1) * z ^ (2 * k)) z := by
  set R := ‖z‖ + 1
  have hR : 0 < R := by positivity
  have hu : Summable (fun k : ℕ => (R ^ 2) ^ k / k.factorial) := Real.summable_pow_div_factorial _
  refine hasDerivAt_tsum_of_isPreconnected (u := fun k : ℕ => (R ^ 2) ^ k / k.factorial)
    (g := fun k (y : ℂ) => b k * y ^ (2 * k + 1))
    (g' := fun k (y : ℂ) => b k * (2 * k + 1) * y ^ (2 * k))
    (t := Metric.ball (0:ℂ) R) (y₀ := (0:ℂ)) hu Metric.isOpen_ball
    (convex_ball (0:ℂ) R).isPreconnected
    ?_ ?_ (Metric.mem_ball_self hR) ?_ (by simp [R])
  · intro k y _
    have := (hasDerivAt_pow (2 * k + 1) y).const_mul (b k)
    convert this using 1
    push_cast; ring
  · intro k y hy
    rw [mem_ball_zero_iff] at hy
    rw [norm_mul, norm_mul, norm_pow]
    have h2 : ‖((2 * k + 1 : ℕ) : ℂ)‖ = 2 * k + 1 := by
      rw [Complex.norm_natCast]; push_cast; ring
    have : ‖(2 * (k:ℂ) + 1)‖ = 2 * k + 1 := by
      rw [← h2]; push_cast; rfl
    rw [this, ← pow_mul]
    calc ‖b k‖ * (2 * k + 1) * ‖y‖ ^ (2 * k) ≤ 1 / k.factorial * R ^ (2 * k) := by
          gcongr
          exact hb k
      _ = _ := by ring
  · simp

private theorem coefficient_erf (k : ℕ) :
    coefficient .erf k = 1 / (k.factorial * (2 * k + 1)) := by
  induction k with
  | zero => simp [coefficient]
  | succ k ih =>
    simp only [coefficient, ih, SeriesKind.num, SeriesKind.den, Nat.factorial_succ]
    push_cast
    field_simp
    ring

private theorem coefficient_si (k : ℕ) :
    coefficient .si k = 1 / ((2 * k + 1).factorial * (2 * k + 1)) := by
  induction k with
  | zero => simp [coefficient]
  | succ k ih =>
    simp only [coefficient, ih, SeriesKind.num, SeriesKind.den]
    have hf : (2 * (k + 1) + 1).factorial = (2 * k + 3) * ((2 * k + 2) * (2 * k + 1).factorial) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by ring, Nat.factorial_succ,
        show 2 * k + 2 = (2 * k + 1) + 1 by ring, Nat.factorial_succ]
    rw [hf]
    push_cast
    field_simp
    ring

/-- Odd-series form of the error function. -/
private theorem erf_eq_tsum (z : ℂ) :
    Complex.erf z = ((2 / Real.sqrt Real.pi : ℝ) : ℂ) *
      ∑' k, ((coefficient .erf k : ℂ) * (-1) ^ k) * z ^ (2 * k + 1) := by
  rw [Complex.erf, seriesC, mul_assoc, ← tsum_mul_left]
  congr 2
  funext k
  rw [neg_pow, ← pow_mul]
  ring

private theorem Si_eq_tsum (z : ℂ) :
    Complex.Si z = ∑' k, ((coefficient .si k : ℂ) * (-1) ^ k) * z ^ (2 * k + 1) := by
  rw [Complex.Si, seriesC, ← tsum_mul_left]
  congr 1
  funext k
  rw [neg_pow, ← pow_mul]
  ring

private theorem norm_ratCast_eq (q : ℚ) : ‖(q : ℂ)‖ = |(q : ℝ)| := by
  rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

private theorem hasDerivAt_erf (z : ℂ) :
    HasDerivAt Complex.erf (((2 / Real.sqrt Real.pi : ℝ) : ℂ) * Complex.exp (-z ^ 2)) z := by
  have hb : ∀ k : ℕ, ‖(coefficient .erf k : ℂ) * (-1) ^ k‖ * (2 * k + 1) ≤ 1 / k.factorial := by
    intro k
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, norm_ratCast_eq,
      coefficient_erf]
    push_cast
    rw [abs_of_nonneg (by positivity)]
    apply le_of_eq; field_simp
  have h := (hasDerivAt_oddSeries _ hb z).const_mul ((2 / Real.sqrt Real.pi : ℝ) : ℂ)
  have hfun : Complex.erf = fun z => ((2 / Real.sqrt Real.pi : ℝ) : ℂ) *
      ∑' k, ((coefficient .erf k : ℂ) * (-1) ^ k) * z ^ (2 * k + 1) := funext erf_eq_tsum
  rw [hfun]
  convert h using 2
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  dsimp only
  congr 1
  funext k
  rw [coefficient_erf, neg_pow, ← pow_mul]
  have : (2 * (k:ℂ) + 1) ≠ 0 := by norm_cast
  push_cast
  field_simp

/-- The entire function `sin z / z`. -/
private noncomputable def sincC (z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1) ^ k * z ^ (2 * k) / ((2 * k + 1).factorial : ℂ)

private theorem hasDerivAt_Si (z : ℂ) : HasDerivAt Complex.Si (sincC z) z := by
  have hb : ∀ k : ℕ, ‖(coefficient .si k : ℂ) * (-1) ^ k‖ * (2 * k + 1) ≤ 1 / k.factorial := by
    intro k
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, norm_ratCast_eq,
      coefficient_si]
    push_cast
    rw [abs_of_nonneg (by positivity)]
    have h1 : (k.factorial : ℝ) ≤ (2 * k + 1).factorial :=
      by exact_mod_cast Nat.factorial_le (by omega)
    have h2 : (0:ℝ) < k.factorial := by positivity
    calc 1 / (((2 * k + 1).factorial : ℝ) * (2 * k + 1)) * (2 * k + 1)
        = 1 / ((2 * k + 1).factorial : ℝ) := by field_simp
      _ ≤ 1 / k.factorial := one_div_le_one_div_of_le h2 h1
  have h := hasDerivAt_oddSeries _ hb z
  have hfun : Complex.Si = fun z =>
      ∑' k, ((coefficient .si k : ℂ) * (-1) ^ k) * z ^ (2 * k + 1) := funext Si_eq_tsum
  rw [hfun]
  convert h using 1
  rw [sincC]
  congr 1
  funext k
  rw [coefficient_si]
  have : (2 * (k:ℂ) + 1) ≠ 0 := by norm_cast
  push_cast
  field_simp

private theorem mul_sincC (z : ℂ) : z * sincC z = Complex.sin z := by
  rw [sincC, ← tsum_mul_left, ← (Complex.hasSum_sin z).tsum_eq]
  congr 1; funext k
  rw [pow_succ]; ring

private theorem sincC_zero : sincC 0 = 1 := by
  rw [sincC, tsum_eq_single 0]
  · simp
  · intro k hk; simp [hk]

private theorem norm_cos_le (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  rw [Complex.cos]
  rw [norm_div, Complex.norm_ofNat]
  have h1 : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.2; simp; exact neg_le_abs _
  have h2 : ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.2; simp; exact le_abs_self _
  have := norm_add_le (Complex.exp (w * Complex.I)) (Complex.exp (-w * Complex.I))
  linarith

private theorem norm_sincC_le (z : ℂ) : ‖sincC z‖ ≤ Real.exp |z.im| := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [sincC_zero]
  have hint : (∫ t in (0:ℝ)..1, Complex.cos (z * t)) = sincC z := by
    have hd : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => Complex.sin (z * t) / z)
        (Complex.cos (z * t)) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => z * (t : ℂ)) z t := by
        simpa using ((hasDerivAt_id (t:ℝ)).ofReal_comp).const_mul z
      have := ((Complex.hasDerivAt_sin (z * t)).comp (t:ℝ) h1).div_const z
      convert this using 1
      · rfl
      · field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ => Complex.cos (z * t)).intervalIntegrable _ _)]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.sin_zero,
      zero_div, sub_zero]
    rw [← mul_sincC z]
    field_simp
  rw [← hint]
  have hb : ∀ t ∈ Set.uIoc (0:ℝ) 1, ‖Complex.cos (z * t)‖ ≤ Real.exp |z.im| := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    refine (norm_cos_le _).trans (Real.exp_le_exp.2 ?_)
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero]
    rw [zero_add, abs_mul, abs_of_pos ht.1]
    nlinarith [abs_nonneg z.im, ht.2]
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this


private theorem hasDerivAt_real_erf (x : ℝ) :
    HasDerivAt Real.erf (2 / Real.sqrt Real.pi * Real.exp (-x ^ 2)) x := by
  have h := (hasDerivAt_erf (x : ℂ)).real_of_complex
  have e1 : (fun y : ℝ => (Complex.erf (y : ℂ)).re) = Real.erf := by
    funext y; rw [erf_ofReal]; simp
  rw [e1] at h
  convert h using 1
  rw [show -(x : ℂ) ^ 2 = ((-x ^ 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

private theorem real_erf_zero : Real.erf 0 = 0 := by simp [Real.erf]

private theorem real_erf_neg (x : ℝ) : Real.erf (-x) = -Real.erf x := by
  simp [Real.erf]

private theorem real_erf_eq_integral (x : ℝ) :
    Real.erf x = 2 / Real.sqrt Real.pi * ∫ t in (0:ℝ)..x, Real.exp (-t ^ 2) := by
  rw [← intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_real_erf t)
    ((by fun_prop : Continuous fun t : ℝ => 2 / Real.sqrt Real.pi * Real.exp (-t ^ 2)).intervalIntegrable _ _)]
  rw [real_erf_zero, sub_zero]

private theorem gaussian_integrable : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
  have := integrable_exp_neg_mul_sq (b := 1) one_pos
  simpa using this

private theorem gaussian_Ioi_zero : ∫ t in Set.Ioi (0:ℝ), Real.exp (-t ^ 2) = Real.sqrt Real.pi / 2 := by
  have := integral_gaussian_Ioi 1
  simpa using this

private theorem real_erf_nonneg_le_one {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.erf x ∧ Real.erf x ≤ 1 := by
  rw [real_erf_eq_integral]
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hI0 : 0 ≤ ∫ t in (0:ℝ)..x, Real.exp (-t ^ 2) :=
    intervalIntegral.integral_nonneg hx (fun t _ => (Real.exp_pos _).le)
  have hI1 : (∫ t in (0:ℝ)..x, Real.exp (-t ^ 2)) ≤ Real.sqrt Real.pi / 2 := by
    rw [intervalIntegral.integral_of_le hx, ← gaussian_Ioi_zero]
    apply setIntegral_mono_set gaussian_integrable.integrableOn
    · exact Eventually.of_forall fun t => (Real.exp_pos _).le
    · exact Set.Ioc_subset_Ioi_self.eventuallyLE
  constructor
  · positivity
  · calc 2 / Real.sqrt Real.pi * ∫ t in (0:ℝ)..x, Real.exp (-t ^ 2)
        ≤ 2 / Real.sqrt Real.pi * (Real.sqrt Real.pi / 2) := by gcongr
      _ = 1 := by field_simp

private theorem real_erf_range (x : ℝ) : -1 ≤ Real.erf x ∧ Real.erf x ≤ 1 := by
  rcases le_total 0 x with hx | hx
  · have := real_erf_nonneg_le_one hx; constructor <;> linarith [this.1, this.2]
  · have := real_erf_nonneg_le_one (neg_nonneg.2 hx)
    rw [real_erf_neg] at this
    constructor <;> linarith [this.1, this.2]

private theorem one_sub_real_erf {x : ℝ} (hx : 0 ≤ x) :
    1 - Real.erf x = 2 / Real.sqrt Real.pi * ∫ t in Set.Ioi x, Real.exp (-t ^ 2) := by
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsplit : (∫ t in Set.Ioi (0:ℝ), Real.exp (-t ^ 2)) =
      (∫ t in (0:ℝ)..x, Real.exp (-t ^ 2)) + ∫ t in Set.Ioi x, Real.exp (-t ^ 2) := by
    rw [intervalIntegral.integral_of_le hx, ← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi gaussian_integrable.integrableOn gaussian_integrable.integrableOn,
      Set.Ioc_union_Ioi_eq_Ioi hx]
  rw [gaussian_Ioi_zero] at hsplit
  rw [real_erf_eq_integral]
  have : (∫ t in Set.Ioi x, Real.exp (-t ^ 2)) = Real.sqrt Real.pi / 2 -
      ∫ t in (0:ℝ)..x, Real.exp (-t ^ 2) := by linarith
  rw [this]; field_simp

private theorem gaussian_tail_le {x : ℝ} (hx : 0 < x) :
    ∫ t in Set.Ioi x, Real.exp (-t ^ 2) ≤ Real.exp (-x ^ 2) / (2 * x) := by
  have hint : IntegrableOn (fun t => t / x * Real.exp (-t ^ 2)) (Set.Ioi x) := by
    have h := (integrable_mul_exp_neg_mul_sq (b := 1) one_pos).div_const x
    refine (h.integrableOn).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp; ring
  have hmaj : ∫ t in Set.Ioi x, t / x * Real.exp (-t ^ 2) = Real.exp (-x ^ 2) / (2 * x) := by
    have hd : ∀ t, HasDerivAt (fun t => -Real.exp (-t ^ 2) / (2 * x))
        (t / x * Real.exp (-t ^ 2)) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => -t ^ 2) (-(2 * t)) t := by
        have := (hasDerivAt_pow 2 t).neg
        convert this using 1; push_cast; ring
      have := (h1.exp.neg).div_const (2 * x)
      convert this using 1
      field_simp
    have hlim : Tendsto (fun t => -Real.exp (-t ^ 2) / (2 * x)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => Real.exp (-t ^ 2)) atTop (𝓝 0) := by
        have := (Real.tendsto_exp_neg_atTop_nhds_zero).comp
          (tendsto_pow_atTop (α := ℝ) (n := 2) two_ne_zero)
        exact this
      simpa using (h1.neg).div_const (2 * x)
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (hd x).continuousAt.continuousWithinAt
      (fun t _ => hd t) hint hlim]
    ring
  rw [← hmaj]
  apply setIntegral_mono_on gaussian_integrable.integrableOn hint measurableSet_Ioi
  intro t ht
  have h1 : 1 ≤ t / x := by rw [le_div_iff₀ hx]; linarith [ht.out]
  nlinarith [Real.exp_pos (-t ^ 2)]

private theorem real_erf_tail {x : ℝ} (hx : 0 < x) :
    |Real.erf x - 1| ≤ Real.exp (-x ^ 2) / x := by
  have hpi : 1 ≤ Real.sqrt Real.pi := by
    rw [Real.one_le_sqrt]; linarith [Real.pi_gt_three]
  have hle := (real_erf_range x).2
  rw [abs_sub_comm, abs_of_nonneg (by linarith), one_sub_real_erf hx.le]
  have ht := gaussian_tail_le hx
  have hI : 0 ≤ ∫ t in Set.Ioi x, Real.exp (-t ^ 2) :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => (Real.exp_pos _).le)
  calc 2 / Real.sqrt Real.pi * ∫ t in Set.Ioi x, Real.exp (-t ^ 2)
      ≤ 2 / 1 * (Real.exp (-x ^ 2) / (2 * x)) := by
        gcongr
    _ = Real.exp (-x ^ 2) / x := by field_simp


private theorem coefficient_airy_le (kind : SeriesKind) (hk : kind = .airy0 ∨ kind = .airy1) (k : ℕ) :
    coefficient kind k ≤ 1 / (2 * k).factorial := by
  induction k with
  | zero => simp [coefficient]
  | succ k ih =>
    simp only [coefficient]
    have h0 := coefficient_nonneg kind k
    have hnum : (kind.num k : ℚ) = 1 := by rcases hk with rfl | rfl <;> simp [SeriesKind.num]
    have hden : ((2 * k + 1) * (2 * k + 2) : ℚ) ≤ kind.den k := by
      rcases hk with rfl | rfl <;> simp only [SeriesKind.den] <;> push_cast <;> nlinarith
    rw [hnum, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    have hd : (0:ℚ) < kind.den k := den_pos kind k
    push_cast
    calc coefficient kind k * 1 / (kind.den k : ℚ) ≤ 1 / (2 * k).factorial / ((2 * k + 1) * (2 * k + 2)) := by
          rw [mul_one]
          apply div_le_div₀ (by positivity) ih (by positivity) hden
      _ = _ := by field_simp; ring

private theorem norm_seriesC_airy_le (kind : SeriesKind) (hk : kind = .airy0 ∨ kind = .airy1) (w : ℂ) :
    ‖seriesC kind w‖ ≤ Real.exp (Real.sqrt ‖w‖) := by
  set u := Real.sqrt ‖w‖
  have hu2 : u ^ 2 = ‖w‖ := Real.sq_sqrt (norm_nonneg w)
  have hterm : ∀ k : ℕ, ‖(coefficient kind k : ℂ) * w ^ k‖ ≤ u ^ (2 * k) / (2 * k).factorial := by
    intro k
    rw [norm_mul, norm_pow, norm_ratCast_eq, abs_of_nonneg (by exact_mod_cast coefficient_nonneg kind k),
      pow_mul, hu2]
    have h2 : ((coefficient kind k : ℚ) : ℝ) ≤ ((1 / ((2 * k).factorial : ℚ) : ℚ) : ℝ) :=
      Rat.cast_le.mpr (coefficient_airy_le kind hk k)
    push_cast at h2
    calc (coefficient kind k : ℝ) * ‖w‖ ^ k ≤ 1 / (2 * k).factorial * ‖w‖ ^ k := by gcongr
      _ = _ := by ring
  have hs : Summable (fun n : ℕ => u ^ n / n.factorial) := Real.summable_pow_div_factorial u
  have hs2 : Summable (fun k : ℕ => u ^ (2 * k) / (2 * k).factorial) :=
    hs.comp_injective (fun a b h => by simpa using h)
  rw [seriesC]
  refine (norm_tsum_le_tsum_norm (summable_seriesC kind w).norm).trans ?_
  refine ((summable_seriesC kind w).norm.tsum_le_tsum hterm hs2).trans ?_
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  exact hs2.tsum_le_tsum_of_inj (fun k => 2 * k) (fun a b h => by simpa using h)
    (fun _ _ => by positivity) (fun _ => le_rfl) hs


private theorem Gamma_le_one_of_mem {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 2) : Real.Gamma s ≤ 1 := by
  have hc := Real.convexOn_Gamma
  have := hc.2 (show (1:ℝ) ∈ Set.Ioi 0 by norm_num) (show (2:ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (0:ℝ) ≤ 2 - s by linarith) (show (0:ℝ) ≤ s - 1 by linarith) (by ring)
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at this
  have e : (2 - s) * 1 + (s - 1) * 2 = s := by ring
  rw [e] at this; linarith

private theorem Gamma_third_mul : Real.Gamma (1/3) * Real.Gamma (2/3) = 2 * Real.pi / Real.sqrt 3 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1/3)
  rw [show (1:ℝ) - 1/3 = 2/3 by norm_num, show Real.pi * (1/3) = Real.pi / 3 by ring,
    Real.sin_pi_div_three] at h
  rw [h]; field_simp

private theorem Gamma_one_third_le : Real.Gamma (1/3) ≤ 3 := by
  have h := Real.Gamma_add_one (s := 1/3) (by norm_num)
  have := Gamma_le_one_of_mem (s := 1/3 + 1) (by norm_num) (by norm_num)
  rw [h] at this; linarith

private theorem Gamma_two_third_le : Real.Gamma (2/3) ≤ 3/2 := by
  have h := Real.Gamma_add_one (s := 2/3) (by norm_num)
  have := Gamma_le_one_of_mem (s := 2/3 + 1) (by norm_num) (by norm_num)
  rw [h] at this; linarith

private theorem two_pi_div_sqrt_three_ge : 3 ≤ 2 * Real.pi / Real.sqrt 3 := by
  have h3 : Real.sqrt 3 < 1.7321 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpos : 0 < Real.sqrt 3 := by positivity
  rw [le_div_iff₀ hpos]
  nlinarith [Real.pi_gt_d2]

private theorem Gamma_one_third_ge : 1 ≤ Real.Gamma (1/3) := by
  have h := Gamma_third_mul
  have h2 := Gamma_two_third_le
  have hp : 0 < Real.Gamma (2/3) := Real.Gamma_pos_of_pos (by norm_num)
  have := two_pi_div_sqrt_three_ge
  nlinarith

private theorem Gamma_two_third_ge : 1 ≤ Real.Gamma (2/3) := by
  have h := Gamma_third_mul
  have h2 := Gamma_one_third_le
  have hp : 0 < Real.Gamma (1/3) := Real.Gamma_pos_of_pos (by norm_num)
  have := two_pi_div_sqrt_three_ge
  nlinarith

private theorem abs_airyA_le : |airyA| ≤ 1 := by
  have h1 : 1 ≤ (3:ℝ) ^ (2/3 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have h2 := Gamma_two_third_ge
  unfold airyA
  rw [abs_of_pos (by positivity)]
  rw [div_le_one (by positivity)]
  nlinarith

private theorem abs_airyB_le : |airyB| ≤ 1 := by
  have h1 : 1 ≤ (3:ℝ) ^ (1/3 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have h2 := Gamma_one_third_ge
  unfold airyB
  rw [neg_div, abs_neg, abs_of_pos (by positivity)]
  rw [div_le_one (by positivity)]
  nlinarith


private theorem norm_erf_bound (z : ℂ) : ‖Complex.erf z‖ ≤ 1 + 2*|z.im| * Real.exp (z.im^2) := by
  set x := z.re
  set y := z.im
  have hpi : 1 ≤ Real.sqrt Real.pi := by
    rw [Real.one_le_sqrt]; linarith [Real.pi_gt_three]
  have hseg : ∀ w ∈ segment ℝ (x : ℂ) z, ‖((2 / Real.sqrt Real.pi : ℝ) : ℂ) *
      Complex.exp (-w ^ 2)‖ ≤ 2 * Real.exp (y ^ 2) := by
    intro w hw
    rw [segment_eq_image] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      Complex.norm_exp]
    have hre : (-((1 - t) • (x : ℂ) + t • z) ^ 2).re = -(x ^ 2) + (t * y) ^ 2 := by
      simp only [Complex.real_smul]
      simp [sq, x, y]; ring
    rw [hre]
    have h1 : 2 / Real.sqrt Real.pi ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h2 : Real.exp (-(x ^ 2) + (t * y) ^ 2) ≤ Real.exp (y ^ 2) := by
      apply Real.exp_le_exp.2
      have : (t * y) ^ 2 ≤ y ^ 2 := by
        rw [mul_pow]; nlinarith [ht.1, ht.2, sq_nonneg y, mul_le_mul ht.2 ht.2 ht.1 zero_le_one]
      nlinarith [sq_nonneg x]
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
  have hmvt := (convex_segment (x : ℂ) z).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Complex.erf) (fun w _ => (hasDerivAt_erf w).hasDerivWithinAt) hseg
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  have hzI : z - (x : ℂ) = (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [x, y]
  have hzx : ‖z - (x : ℂ)‖ = |y| := by
    rw [hzI, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hzx] at hmvt
  have hx : ‖Complex.erf (x : ℂ)‖ ≤ 1 := by
    rw [erf_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact real_erf_range x
  calc ‖Complex.erf z‖ ≤ ‖Complex.erf (x : ℂ)‖ + ‖Complex.erf z - Complex.erf (x : ℂ)‖ := by
        have := norm_add_le (Complex.erf (x : ℂ)) (Complex.erf z - Complex.erf (x : ℂ))
        simpa using this
    _ ≤ 1 + 2 * Real.exp (y ^ 2) * |y| := add_le_add hx hmvt
    _ = _ := by ring

private theorem norm_Si_bound (z : ℂ) : ‖Complex.Si z‖ ≤ ‖z‖ * Real.exp |z.im| := by
  have hseg : ∀ w ∈ segment ℝ (0 : ℂ) z, ‖sincC w‖ ≤ Real.exp |z.im| := by
    intro w hw
    rw [segment_eq_image] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    refine (norm_sincC_le _).trans (Real.exp_le_exp.2 ?_)
    simp only [smul_zero, zero_add, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    rw [abs_mul, abs_of_nonneg ht.1]
    nlinarith [abs_nonneg z.im, ht.2]
  have hmvt := (convex_segment (0 : ℂ) z).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Complex.Si) (fun w _ => (hasDerivAt_Si w).hasDerivWithinAt) hseg
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  have h0 : Complex.Si 0 = 0 := by simp [Complex.Si]
  rw [h0, sub_zero, sub_zero] at hmvt
  linarith [mul_comm (Real.exp |z.im|) ‖z‖]

private theorem norm_airyAi_bound (z : ℂ) : ‖Complex.airyAi z‖ ≤ (1+‖z‖) * Real.exp (‖z‖^2+1) := by
  have hr := norm_nonneg z
  have hsq : Real.sqrt ‖z ^ 3‖ ≤ ‖z‖ ^ 2 + 1 := by
    rw [norm_pow, Real.sqrt_le_left (by positivity)]
    rcases le_total ‖z‖ 1 with h | h
    · have : ‖z‖ ^ 3 ≤ 1 := pow_le_one₀ hr h
      nlinarith [sq_nonneg ‖z‖, pow_nonneg hr 4]
    · nlinarith [sq_nonneg ‖z‖, pow_nonneg hr 4, mul_le_mul_of_nonneg_left h (pow_nonneg hr 3)]
  have hE : Real.exp (Real.sqrt ‖z ^ 3‖) ≤ Real.exp (‖z‖ ^ 2 + 1) := Real.exp_le_exp.2 hsq
  have h0 := (norm_seriesC_airy_le .airy0 (Or.inl rfl) (z ^ 3)).trans hE
  have h1 := (norm_seriesC_airy_le .airy1 (Or.inr rfl) (z ^ 3)).trans hE
  have hA : ‖(airyA : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_airyA_le
  have hB : ‖(airyB : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_airyB_le
  unfold Complex.airyAi
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul]
  have he := Real.exp_pos (‖z‖ ^ 2 + 1)
  calc ‖(airyA : ℂ)‖ * ‖seriesC SeriesKind.airy0 (z ^ 3)‖ +
        ‖(airyB : ℂ)‖ * ‖z‖ * ‖seriesC SeriesKind.airy1 (z ^ 3)‖
      ≤ 1 * Real.exp (‖z‖ ^ 2 + 1) + 1 * ‖z‖ * Real.exp (‖z‖ ^ 2 + 1) := by
        gcongr
    _ = _ := by ring

end SpecialFunctions


end

section
/- Auxiliary proofs ported from SpecialFunctionsAiry.lean. -/

/-! The Airy differential equation for the power-series definition of `Ai`. -/

open Filter Topology

namespace SpecialFunctions

/-- A complex power series with coefficients `d`. -/
private noncomputable def pser (d : ℕ → ℂ) (w : ℂ) : ℂ := ∑' k, d k * w ^ k

/-- Coefficients of the formal derivative. -/
private def dsh (d : ℕ → ℂ) (k : ℕ) : ℂ := ((k : ℂ) + 1) * d (k + 1)

/-- Factorially decaying coefficients. -/
private def FacBdd (d : ℕ → ℂ) : Prop := ∀ k, ‖d k‖ ≤ 1 / k.factorial

private theorem FacBdd.dsh {d : ℕ → ℂ} (hd : FacBdd d) : FacBdd (dsh d) := by
  intro k
  rw [SpecialFunctions.dsh, norm_mul]
  have h1 : ‖((k : ℂ) + 1)‖ = k + 1 := by
    rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  rw [h1]
  calc (k + 1 : ℝ) * ‖d (k + 1)‖ ≤ (k + 1) * (1 / (k + 1).factorial) := by
        gcongr; exact hd (k + 1)
    _ = 1 / k.factorial := by
        rw [Nat.factorial_succ]; push_cast; field_simp

private theorem FacBdd.summable {d : ℕ → ℂ} (hd : FacBdd d) (w : ℂ) :
    Summable (fun k => d k * w ^ k) := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖w‖) (fun k => ?_)
  rw [norm_mul, norm_pow]
  calc ‖d k‖ * ‖w‖ ^ k ≤ 1 / k.factorial * ‖w‖ ^ k := by gcongr; exact hd k
    _ = _ := by ring

private theorem pser_eq_zero_add {d : ℕ → ℂ} (hd : FacBdd d) (w : ℂ) :
    pser d w = d 0 + ∑' k, d (k + 1) * w ^ (k + 1) := by
  rw [pser, (hd.summable w).tsum_eq_zero_add]; simp

private theorem hasDerivAt_pser {d : ℕ → ℂ} (hd : FacBdd d) (w : ℂ) :
    HasDerivAt (pser d) (pser (dsh d) w) w := by
  set R := ‖w‖ + 1
  have hR : 0 < R := by positivity
  have hfun : pser d = fun z => d 0 + ∑' k, d (k + 1) * z ^ (k + 1) :=
    funext (pser_eq_zero_add hd)
  rw [hfun]
  refine HasDerivAt.const_add _ ?_
  refine hasDerivAt_tsum_of_isPreconnected (u := fun k : ℕ => R ^ k / k.factorial)
    (g := fun k (y : ℂ) => d (k + 1) * y ^ (k + 1))
    (g' := fun k (y : ℂ) => dsh d k * y ^ k)
    (t := Metric.ball (0:ℂ) R) (y₀ := (0:ℂ)) (Real.summable_pow_div_factorial R)
    Metric.isOpen_ball (convex_ball (0:ℂ) R).isPreconnected
    ?_ ?_ (Metric.mem_ball_self hR) ?_ (by simp [R])
  · intro k y _
    have := (hasDerivAt_pow (k + 1) y).const_mul (d (k + 1))
    convert this using 1
    simp only [SpecialFunctions.dsh, Nat.add_sub_cancel]; push_cast; ring
  · intro k y hy
    rw [mem_ball_zero_iff] at hy
    rw [norm_mul, norm_pow]
    calc ‖dsh d k‖ * ‖y‖ ^ k ≤ 1 / k.factorial * R ^ k := by
          gcongr; exact hd.dsh k
      _ = _ := by ring
  · simp

/-- `w * pser d w` as a power series. -/
private theorem mul_pser (d : ℕ → ℂ) (w : ℂ) :
    w * pser d w = ∑' k, d k * w ^ (k + 1) := by
  rw [pser, ← tsum_mul_left]
  congr 1; funext k; ring

/-- Identity `a * pser d₁ + b * w * pser d₂ = pser d₀` from a coefficient identity. -/
private theorem pser_combo {d₀ d₁ d₂ : ℕ → ℂ} (h₀ : FacBdd d₀) (h₁ : FacBdd d₁) (h₂ : FacBdd d₂)
    (a b : ℂ) (hz : a * d₁ 0 = d₀ 0)
    (hs : ∀ k, a * d₁ (k + 1) + b * d₂ k = d₀ (k + 1)) (w : ℂ) :
    a * pser d₁ w + b * (w * pser d₂ w) = pser d₀ w := by
  rw [mul_pser d₂, pser_eq_zero_add h₁, pser_eq_zero_add h₀, mul_add, add_assoc,
    ← tsum_mul_left, ← tsum_mul_left]
  have s1 : Summable fun k => a * (d₁ (k + 1) * w ^ (k + 1)) :=
    ((h₁.summable w).comp_injective (add_left_injective 1)).mul_left a
  have s2 : Summable fun k => b * (d₂ k * w ^ (k + 1)) := by
    have := ((h₂.summable w).mul_right w).mul_left b
    refine this.congr fun k => ?_
    rw [pow_succ]; ring
  rw [← (s1.tsum_add s2), hz]
  congr 1
  congr 1; funext k
  rw [← hs k]; ring

/-- Complex coefficients of the Airy series. -/
private noncomputable def cA (kind : SeriesKind) (k : ℕ) : ℂ := (coefficient kind k : ℂ)

private theorem facBdd_cA (kind : SeriesKind) : FacBdd (cA kind) := by
  intro k
  rw [cA, norm_ratCast_eq]
  exact coefficient_abs_le kind k

private theorem seriesC_eq_pser (kind : SeriesKind) : seriesC kind = pser (cA kind) := rfl

private theorem coefficient_succ (kind : SeriesKind) (k : ℕ) :
    coefficient kind (k + 1) = coefficient kind k * kind.num k / kind.den k := rfl

private theorem airy0_combo (w : ℂ) :
    6 * pser (dsh (cA .airy0)) w + 9 * (w * pser (dsh (dsh (cA .airy0))) w) =
      pser (cA .airy0) w := by
  refine pser_combo (facBdd_cA _) (facBdd_cA _).dsh (facBdd_cA _).dsh.dsh 6 9 ?_ ?_ w
  · simp [dsh, cA, coefficient, SeriesKind.num, SeriesKind.den]
  · intro k
    simp only [dsh, cA, coefficient_succ (k := k + 1), SeriesKind.num, SeriesKind.den]
    push_cast
    generalize (coefficient SeriesKind.airy0 (k + 1) : ℂ) = q
    have h : ((3 * ((k:ℝ) + 1) + 3) * (3 * ((k:ℝ) + 1) + 2)) ≠ 0 := by positivity
    have : ((3 * ((k:ℂ) + 1) + 3) * (3 * ((k:ℂ) + 1) + 2)) ≠ 0 := by exact_mod_cast h
    rw [mul_one]
    generalize hD : ((3 * ((k:ℂ) + 1) + 3) * (3 * ((k:ℂ) + 1) + 2)) = D at this
    have e : ((k:ℂ) + 1 + 1) * (6 + 9 * ((k:ℂ) + 1)) = D := by rw [← hD]; ring
    rw [show (6:ℂ) * (((k:ℂ) + 1 + 1) * (q / D)) + 9 * (((k:ℂ) + 1) * (((k:ℂ) + 1 + 1) * (q / D)))
      = q * ((((k:ℂ) + 1 + 1) * (6 + 9 * ((k:ℂ) + 1))) / D) by ring, e, div_self this, mul_one]

private theorem airy1_combo (w : ℂ) :
    12 * pser (dsh (cA .airy1)) w + 9 * (w * pser (dsh (dsh (cA .airy1))) w) =
      pser (cA .airy1) w := by
  refine pser_combo (facBdd_cA _) (facBdd_cA _).dsh (facBdd_cA _).dsh.dsh 12 9 ?_ ?_ w
  · simp [dsh, cA, coefficient, SeriesKind.num, SeriesKind.den]
  · intro k
    simp only [dsh, cA, coefficient_succ (k := k + 1), SeriesKind.num, SeriesKind.den]
    push_cast
    generalize (coefficient SeriesKind.airy1 (k + 1) : ℂ) = q
    have h : ((3 * ((k:ℝ) + 1) + 3) * (3 * ((k:ℝ) + 1) + 4)) ≠ 0 := by positivity
    have : ((3 * ((k:ℂ) + 1) + 3) * (3 * ((k:ℂ) + 1) + 4)) ≠ 0 := by exact_mod_cast h
    rw [mul_one]
    generalize hD : ((3 * ((k:ℂ) + 1) + 3) * (3 * ((k:ℂ) + 1) + 4)) = D at this
    have e : ((k:ℂ) + 1 + 1) * (12 + 9 * ((k:ℂ) + 1)) = D := by rw [← hD]; ring
    rw [show (12:ℂ) * (((k:ℂ) + 1 + 1) * (q / D)) + 9 * (((k:ℂ) + 1) * (((k:ℂ) + 1 + 1) * (q / D)))
      = q * ((((k:ℂ) + 1 + 1) * (12 + 9 * ((k:ℂ) + 1))) / D) by ring, e, div_self this, mul_one]

/-- The derivative of the complex Airy function. -/
private noncomputable def airyD (z : ℂ) : ℂ :=
  (airyA : ℂ) * (3 * z ^ 2 * pser (dsh (cA .airy0)) (z ^ 3)) +
    (airyB : ℂ) * (pser (cA .airy1) (z ^ 3) + 3 * z ^ 3 * pser (dsh (cA .airy1)) (z ^ 3))

private theorem hasDerivAt_pser_cube {d : ℕ → ℂ} (hd : FacBdd d) (z : ℂ) :
    HasDerivAt (fun z => pser d (z ^ 3)) (3 * z ^ 2 * pser (dsh d) (z ^ 3)) z := by
  have h := (hasDerivAt_pser hd (z ^ 3)).comp z (hasDerivAt_pow 3 z)
  rw [Function.comp_def] at h
  convert h using 1
  push_cast; ring

private theorem hasDerivAt_airyAi (z : ℂ) : HasDerivAt Complex.airyAi (airyD z) z := by
  have h0 := (hasDerivAt_pser_cube (facBdd_cA .airy0) z).const_mul (airyA : ℂ)
  have h1 := ((hasDerivAt_id z).mul (hasDerivAt_pser_cube (facBdd_cA .airy1) z)).const_mul
    (airyB : ℂ)
  have e : Complex.airyAi = fun z => (airyA : ℂ) * pser (cA .airy0) (z ^ 3) +
      (airyB : ℂ) * (id z * pser (cA .airy1) (z ^ 3)) := by
    funext z; simp only [Complex.airyAi, seriesC_eq_pser, id]; ring
  rw [e]
  convert h0.add h1 using 1
  simp only [airyD, id]; ring

private theorem norm_pser_dsh_airy_le (kind : SeriesKind) (hk : kind = .airy0 ∨ kind = .airy1) (w : ℂ) :
    ‖pser (dsh (cA kind)) w‖ ≤ Real.exp (Real.sqrt ‖w‖) := by
  set u := Real.sqrt ‖w‖
  have hu2 : u ^ 2 = ‖w‖ := Real.sq_sqrt (norm_nonneg w)
  have hterm : ∀ k : ℕ, ‖dsh (cA kind) k * w ^ k‖ ≤ u ^ (2 * k) / (2 * k).factorial := by
    intro k
    rw [norm_mul, norm_pow, pow_mul, hu2, dsh, cA, norm_mul, norm_ratCast_eq,
      abs_of_nonneg (by exact_mod_cast coefficient_nonneg kind (k+1))]
    have h2 : ((coefficient kind (k+1) : ℚ) : ℝ) ≤ ((1 / ((2 * (k+1)).factorial : ℚ) : ℚ) : ℝ) :=
      Rat.cast_le.mpr (coefficient_airy_le kind hk (k+1))
    push_cast at h2
    have hn : ‖((k : ℂ) + 1)‖ = k + 1 := by
      rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    rw [hn]
    have hf : ((2 * (k+1)).factorial : ℝ) = (2*k+2) * (2*k+1) * (2*k).factorial := by
      rw [show 2 * (k+1) = (2*k+1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [hf] at h2
    have hfp : (0:ℝ) < (2*k).factorial := by positivity
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hc : ((k:ℝ) + 1) * (coefficient kind (k+1) : ℝ) ≤ 1 / (2*k).factorial := by
      calc ((k:ℝ) + 1) * (coefficient kind (k+1) : ℝ)
          ≤ ((k:ℝ) + 1) * (1 / ((2*k+2) * (2*k+1) * (2*k).factorial)) := by gcongr
        _ ≤ 1 / (2*k).factorial := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) hfp]
          nlinarith [mul_nonneg hk0 hfp.le, mul_nonneg (mul_nonneg hk0 hk0) hfp.le]
    calc ((k:ℝ) + 1) * (coefficient kind (k+1) : ℝ) * ‖w‖ ^ k ≤ 1 / (2 * k).factorial * ‖w‖ ^ k := by
          gcongr
      _ = _ := by ring
  have hs : Summable (fun n : ℕ => u ^ n / n.factorial) := Real.summable_pow_div_factorial u
  have hs2 : Summable (fun k : ℕ => u ^ (2 * k) / (2 * k).factorial) :=
    hs.comp_injective (fun a b h => by simpa using h)
  rw [pser]
  have hsum := ((facBdd_cA kind).dsh.summable w)
  refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
  refine (hsum.norm.tsum_le_tsum hterm hs2).trans ?_
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  exact hs2.tsum_le_tsum_of_inj (fun k => 2 * k) (fun a b h => by simpa using h)
    (fun _ _ => by positivity) (fun _ => le_rfl) hs

private theorem norm_airyD_le (z : ℂ) (r : ℝ) (hz : ‖z‖ ≤ r) :
    ‖airyD z‖ ≤ (2 + r)^2 * Real.exp (r^2 + 1) := by
  have hn := norm_nonneg z
  have hr : 0 ≤ r := hn.trans hz
  set a := Real.exp ((r^2 + r)/2)
  have hsq : Real.sqrt ‖z ^ 3‖ ≤ (r^2 + r)/2 := by
    rw [norm_pow, Real.sqrt_le_left (by positivity)]
    have : ‖z‖^3 ≤ r^3 := pow_le_pow_left₀ hn hz 3
    nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg (r-1))]
  have hE : Real.exp (Real.sqrt ‖z ^ 3‖) ≤ a := Real.exp_le_exp.2 hsq
  have h0 := (norm_pser_dsh_airy_le .airy0 (Or.inl rfl) (z ^ 3)).trans hE
  have h1' := (norm_pser_dsh_airy_le .airy1 (Or.inr rfl) (z ^ 3)).trans hE
  have h1 := (norm_seriesC_airy_le .airy1 (Or.inr rfl) (z ^ 3)).trans hE
  rw [seriesC_eq_pser] at h1
  have hA : ‖(airyA : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_airyA_le
  have hB : ‖(airyB : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_airyB_le
  have ha : 0 ≤ a := (Real.exp_pos _).le
  have hz2 : ‖z‖^2 ≤ r^2 := pow_le_pow_left₀ hn hz 2
  have hz3 : ‖z‖^3 ≤ r^3 := pow_le_pow_left₀ hn hz 3
  have h3 : ‖(3:ℂ)‖ = 3 := by norm_num
  have hbound : ‖airyD z‖ ≤ (1 + 3*r^2 + 3*r^3) * a := by
    unfold airyD
    have e1 : ‖(airyA : ℂ) * (3 * z^2 * pser (dsh (cA .airy0)) (z ^ 3))‖ ≤ 3 * r^2 * a := by
      rw [norm_mul, norm_mul, norm_mul, norm_pow, h3]
      calc _ ≤ 1 * (3 * r^2 * a) := by gcongr
        _ = _ := one_mul _
    have e2 : ‖(airyB : ℂ) * (pser (cA .airy1) (z ^ 3) +
        3 * z ^ 3 * pser (dsh (cA .airy1)) (z ^ 3))‖ ≤ a + 3 * r^3 * a := by
      rw [norm_mul]
      have : ‖pser (cA .airy1) (z ^ 3) + 3 * z ^ 3 * pser (dsh (cA .airy1)) (z ^ 3)‖ ≤
          a + 3 * r^3 * a := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_pow, h3]
        gcongr
      calc _ ≤ 1 * (a + 3 * r^3 * a) := by gcongr
        _ = _ := one_mul _
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ 3 * r^2 * a + (a + 3 * r^3 * a) := add_le_add e1 e2
      _ = _ := by ring
  have hexp : Real.exp (r^2 + 1) = a * Real.exp ((r^2 - r)/2 + 1) := by
    rw [← Real.exp_add]; congr 1; ring
  have hy : 0 ≤ (r^2 - r)/2 + 1 := by nlinarith [sq_nonneg (r - 1/2)]
  have hq := Real.quadratic_le_exp_of_nonneg hy
  have hpoly : 1 + 3*r^2 + 3*r^3 ≤ (2+r)^2 * (1 + ((r^2-r)/2+1) + ((r^2-r)/2+1)^2/2) := by
    nlinarith [sq_nonneg (r-1), sq_nonneg (r^2-2*r), mul_nonneg hr (sq_nonneg (r-1)),
      pow_nonneg hr 3, pow_nonneg hr 4, mul_nonneg (pow_nonneg hr 2) (sq_nonneg (r-1)),
      mul_nonneg (pow_nonneg hr 2) (sq_nonneg (r-2))]
  refine hbound.trans ?_
  rw [hexp]
  calc (1 + 3*r^2 + 3*r^3) * a ≤ ((2+r)^2 * Real.exp ((r^2 - r)/2 + 1)) * a := by
        gcongr
        exact hpoly.trans (by gcongr)
    _ = _ := by ring

/-- Derivative bounds for the three complex special functions, exposed for
the interval evaluator's Lipschitz transport theorem. -/
theorem complex_derivative_bounds (z : ℂ) (r : ℝ) (hz : ‖z‖ ≤ r) :
    (HasDerivAt Complex.erf (deriv Complex.erf z) z ∧
      ‖deriv Complex.erf z‖ ≤ 2 * Real.exp (r^2)) ∧
    (HasDerivAt Complex.Si (deriv Complex.Si z) z ∧
      ‖deriv Complex.Si z‖ ≤ Real.exp r) ∧
    (HasDerivAt Complex.airyAi (deriv Complex.airyAi z) z ∧
      ‖deriv Complex.airyAi z‖ ≤ (2+r)^2 * Real.exp (r^2+1)) := by
  have he := hasDerivAt_erf z
  have hs := hasDerivAt_Si z
  have ha := hasDerivAt_airyAi z
  have he' : HasDerivAt Complex.erf (deriv Complex.erf z) z := by
    rw [he.deriv]
    exact he
  have hs' : HasDerivAt Complex.Si (deriv Complex.Si z) z := by
    rw [hs.deriv]
    exact hs
  have ha' : HasDerivAt Complex.airyAi (deriv Complex.airyAi z) z := by
    rw [ha.deriv]
    exact ha
  have hpi : 1 ≤ Real.sqrt Real.pi := by
    rw [Real.one_le_sqrt]
    linarith [Real.pi_gt_three]
  have h2 : 2 / Real.sqrt Real.pi ≤ 2 := div_le_self (by norm_num) hpi
  have hre : (-z ^ 2).re ≤ r ^ 2 := by
    calc
      (-z ^ 2).re ≤ ‖-z ^ 2‖ := Complex.re_le_norm _
      _ = ‖z‖ ^ 2 := by rw [norm_neg, norm_pow]
      _ ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hexp : Real.exp ((-z ^ 2).re) ≤ Real.exp (r ^ 2) :=
    Real.exp_le_exp.mpr hre
  have he_bound : ‖deriv Complex.erf z‖ ≤ 2 * Real.exp (r ^ 2) := by
    rw [he.deriv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), Complex.norm_exp]
    exact (mul_le_mul_of_nonneg_left hexp (by positivity)).trans
      (mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _))
  have hs_bound : ‖deriv Complex.Si z‖ ≤ Real.exp r := by
    rw [hs.deriv]
    exact (norm_sincC_le z).trans
      (Real.exp_le_exp.mpr ((Complex.abs_im_le_norm z).trans hz))
  have ha_bound : ‖deriv Complex.airyAi z‖ ≤ (2+r)^2 * Real.exp (r^2+1) := by
    rw [ha.deriv]
    exact norm_airyD_le z r hz
  exact ⟨⟨he', he_bound⟩, ⟨⟨hs', hs_bound⟩, ⟨ha', ha_bound⟩⟩⟩

private theorem hasDerivAt_airyD (z : ℂ) : HasDerivAt airyD (z * Complex.airyAi z) z := by
  have hc0 := facBdd_cA .airy0
  have hc1 := facBdd_cA .airy1
  have h0 := (((hasDerivAt_pow 2 z).const_mul (3:ℂ)).mul
    (hasDerivAt_pser_cube hc0.dsh z)).const_mul (airyA : ℂ)
  have h1 := ((hasDerivAt_pser_cube hc1 z).add (((hasDerivAt_pow 3 z).const_mul (3:ℂ)).mul
    (hasDerivAt_pser_cube hc1.dsh z))).const_mul (airyB : ℂ)
  have e : airyD = fun z => (airyA : ℂ) * ((3 * z ^ 2) * pser (dsh (cA .airy0)) (z ^ 3)) +
      (airyB : ℂ) * (pser (cA .airy1) (z ^ 3) + (3 * z ^ 3) * pser (dsh (cA .airy1)) (z ^ 3)) := by
    funext z; simp only [airyD]
  rw [e]
  convert h0.add h1 using 1
  have a0 := airy0_combo (z ^ 3)
  have a1 := airy1_combo (z ^ 3)
  simp only [Complex.airyAi, seriesC_eq_pser]
  rw [← a0, ← a1]
  push_cast
  ring

private theorem pser_zero (d : ℕ → ℂ) : pser d 0 = d 0 := by
  rw [pser, tsum_eq_single 0]
  · simp
  · intro b hb; simp [hb]

private theorem airyAi_zero : Complex.airyAi 0 = airyA := by
  simp [Complex.airyAi, seriesC_eq_pser, pser_zero, cA, coefficient]

private theorem airyD_zero : airyD 0 = airyB := by
  simp [airyD, pser_zero, cA, coefficient]

/-- The derivative of the real Airy function. -/
private noncomputable def airyDR (x : ℝ) : ℝ := (airyD x).re

private theorem hasDerivAt_real_airyAi (x : ℝ) : HasDerivAt Real.airyAi (airyDR x) x := by
  have h := (hasDerivAt_airyAi (x : ℂ)).real_of_complex
  have e : (fun y : ℝ => (Complex.airyAi (y : ℂ)).re) = Real.airyAi := by
    funext y; rw [airyAi_ofReal]; simp
  rwa [e] at h

private theorem hasDerivAt_airyDR (x : ℝ) : HasDerivAt airyDR (x * Real.airyAi x) x := by
  have h := (hasDerivAt_airyD (x : ℂ)).real_of_complex
  rw [Complex.re_ofReal_mul, airyAi_ofReal, Complex.ofReal_re] at h
  exact h

private theorem airyD_ofReal (x : ℝ) : airyD x = (airyDR x : ℂ) := by
  have h1 := (hasDerivAt_airyAi (x : ℂ)).comp_ofReal
  have h2 := (hasDerivAt_real_airyAi x).ofReal_comp
  have e : (fun y : ℝ => Complex.airyAi (y : ℂ)) = fun y => (Real.airyAi y : ℂ) := by
    funext y; rw [airyAi_ofReal]
  rw [e] at h1
  exact h1.unique h2

private theorem real_airyAi_zero : Real.airyAi 0 = airyA := by
  have := airyAi_ofReal 0
  rw [Complex.ofReal_zero, airyAi_zero] at this
  exact_mod_cast this.symm

private theorem airyDR_zero : airyDR 0 = airyB := by
  simp [airyDR, airyD_zero]

/-- Zero initial data for `u' = v`, `v' = c u` with `|c t| ≤ |t|` forces zero on `[0, ∞)`. -/
private theorem ode_zero_nonneg {u v c : ℝ → ℝ} (hu : ∀ t, HasDerivAt u (v t) t)
    (hv : ∀ t, HasDerivAt v (c t * u t) t) (hc : ∀ t, |c t| ≤ |t|)
    (h0 : u 0 = 0) (h1 : v 0 = 0) {x : ℝ} (hx : 0 ≤ x) : u x = 0 ∧ v x = 0 := by
  have key := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun t => (u t, v t))
    (f' := fun t => (v t, c t * u t)) (δ := 0) (K := 1 + x) (ε := 0) (a := 0) (b := x)
    (fun t _ => ((hu t).continuousAt.prodMk (hv t).continuousAt).continuousWithinAt)
    (fun t _ => ((hu t).prodMk (hv t)).hasDerivWithinAt)
    (by simp [h0, h1])
    (by
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have htx : t ≤ x := ht.2.le
      simp only [Prod.norm_def, Real.norm_eq_abs, add_zero]
      have hm1 := le_max_left |u t| |v t|
      have hm2 := le_max_right |u t| |v t|
      have hmn : 0 ≤ max |u t| |v t| := le_trans (abs_nonneg _) hm1
      apply max_le
      · nlinarith
      · rw [abs_mul]
        have := hc t
        rw [abs_of_nonneg ht0] at this
        have h3 : |c t| * |u t| ≤ x * max |u t| |v t| :=
          mul_le_mul (this.trans htx) hm1 (abs_nonneg _) hx
        nlinarith)
    x ⟨hx, le_rfl⟩
  rw [gronwallBound_ε0, zero_mul] at key
  have := norm_nonneg (u x, v x)
  have h := le_antisymm key this
  rw [Prod.norm_def] at h
  constructor
  · have := le_max_left ‖u x‖ ‖v x‖; rw [h] at this; exact norm_le_zero_iff.1 this
  · have := le_max_right ‖u x‖ ‖v x‖; rw [h] at this; exact norm_le_zero_iff.1 this

private theorem ode_zero {u v : ℝ → ℝ} (hu : ∀ t, HasDerivAt u (v t) t)
    (hv : ∀ t, HasDerivAt v (t * u t) t) (h0 : u 0 = 0) (h1 : v 0 = 0) (x : ℝ) :
    u x = 0 ∧ v x = 0 := by
  rcases le_total 0 x with hx | hx
  · exact ode_zero_nonneg hu hv (fun t => le_rfl) h0 h1 hx
  · have hu' : ∀ t, HasDerivAt (fun t => u (-t)) (-v (-t)) t := by
      intro t
      have := (hu (-t)).scomp t (hasDerivAt_neg t)
      simpa [Function.comp_def] using this
    have hv' : ∀ t, HasDerivAt (fun t => -v (-t)) (-t * u (-t)) t := by
      intro t
      have := ((hv (-t)).scomp t (hasDerivAt_neg t)).neg
      simp only [Function.comp_def] at this
      convert this using 1; simp
    have := ode_zero_nonneg (c := fun t => -t) hu' hv' (fun t => by simp) (by simpa using h0)
      (by simpa using h1) (neg_nonneg.2 hx)
    simp only [neg_neg, neg_eq_zero] at this
    exact this

end SpecialFunctions


end

section
/- Auxiliary proofs ported from SpecialFunctionsAiryInt.lean. -/

/-! A contour-integral representation of the Airy function along the rays
`arg t = ±π/3`, and the resulting bounds on the real axis. -/

open MeasureTheory Set Filter Topology

namespace SpecialFunctions

/-- `ω = e^{iπ/3}`. -/
private noncomputable def omA : ℂ := ⟨1/2, Real.sqrt 3 / 2⟩

private theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private theorem omA_cube : omA ^ 3 = -1 := by
  have h := sqrt3_sq
  apply Complex.ext <;> simp [omA, pow_succ, Complex.mul_re, Complex.mul_im]
  · linear_combination (-3/8) * h
  · linear_combination (-Real.sqrt 3 / 8) * h

private theorem norm_omA : ‖omA‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [omA]
  rw [show 1 / 2 * (1 / 2) + Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = (1:ℝ) by nlinarith [sqrt3_sq]]
  simp

/-- The integrand kernel `exp(-r³/3 - x ω r)`. -/
private noncomputable def gA (x r : ℝ) : ℂ := Complex.exp (((-(r ^ 3 / 3) : ℝ) : ℂ) - (x : ℂ) * omA * r)

private theorem norm_gA (x r : ℝ) : ‖gA x r‖ = Real.exp (-(r ^ 3 / 3) + (-x / 2) * r) := by
  rw [gA, Complex.norm_exp]
  congr 1
  rw [Complex.sub_re, Complex.ofReal_re]
  simp [omA, Complex.mul_re]
  ring

/-- Gaussian-cubic moments are integrable for any linear exponential weight. -/
private theorem integrableOn_cubic (n : ℕ) (a : ℝ) :
    IntegrableOn (fun r : ℝ => r ^ n * Real.exp (-(r ^ 3 / 3) + a * r)) (Ioi 0) := by
  set C := |a| * (6 * |a| + 1)
  have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 3) (b := 1/6)
    (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) (by norm_num) (by norm_num)).mul_const
    (Real.exp C)
  refine Integrable.mono' h ?_ ?_
  · exact (Continuous.mul (by fun_prop) (by fun_prop)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun r hr => ?_
    have hr' : (0:ℝ) < r := hr
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have e1 : (r : ℝ) ^ (n : ℝ) = r ^ n := Real.rpow_natCast r n
    have e2 : (r : ℝ) ^ (3 : ℝ) = r ^ 3 := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [e1, e2, mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.2
    have hle : a * r ≤ |a| * r := mul_le_mul_of_nonneg_right (le_abs_self a) hr'.le
    have hkey : |a| * r ≤ r ^ 3 / 6 + C := by
      have ha := abs_nonneg a
      rcases le_total r (6 * |a| + 1) with h1 | h1
      · have : |a| * r ≤ |a| * (6 * |a| + 1) := mul_le_mul_of_nonneg_left h1 ha
        have : 0 ≤ r ^ 3 := by positivity
        simp only [C]; linarith
      · have hr1 : 1 ≤ r := by linarith
        have : 6 * |a| ≤ r ^ 2 := by nlinarith
        have : |a| * r ≤ r ^ 3 / 6 := by nlinarith
        have : 0 ≤ C := by positivity
        linarith
    linarith

private theorem continuous_gA (x : ℝ) : Continuous (fun r => gA x r) := by
  unfold gA; fun_prop

/-- The integrand of the `n`-th derivative. -/
private noncomputable def aI (n : ℕ) (x r : ℝ) : ℂ := (-(omA * r)) ^ n * (omA * gA x r)

/-- `aJ n` is the `n`-th derivative of the integral representation. -/
private noncomputable def aJ (n : ℕ) (x : ℝ) : ℂ := ∫ r in Ioi (0:ℝ), aI n x r

private theorem continuous_aI (n : ℕ) (x : ℝ) : Continuous (fun r => aI n x r) := by
  unfold aI; have := continuous_gA x; fun_prop

private theorem norm_aI (n : ℕ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ‖aI n x r‖ = r ^ n * Real.exp (-(r ^ 3 / 3) + (-x / 2) * r) := by
  rw [aI, norm_mul, norm_mul, norm_pow, norm_neg, norm_mul, norm_omA, norm_gA,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  ring

private theorem integrableOn_aI (n : ℕ) (x : ℝ) : IntegrableOn (fun r => aI n x r) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_cubic n (-x / 2))
    (continuous_aI n x).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact ae_of_all _ fun r hr => (norm_aI n x (le_of_lt hr)).le

private theorem hasDerivAt_gA (x r : ℝ) :
    HasDerivAt (fun x => gA x r) (gA x r * (-(omA * r))) x := by
  have h : HasDerivAt (fun y : ℝ => (((-(r ^ 3 / 3) : ℝ)) : ℂ) - (y : ℂ) * omA * r)
      (-(omA * r)) x := by
    have := ((hasDerivAt_id x).ofReal_comp.mul_const (omA * (r : ℂ))).const_sub
      (((-(r ^ 3 / 3) : ℝ)) : ℂ)
    convert this using 1
    · funext y; simp only [id]; ring
    · simp
  exact h.cexp

private theorem hasDerivAt_aI (n : ℕ) (x r : ℝ) :
    HasDerivAt (fun x => aI n x r) (aI (n + 1) x r) x := by
  have := ((hasDerivAt_gA x r).const_mul omA).const_mul ((-(omA * r)) ^ n)
  exact this.congr_deriv (by show _ = (-(omA * r)) ^ (n + 1) * (omA * gA x r); ring)

private theorem hasDerivAt_aJ (n : ℕ) (x₀ : ℝ) : HasDerivAt (aJ n) (aJ (n + 1) x₀) x₀ := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun x r => aI n x r) (F' := fun x r => aI (n + 1) x r)
    (bound := fun r => r ^ (n + 1) * Real.exp (-(r ^ 3 / 3) + ((|x₀| + 1) / 2) * r))
    (s := Metric.ball x₀ 1) (x₀ := x₀)
    (Metric.ball_mem_nhds x₀ one_pos)
    (Eventually.of_forall fun x => (continuous_aI n x).aestronglyMeasurable)
    (integrableOn_aI n x₀)
    (continuous_aI (n + 1) x₀).aestronglyMeasurable
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ fun r hr x hx => ?_
      have hr' : (0:ℝ) ≤ r := le_of_lt hr
      rw [norm_aI (n + 1) x hr']
      gcongr
      rw [Metric.mem_ball, Real.dist_eq] at hx
      have h1 : -x ≤ |x₀| + 1 := by
        have := neg_abs_le (x - x₀)
        have := neg_abs_le x₀
        linarith
      linarith)
    (integrableOn_cubic (n + 1) _)
    (ae_of_all _ fun r x _ => hasDerivAt_aI n x r)
  exact key.2

private theorem hasDerivAt_gA_r (x r : ℝ) :
    HasDerivAt (fun r => gA x r) (aI 2 x r - x * aI 0 x r) r := by
  have h1 : HasDerivAt (fun r : ℝ => -(r ^ 3 / 3)) (-(r ^ 2)) r := by
    have := ((hasDerivAt_pow 3 r).div_const 3).neg
    convert this using 1; push_cast; ring
  have h2 : HasDerivAt (fun r : ℝ => (((-(r ^ 3 / 3) : ℝ)) : ℂ) - (x : ℂ) * omA * r)
      (((-(r ^ 2) : ℝ) : ℂ) - x * omA) r := by
    have := h1.ofReal_comp.sub (((hasDerivAt_id r).ofReal_comp).const_mul ((x : ℂ) * omA))
    convert this using 1
    · funext y; simp
    · simp
  have := h2.cexp
  refine this.congr_deriv ?_
  show _ = (-(omA * r)) ^ 2 * (omA * gA x r) - x * ((-(omA * r)) ^ 0 * (omA * gA x r))
  have hc := omA_cube
  rw [show (-(omA * (r : ℂ))) ^ 2 * (omA * gA x r) = omA ^ 3 * r ^ 2 * gA x r by ring, hc]
  simp only [gA]; push_cast; ring

private theorem tendsto_gA_atTop (x : ℝ) : Tendsto (fun r => gA x r) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_gA]
  refine Real.tendsto_exp_atBot.comp ?_
  set c := -x / 2
  refine tendsto_atBot_mono' atTop ?_ tendsto_neg_atTop_atBot
  filter_upwards [eventually_ge_atTop (3 * (|c| + 1))] with r hr
  have hc := abs_nonneg c
  have hr1 : 1 ≤ r := by linarith
  have h2 : 3 * (|c| + 1) ≤ r ^ 2 := by nlinarith
  have h3 : c * r ≤ |c| * r := mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith)
  nlinarith

private theorem aJ_two (x : ℝ) : aJ 2 x = x * aJ 0 x - 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (f := fun r => gA x r)
    (f' := fun r => aI 2 x r - x * aI 0 x r) (m := 0)
    (continuous_gA x).continuousAt.continuousWithinAt
    (fun r _ => hasDerivAt_gA_r x r)
    ((integrableOn_aI 2 x).sub ((integrableOn_aI 0 x).const_mul _))
    (tendsto_gA_atTop x)
  rw [integral_sub (integrableOn_aI 2 x) ((integrableOn_aI 0 x).const_mul _),
    integral_const_mul] at h
  have h0 : gA x 0 = 1 := by simp [gA]
  rw [h0] at h
  unfold aJ
  linear_combination h

private theorem integral_cubic_moment (q : ℕ) :
    ∫ r in Ioi (0:ℝ), r ^ q * Real.exp (-(r ^ 3 / 3)) =
      (1/3 : ℝ) ^ (-((q:ℝ) + 1) / 3) * (1 / 3) * Real.Gamma (((q:ℝ) + 1) / 3) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 3) (q := (q:ℝ)) (b := 1/3) (by norm_num)
    (by linarith [(Nat.cast_nonneg q : (0:ℝ) ≤ q)]) (by norm_num)
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have e : r ^ (3:ℝ) = r ^ (3:ℕ) := by exact_mod_cast Real.rpow_natCast r 3
  rw [Real.rpow_natCast, e]
  ring_nf

/-- The cube root of three. -/
private noncomputable def cbrt3 : ℝ := (3:ℝ) ^ (1/3 : ℝ)

private theorem cbrt3_pos : 0 < cbrt3 := by unfold cbrt3; positivity

private theorem cbrt3_cube : cbrt3 ^ 3 = 3 := by
  unfold cbrt3
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

private theorem third_rpow_neg_third : (1/3 : ℝ) ^ (-((0:ℕ) + 1 : ℝ) / 3) = cbrt3 := by
  rw [show (-((0:ℕ) + 1 : ℝ) / 3) = -(1/3 : ℝ) by push_cast; ring, Real.rpow_neg (by norm_num),
    Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow]
  unfold cbrt3; field_simp

private theorem third_rpow_neg_two_thirds : (1/3 : ℝ) ^ (-((1:ℕ) + 1 : ℝ) / 3) = cbrt3 ^ 2 := by
  rw [show (-((1:ℕ) + 1 : ℝ) / 3) = -(2/3 : ℝ) by push_cast; ring, Real.rpow_neg (by norm_num),
    Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow]
  unfold cbrt3
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

private theorem three_rpow_two_thirds : (3 : ℝ) ^ (2/3 : ℝ) = cbrt3 ^ 2 := by
  unfold cbrt3
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

private theorem gA_zero (r : ℝ) : gA 0 r = (Real.exp (-(r ^ 3 / 3)) : ℂ) := by
  simp [gA, Complex.ofReal_exp]

private theorem aJ_zero_zero : aJ 0 0 = omA * (∫ r in Ioi (0:ℝ), Real.exp (-(r ^ 3 / 3)) : ℝ) := by
  unfold aJ aI
  simp only [pow_zero, one_mul, gA_zero]
  rw [integral_const_mul, integral_complex_ofReal]

private theorem aJ_one_zero : aJ 1 0 =
    -omA ^ 2 * (∫ r in Ioi (0:ℝ), r * Real.exp (-(r ^ 3 / 3)) : ℝ) := by
  unfold aJ aI
  simp only [pow_one, gA_zero]
  rw [← integral_complex_ofReal, ← integral_const_mul]
  congr 1; funext r; push_cast; ring

/-- The integral representation. -/
private noncomputable def airyF (x : ℝ) : ℝ := (aJ 0 x).im / Real.pi
private noncomputable def airyF1 (x : ℝ) : ℝ := (aJ 1 x).im / Real.pi

private theorem hasDerivAt_im_aJ (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x => (aJ n x).im / Real.pi) ((aJ (n + 1) x).im / Real.pi) x := by
  have := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_aJ n x)).div_const Real.pi
  simpa using this

private theorem hasDerivAt_airyF (x : ℝ) : HasDerivAt airyF (airyF1 x) x := hasDerivAt_im_aJ 0 x

private theorem hasDerivAt_airyF1 (x : ℝ) : HasDerivAt airyF1 (x * airyF x) x := by
  have := hasDerivAt_im_aJ 1 x
  rw [aJ_two] at this
  refine this.congr_deriv ?_
  simp [airyF]; ring

private theorem airyF_zero : airyF 0 = airyA := by
  have hI := integral_cubic_moment 0
  simp only [pow_zero, one_mul] at hI
  rw [airyF, aJ_zero_zero, hI, third_rpow_neg_third, airyA, three_rpow_two_thirds]
  have hG := Gamma_third_mul
  have hc := cbrt3_cube
  have hp := cbrt3_pos
  have hpi := Real.pi_pos
  have hs : 0 < Real.sqrt 3 := by positivity
  have hs2 := sqrt3_sq
  have hg2 : 0 < Real.Gamma (2/3) := Real.Gamma_pos_of_pos (by norm_num)
  simp only [Complex.mul_im, omA, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  push_cast
  rw [show ((0:ℝ) + 1) / 3 = 1/3 by norm_num]
  rw [eq_div_iff hs.ne'] at hG
  field_simp
  nlinarith [hG]

private theorem airyF1_zero : airyF1 0 = airyB := by
  have hI := integral_cubic_moment 1
  simp only [pow_one] at hI
  rw [airyF1, aJ_one_zero, hI, third_rpow_neg_two_thirds, airyB]
  have hG := Gamma_third_mul
  have hc := cbrt3_cube
  have hp := cbrt3_pos
  have hpi := Real.pi_pos
  have hs : 0 < Real.sqrt 3 := by positivity
  have hs2 := sqrt3_sq
  have hg1 : 0 < Real.Gamma (1/3) := Real.Gamma_pos_of_pos (by norm_num)
  have hom : (-omA ^ 2).im = -(Real.sqrt 3 / 2) := by
    simp [omA, pow_two, Complex.mul_im]; ring
  rw [Complex.mul_im, hom, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
  rw [show ((1:ℕ):ℝ) + 1 = 2 by norm_num, show (2:ℝ) / 3 = 2/3 by norm_num]
  rw [show (3:ℝ) ^ (1/3 : ℝ) = cbrt3 from rfl]
  rw [eq_div_iff hs.ne'] at hG
  field_simp
  nlinarith [hG]

/-- The power-series Airy function equals its integral representation. -/
private theorem airyAi_eq_airyF (x : ℝ) : Real.airyAi x = airyF x ∧ airyDR x = airyF1 x := by
  have h := ode_zero (u := fun t => Real.airyAi t - airyF t) (v := fun t => airyDR t - airyF1 t)
    (fun t => (hasDerivAt_real_airyAi t).sub (hasDerivAt_airyF t))
    (fun t => by
      have := (hasDerivAt_airyDR t).sub (hasDerivAt_airyF1 t)
      refine this.congr_deriv ?_; ring)
    (by simp [real_airyAi_zero, airyF_zero]) (by simp [airyDR_zero, airyF1_zero]) x
  constructor <;> [linarith [h.1]; linarith [h.2]]

end SpecialFunctions


end

section
/- Auxiliary proofs ported from SpecialFunctionsAiryBound.lean. -/

/-! Bounds for the real Airy function and its derivative. -/

open MeasureTheory Set Filter Topology

namespace SpecialFunctions

private theorem norm_aJ_le_of_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖aJ n x‖ ≤ ∫ r in Ioi (0:ℝ), r ^ n * Real.exp (-(r ^ 3 / 3)) := by
  unfold aJ
  refine norm_integral_le_of_norm_le ?_ ?_
  · have := integrableOn_cubic n 0
    simp only [zero_mul, add_zero] at this
    exact this
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun r hr => ?_
    have hr' : (0:ℝ) ≤ r := le_of_lt hr
    rw [norm_aI n x hr']
    gcongr
    nlinarith

private theorem cbrt3_bounds : 1.44 ≤ cbrt3 ∧ cbrt3 ≤ 2 := by
  have h := cbrt3_cube
  have hp := cbrt3_pos
  constructor <;> nlinarith [sq_nonneg (cbrt3 - 1.44), sq_nonneg (cbrt3 - 2), sq_nonneg cbrt3]

private theorem integral_cubic_zero_le : ∫ r in Ioi (0:ℝ), r ^ 0 * Real.exp (-(r ^ 3 / 3)) ≤ 2 := by
  rw [integral_cubic_moment 0, third_rpow_neg_third]
  have := cbrt3_bounds
  have hg := Gamma_one_third_le
  have hg0 : 0 < Real.Gamma ((((0:ℕ):ℝ) + 1) / 3) := Real.Gamma_pos_of_pos (by norm_num)
  rw [show ((0:ℕ):ℝ) + 1 = 1 by norm_num] at hg0 ⊢
  nlinarith

private theorem integral_cubic_one_le : ∫ r in Ioi (0:ℝ), r ^ 1 * Real.exp (-(r ^ 3 / 3)) ≤ 2 := by
  rw [integral_cubic_moment 1, third_rpow_neg_two_thirds]
  have := cbrt3_bounds
  have hg := Gamma_two_third_le
  have hg0 : 0 < Real.Gamma ((((1:ℕ):ℝ) + 1) / 3) := Real.Gamma_pos_of_pos (by norm_num)
  rw [show ((1:ℕ):ℝ) + 1 = 2 by norm_num] at hg0 ⊢
  nlinarith

private theorem abs_im_div_pi_le {z : ℂ} (h : ‖z‖ ≤ 2) : |z.im / Real.pi| ≤ 1 := by
  rw [abs_div, abs_of_pos Real.pi_pos, div_le_one Real.pi_pos]
  linarith [Complex.abs_im_le_norm z, Real.pi_gt_three]

private theorem airy_bound_nonneg {x : ℝ} (hx : 0 ≤ x) :
    |Real.airyAi x| ≤ 1 ∧ |airyDR x| ≤ 1 := by
  obtain ⟨h1, h2⟩ := airyAi_eq_airyF x
  rw [h1, h2]
  exact ⟨abs_im_div_pi_le ((norm_aJ_le_of_nonneg 0 hx).trans integral_cubic_zero_le),
    abs_im_div_pi_le ((norm_aJ_le_of_nonneg 1 hx).trans integral_cubic_one_le)⟩

private theorem airy_energy_zero : airyA ^ 2 + airyB ^ 2 ≤ 0.33 := by
  obtain ⟨c1, c2⟩ := cbrt3_bounds
  have hc := cbrt3_cube
  have hg2 := Gamma_two_third_ge
  have hg2' := Gamma_two_third_le
  have hG := Gamma_third_mul
  have hg1 : 0 < Real.Gamma (1/3) := Real.Gamma_pos_of_pos (by norm_num)
  have hs3 : Real.sqrt 3 < 1.7321 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs : 0 < Real.sqrt 3 := by positivity
  have hpi := Real.pi_gt_d2
  have hq : 3.6 ≤ 2 * Real.pi / Real.sqrt 3 := by
    rw [le_div_iff₀ hs]; nlinarith
  have hg1' : 2.4 ≤ Real.Gamma (1/3) := by nlinarith
  have hA : airyA ^ 2 ≤ 1 / 4.32 := by
    rw [airyA, three_rpow_two_thirds, div_pow, one_pow]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h4 : 4.32 ≤ cbrt3 ^ 4 := by
      rw [show cbrt3 ^ 4 = cbrt3 * cbrt3 ^ 3 by ring, hc]; linarith
    have h5 : 1 ≤ Real.Gamma (2/3) ^ 2 := by nlinarith
    rw [mul_pow, ← pow_mul]
    nlinarith
  have hB : airyB ^ 2 ≤ 1 / (2.07 * 5.76) := by
    rw [airyB, show (3:ℝ) ^ (1/3 : ℝ) = cbrt3 from rfl, div_pow, neg_one_sq]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 2.07 ≤ cbrt3 ^ 2 := by nlinarith
    have : 5.76 ≤ Real.Gamma (1/3) ^ 2 := by nlinarith
    rw [mul_pow]; nlinarith
  norm_num at hA hB ⊢
  linarith

private theorem airy_energy_Icc {x : ℝ} (hx1 : -1 ≤ x) (hx0 : x ≤ 0) :
    Real.airyAi x ^ 2 + airyDR x ^ 2 ≤ 0.9 := by
  set h : ℝ → ℝ := fun t => (Real.airyAi t ^ 2 + airyDR t ^ 2) * Real.exp t
  have hd : ∀ t, HasDerivAt h ((2 * Real.airyAi t * airyDR t + 2 * airyDR t * (t * Real.airyAi t))
      * Real.exp t + (Real.airyAi t ^ 2 + airyDR t ^ 2) * Real.exp t) t := by
    intro t
    have h1 := ((hasDerivAt_real_airyAi t).pow 2).add ((hasDerivAt_airyDR t).pow 2)
    have := h1.mul (Real.hasDerivAt_exp t)
    convert this using 1; simp only [Pi.add_apply, Pi.pow_apply]; push_cast; ring
  have hmono : MonotoneOn h (Icc (-1) 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    have he := Real.exp_pos t
    have h1 : 0 ≤ 2 * Real.airyAi t * airyDR t + 2 * airyDR t * (t * Real.airyAi t) +
        (Real.airyAi t ^ 2 + airyDR t ^ 2) := by
      nlinarith [sq_nonneg (Real.airyAi t + airyDR t), sq_nonneg (Real.airyAi t),
        sq_nonneg (airyDR t), ht.1, ht.2,
        mul_nonneg (le_of_lt (show 0 < 1 + t by linarith [ht.1]))
          (sq_nonneg (Real.airyAi t + airyDR t)),
        mul_nonneg (le_of_lt (show 0 < -t by linarith [ht.2]))
          (add_nonneg (sq_nonneg (Real.airyAi t)) (sq_nonneg (airyDR t)))]
    nlinarith
  have hle := hmono ⟨hx1, hx0⟩ ⟨by norm_num, le_rfl⟩ hx0
  simp only [h, Real.exp_zero, mul_one, real_airyAi_zero, airyDR_zero] at hle
  have hE := airy_energy_zero
  have hexp : Real.exp (-x) ≤ 2.7183 := by
    calc Real.exp (-x) ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
      _ ≤ 2.7183 := by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have hx' : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos x
  have hpos' := Real.exp_pos (-x)
  have hE0 : 0 ≤ Real.airyAi x ^ 2 + airyDR x ^ 2 := by positivity
  have : Real.airyAi x ^ 2 + airyDR x ^ 2 ≤ (airyA ^ 2 + airyB ^ 2) * Real.exp (-x) := by
    have := mul_le_mul_of_nonneg_right hle hpos'.le
    rw [mul_assoc, hx', mul_one] at this
    exact this
  nlinarith

private theorem airy_sq_le_of_le_neg_one {x : ℝ} (hx : x ≤ -1) :
    Real.airyAi x ^ 2 ≤ Real.airyAi (-1) ^ 2 + airyDR (-1) ^ 2 := by
  set F : ℝ → ℝ := fun t => Real.airyAi t ^ 2 - airyDR t ^ 2 * t⁻¹
  have hd : ∀ t, t ≠ 0 → HasDerivAt F (2 * Real.airyAi t * airyDR t -
      (2 * airyDR t * (t * Real.airyAi t) * t⁻¹ + airyDR t ^ 2 * (-(t ^ 2)⁻¹))) t := by
    intro t ht
    have := ((hasDerivAt_real_airyAi t).pow 2).sub (((hasDerivAt_airyDR t).pow 2).mul
      (hasDerivAt_inv ht))
    convert this using 1; simp only [Pi.pow_apply]; push_cast; ring
  have hmono : MonotoneOn F (Iic (-1)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic _)
      (fun t ht => (hd t (by simp at ht; linarith)).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (by rw [interior_Iic] at ht; simp at ht; linarith)).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Iic] at ht
    have ht0 : t ≠ 0 := by simp at ht; linarith
    have e : 2 * Real.airyAi t * airyDR t - (2 * airyDR t * (t * Real.airyAi t) * t⁻¹ +
        airyDR t ^ 2 * (-(t ^ 2)⁻¹)) = airyDR t ^ 2 / t ^ 2 := by
      field_simp; ring
    rw [e]; positivity
  have hle := hmono hx (Set.mem_Iic.2 le_rfl) hx
  simp only [F] at hle
  have hneg : 0 ≤ -(airyDR x ^ 2 * x⁻¹) := by
    have : x⁻¹ < 0 := inv_lt_zero.2 (by linarith)
    nlinarith [sq_nonneg (airyDR x)]
  norm_num at hle
  linarith

private theorem real_airy_abs_le_one (x : ℝ) : |Real.airyAi x| ≤ 1 := by
  rcases le_total 0 x with h | h
  · exact (airy_bound_nonneg h).1
  rcases le_total (-1) x with h1 | h1
  · have := airy_energy_Icc h1 h
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (airyDR x)]
  · have := airy_sq_le_of_le_neg_one h1
    have := airy_energy_Icc (le_refl (-1)) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith

private theorem airyDR_sq_le_of_le_neg_one {x : ℝ} (hx : x ≤ -1) : airyDR x ^ 2 ≤ -x := by
  set H : ℝ → ℝ := fun t => airyDR t ^ 2 - t * Real.airyAi t ^ 2 + t
  have hd : ∀ t, HasDerivAt H (2 * airyDR t * (t * Real.airyAi t) -
      (1 * Real.airyAi t ^ 2 + t * (2 * Real.airyAi t * airyDR t)) + 1) t := by
    intro t
    have := (((hasDerivAt_airyDR t).pow 2).sub ((hasDerivAt_id t).mul
      ((hasDerivAt_real_airyAi t).pow 2))).add (hasDerivAt_id t)
    convert this using 1
    · funext s; simp [H]
    · simp only [id, Pi.pow_apply]; push_cast; ring
  have hmono : MonotoneOn H (Iic (-1)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic _)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt) ?_
    intro t _
    have := real_airy_abs_le_one t
    have : Real.airyAi t ^ 2 ≤ 1 := by rw [sq_le_one_iff_abs_le_one]; exact this
    nlinarith
  have hle := hmono hx (Set.mem_Iic.2 le_rfl) hx
  simp only [H] at hle
  have hE := airy_energy_Icc (le_refl (-1)) (by norm_num)
  nlinarith [sq_nonneg (Real.airyAi x)]

private theorem airyDR_abs_le (x : ℝ) : |airyDR x| ≤ 1 + |x| := by
  rcases le_total 0 x with h | h
  · have := (airy_bound_nonneg h).2; linarith [abs_nonneg x]
  rcases le_total (-1) x with h1 | h1
  · have := airy_energy_Icc h1 h
    have : |airyDR x| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Real.airyAi x)]
    linarith [abs_nonneg x]
  · have := airyDR_sq_le_of_le_neg_one h1
    rw [abs_of_nonpos h, abs_le]
    constructor <;> nlinarith

private theorem real_airyAi_lipschitz_aux (x y : ℝ) :
    |Real.airyAi x - Real.airyAi y| ≤ (2 + |x| + |y|) * Real.exp (|x| + |y|) * |x - y| := by
  have hmvt := (convex_uIcc y x).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.airyAi) (C := 1 + |x| + |y|)
    (fun t _ => (hasDerivAt_real_airyAi t).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs]
      refine (airyDR_abs_le t).trans ?_
      have : |t| ≤ |x| + |y| := by
        rcases Set.mem_uIcc.1 ht with h | h
        · rw [abs_le]; constructor
          · linarith [neg_abs_le y, neg_abs_le x, abs_nonneg x]
          · linarith [le_abs_self x, abs_nonneg y]
        · rw [abs_le]; constructor
          · linarith [neg_abs_le x, abs_nonneg y]
          · linarith [le_abs_self y, abs_nonneg x]
      linarith)
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have he : 1 ≤ Real.exp (|x| + |y|) := Real.one_le_exp (by positivity)
  have hC : 1 + |x| + |y| ≤ (2 + |x| + |y|) * Real.exp (|x| + |y|) := by
    nlinarith [abs_nonneg x, abs_nonneg y]
  calc |Real.airyAi x - Real.airyAi y| ≤ (1 + |x| + |y|) * |x - y| := hmvt
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (abs_nonneg _)

/-- Gronwall along a vertical ray. -/
private theorem airy_ray_bound (x : ℝ) (c : ℂ) (hc : ‖c‖ = 1) {T : ℝ} (hT : 0 ≤ T) :
    ‖Complex.airyAi (x + T * c)‖ ≤ (2 + |x|) * Real.exp ((1 + |x| + T) * T) := by
  set w : ℝ → ℂ := fun s => (x : ℂ) + s * c
  have hw : ∀ s : ℝ, HasDerivAt w c s := by
    intro s
    have := ((hasDerivAt_id s).ofReal_comp.mul_const c).const_add (x : ℂ)
    convert this using 1
    · rfl
    · simp
  have hf : ∀ s : ℝ, HasDerivAt (fun s => (Complex.airyAi (w s), airyD (w s)))
      (airyD (w s) * c, (w s * Complex.airyAi (w s)) * c) s := fun s =>
    ((hasDerivAt_airyAi (w s)).comp s (hw s)).prodMk ((hasDerivAt_airyD (w s)).comp s (hw s))
  have hnw : ∀ s, 0 ≤ s → ‖w s‖ ≤ |x| + s := by
    intro s hs
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hc, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hs, mul_one]
  have key := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun s => (Complex.airyAi (w s), airyD (w s)))
    (f' := fun s => (airyD (w s) * c, (w s * Complex.airyAi (w s)) * c))
    (δ := 2 + |x|) (K := 1 + |x| + T) (ε := 0) (a := 0) (b := T)
    (fun s _ => (hf s).continuousAt.continuousWithinAt)
    (fun s _ => (hf s).hasDerivWithinAt)
    (by
      simp only [w, Complex.ofReal_zero, zero_mul, add_zero]
      rw [Prod.norm_def, airyAi_ofReal, airyD_ofReal, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := real_airy_abs_le_one x
      have h2 := airyDR_abs_le x
      apply max_le <;> linarith [abs_nonneg x])
    (by
      intro s hs
      have hs0 : 0 ≤ s := hs.1
      have hsT : s ≤ T := hs.2.le
      have hn := hnw s hs0
      simp only [Prod.norm_def, norm_mul, hc, mul_one, add_zero]
      have hm1 := le_max_left ‖Complex.airyAi (w s)‖ ‖airyD (w s)‖
      have hm2 := le_max_right ‖Complex.airyAi (w s)‖ ‖airyD (w s)‖
      have hmn : 0 ≤ max ‖Complex.airyAi (w s)‖ ‖airyD (w s)‖ := le_trans (norm_nonneg _) hm1
      have hx := abs_nonneg x
      apply max_le
      · nlinarith
      · have : ‖w s‖ * ‖Complex.airyAi (w s)‖ ≤ (|x| + T) * max ‖Complex.airyAi (w s)‖ ‖airyD (w s)‖ :=
          mul_le_mul (by linarith) hm1 (norm_nonneg _) (by linarith)
        nlinarith)
    T ⟨hT, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at key
  refine le_trans ?_ key
  rw [Prod.norm_def]
  exact le_max_left _ _

private theorem airy_complex_vertical_aux (z : ℂ) :
    ‖Complex.airyAi z‖ ≤ (2 + |z.re|) * Real.exp ((1 + |z.re| + |z.im|) * |z.im|) := by
  rcases le_total 0 z.im with h | h
  · have := airy_ray_bound z.re Complex.I Complex.norm_I (abs_nonneg z.im)
    rw [abs_of_nonneg h] at this ⊢
    have e : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := Complex.re_add_im z
    rwa [e] at this
  · have := airy_ray_bound z.re (-Complex.I) (by simp) (abs_nonneg z.im)
    rw [abs_of_nonpos h] at this ⊢
    have e : (z.re : ℂ) + ((-z.im : ℝ) : ℂ) * -Complex.I = z := by
      push_cast; rw [neg_mul_neg]; exact Complex.re_add_im z
    rwa [e] at this

end SpecialFunctions


end

section
/- Auxiliary proofs ported from SpecialFunctionsSi.lean. -/

/-! Laplace-integral representation of the sine integral and the remainder
bounds for its asymptotic expansion. -/

open MeasureTheory Set Filter Topology

namespace SpecialFunctions

/-- Gamma moments `∫₀^∞ t^m e^{-xt} dt = m! / x^(m+1)`. -/
private theorem integrableOn_pow_mul_exp_neg (m : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(x * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (m : ℝ)) (p := 1) (b := x)
    (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) one_pos hx
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, Real.rpow_natCast, neg_mul]

private theorem integral_pow_mul_exp_neg (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0:ℝ), t ^ m * Real.exp (-(x * t)) = m.factorial / x ^ (m + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (m : ℝ) + 1) (r := x) (by positivity) hx
  rw [show (m : ℝ) + 1 - 1 = (m : ℝ) by ring, Real.Gamma_nat_eq_factorial] at h
  have e : ∫ t in Ioi (0:ℝ), t ^ m * Real.exp (-(x * t)) =
      ∫ t in Ioi (0:ℝ), t ^ (m : ℝ) * Real.exp (-(x * t)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => by simp only [Real.rpow_natCast])
  rw [e, h, show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [div_pow, one_pow]; ring

/-- Laplace moments against `1/(1+t^2)`. -/
private noncomputable def lapI (x : ℝ) (m : ℕ) : ℝ :=
  ∫ t in Ioi (0:ℝ), t ^ m * Real.exp (-(x * t)) / (1 + t ^ 2)

private theorem lap_integrand_le (m : ℕ) (x t : ℝ) (ht : 0 < t) :
    ‖t ^ m * Real.exp (-(x * t)) / (1 + t ^ 2)‖ ≤ t ^ m * Real.exp (-(x * t)) := by
  have h1 : 0 ≤ t ^ m * Real.exp (-(x * t)) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_self h1 (by nlinarith)

private theorem integrableOn_lap (m : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(x * t)) / (1 + t ^ 2)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_pow_mul_exp_neg m hx) ?_ ?_
  · exact (Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity)
      : Continuous (fun t : ℝ => t ^ m * Real.exp (-(x * t)) / (1 + t ^ 2))).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ fun t ht => lap_integrand_le m x t ht

private theorem lapI_nonneg (m : ℕ) (x : ℝ) : 0 ≤ lapI x m := by
  unfold lapI
  refine setIntegral_nonneg measurableSet_Ioi (fun t ht => ?_)
  have : (0:ℝ) < t := ht
  positivity

private theorem lapI_le (m : ℕ) {x : ℝ} (hx : 0 < x) : lapI x m ≤ m.factorial / x ^ (m + 1) := by
  rw [← integral_pow_mul_exp_neg m hx]
  unfold lapI
  refine setIntegral_mono_on (integrableOn_lap m hx) (integrableOn_pow_mul_exp_neg m hx)
    measurableSet_Ioi (fun t ht => ?_)
  have := lap_integrand_le m x t ht
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

private theorem lapI_rec (m : ℕ) {x : ℝ} (hx : 0 < x) :
    lapI x m = m.factorial / x ^ (m + 1) - lapI x (m + 2) := by
  rw [← integral_pow_mul_exp_neg m hx]
  unfold lapI
  rw [← integral_sub (integrableOn_pow_mul_exp_neg m hx) (integrableOn_lap (m + 2) hx)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have : (0:ℝ) < 1 + t ^ 2 := by positivity
  field_simp
  ring

private theorem lapI_expand (s : ℕ) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    lapI x s = ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * (2 * k + s).factorial / x ^ (2 * k + s + 1) +
      (-1) ^ n * lapI x (2 * n + s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, lapI_rec (2 * n + s) hx, Finset.sum_range_succ,
      show 2 * n + s + 2 = 2 * (n + 1) + s by ring]
    ring

private theorem hasDerivAt_lapI (m : ℕ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    HasDerivAt (fun x => lapI x m) (-lapI x₀ (m + 1)) x₀ := by
  have hb : 0 < x₀ / 2 := by linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun x t => t ^ m * Real.exp (-(x * t)) / (1 + t ^ 2))
    (F' := fun x t => -(t ^ (m + 1) * Real.exp (-(x * t)) / (1 + t ^ 2)))
    (bound := fun t => t ^ (m + 1) * Real.exp (-((x₀ / 2) * t)))
    (s := Ioi (x₀ / 2)) (x₀ := x₀)
    (Ioi_mem_nhds (by linarith))
    (Eventually.of_forall fun x => (Continuous.div (by fun_prop) (by fun_prop)
      (fun t => by positivity)).aestronglyMeasurable)
    (integrableOn_lap m hx₀)
    ((Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity)).aestronglyMeasurable.neg)
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ fun t ht x hx => ?_
      have ht' : (0:ℝ) < t := ht
      have hx' : x₀ / 2 < x := hx
      rw [norm_neg]
      refine (lap_integrand_le (m + 1) x t ht').trans ?_
      gcongr)
    (integrableOn_pow_mul_exp_neg (m + 1) hb)
    (by
      refine ae_of_all _ fun t x _ => ?_
      have h1 : HasDerivAt (fun x => Real.exp (-(x * t))) (Real.exp (-(x * t)) * (-t)) x := by
        have := ((hasDerivAt_id x).mul_const t).neg.exp
        simpa using this
      have := (h1.const_mul (t ^ m)).div_const (1 + t ^ 2)
      convert this using 1
      ring)
  have e : ∫ t in Ioi (0:ℝ), -(t ^ (m + 1) * Real.exp (-(x₀ * t)) / (1 + t ^ 2)) =
      -lapI x₀ (m + 1) := by
    rw [integral_neg]; rfl
  rw [← e]
  exact key.2

private theorem hasDerivAt_real_Si (x : ℝ) : HasDerivAt Real.Si (sincC x).re x := by
  have h := (hasDerivAt_Si (x : ℂ)).real_of_complex
  have e1 : (fun y : ℝ => (Complex.Si (y : ℂ)).re) = Real.Si := by
    funext y; rw [Si_ofReal]; simp
  rwa [e1] at h

private theorem sincC_re {x : ℝ} (hx : x ≠ 0) : (sincC x).re = Real.sin x / x := by
  have h := mul_sincC (x : ℂ)
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have : sincC x = Complex.sin x / x := by
    rw [eq_div_iff hx', mul_comm]; exact h
  rw [this, ← Complex.ofReal_sin, ← Complex.ofReal_div, Complex.ofReal_re]

/-- The combination that is constant on `(0, ∞)`. -/
private noncomputable def siH (x : ℝ) : ℝ :=
  Real.Si x + lapI x 0 * Real.cos x + lapI x 1 * Real.sin x

private theorem hasDerivAt_siH {x : ℝ} (hx : 0 < x) : HasDerivAt siH 0 x := by
  have h0 := hasDerivAt_lapI 0 hx
  have h1 := hasDerivAt_lapI 1 hx
  have hrec := lapI_rec 0 hx
  have hS := hasDerivAt_real_Si x
  rw [sincC_re hx.ne'] at hS
  have := (hS.add (h0.mul (Real.hasDerivAt_cos x))).add (h1.mul (Real.hasDerivAt_sin x))
  have e : siH = Real.Si + (fun x => lapI x 0) * Real.cos + (fun x => lapI x 1) * Real.sin := rfl
  rw [e]
  convert this using 1
  simp only [zero_add, Nat.factorial_zero, Nat.cast_one, pow_one] at hrec
  have hx' : x ≠ 0 := hx.ne'
  rw [show lapI x (1 + 1) = 1 / x - lapI x 0 by linarith]
  field_simp
  ring

private theorem siH_const {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : siH x = siH y := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := siH) (C := 0)
    (s := Ioi 0) (fun t ht => (hasDerivAt_siH ht).hasDerivWithinAt)
    (fun t _ => by simp) (convex_Ioi 0) hy hx
  simp at this
  linarith

private theorem lapI0_tendsto : Tendsto (fun x => lapI x 0) (𝓝[>] 0) (𝓝 (Real.pi / 2)) := by
  have hlim : ∫ t in Ioi (0:ℝ), (1 + t ^ 2)⁻¹ = Real.pi / 2 := by
    rw [integral_Ioi_inv_one_add_sq]; simp
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (fun t => (1 + t ^ 2)⁻¹) ?_ ?_
    integrable_inv_one_add_sq.integrableOn ?_
  · exact Eventually.of_forall fun x => (Continuous.div (by fun_prop) (by fun_prop)
      (fun t => by positivity)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with x hx
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun t ht => ?_
    have hx' : (0:ℝ) < x := hx
    have ht' : (0:ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_zero, one_mul, div_eq_mul_inv]
    have : Real.exp (-(x * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
    nlinarith
  · refine ae_of_all _ fun t => ?_
    have hc : Continuous (fun x : ℝ => t ^ 0 * Real.exp (-(x * t)) / (1 + t ^ 2)) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this

private theorem x_lapI1_tendsto : Tendsto (fun x => x * lapI x 1) (𝓝[>] 0) (𝓝 0) := by
  have e : (fun x => x * lapI x 1) =
      fun x => ∫ t in Ioi (0:ℝ), x * (t ^ 1 * Real.exp (-(x * t)) / (1 + t ^ 2)) := by
    funext x; unfold lapI; rw [integral_const_mul]
  rw [e]
  rw [show (𝓝 (0:ℝ)) = 𝓝 (∫ t in Ioi (0:ℝ), (0:ℝ) * (t ^ 1 * Real.exp (-((0:ℝ) * t)) /
    (1 + t ^ 2))) by simp]
  refine tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0:ℝ))
    (fun t => (1 + t ^ 2)⁻¹) ?_ ?_ integrable_inv_one_add_sq.integrableOn ?_
  · exact Eventually.of_forall fun x => ((Continuous.div (by fun_prop) (by fun_prop)
      (fun t => by positivity)).const_mul x).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with x hx
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun t ht => ?_
    have hx' : (0:ℝ) < x := hx
    have ht' : (0:ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_one]
    have hy : x * t * Real.exp (-(x * t)) ≤ 1 := by
      have h1 := Real.add_one_le_exp (x * t)
      have h2 : Real.exp (x * t) * Real.exp (-(x * t)) = 1 := by
        rw [← Real.exp_add]; simp
      have h3 := Real.exp_pos (-(x * t))
      nlinarith
    have hpos : 0 < 1 + t ^ 2 := by positivity
    rw [show x * (t * Real.exp (-(x * t)) / (1 + t ^ 2)) =
      (x * t * Real.exp (-(x * t))) * (1 + t ^ 2)⁻¹ by field_simp]
    have : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
    nlinarith
  · refine ae_of_all _ fun t => ?_
    have hc : Continuous (fun x : ℝ => x * (t ^ 1 * Real.exp (-(x * t)) / (1 + t ^ 2))) := by
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this

private theorem siH_tendsto : Tendsto siH (𝓝[>] 0) (𝓝 (Real.pi / 2)) := by
  have hSi : Tendsto Real.Si (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_Si.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [Real.Si] using this
  have hcos : Tendsto Real.cos (𝓝[>] 0) (𝓝 1) := by
    have := (Real.continuous_cos.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have h3 : Tendsto (fun x => lapI x 1 * Real.sin x) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ x_lapI1_tendsto
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0:ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (lapI_nonneg 1 x)]
    have := Real.abs_sin_le_abs (x := x)
    rw [abs_of_pos hx'] at this
    nlinarith [lapI_nonneg 1 x]
  have := (hSi.add (lapI0_tendsto.mul hcos)).add h3
  have e : siH = fun x => Real.Si x + lapI x 0 * Real.cos x + lapI x 1 * Real.sin x := rfl
  rw [e]
  simpa using this

private theorem Si_eq_laplace {x : ℝ} (hx : 0 < x) :
    Real.Si x = Real.pi / 2 - lapI x 0 * Real.cos x - lapI x 1 * Real.sin x := by
  have hconst : Tendsto siH (𝓝[>] 0) (𝓝 (siH x)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact siH_const hx hy
  have := tendsto_nhds_unique hconst siH_tendsto
  unfold siH at this
  linarith


private theorem si_asymptotic_of_laplace (x : ℝ) (hx : 0 < x) (n : ℕ) :
    |Real.Si x - (Real.pi/2 - Real.cos x / x *
      (∑ k ∈ Finset.range n, (-1 : ℝ)^k * (2*k).factorial / x^(2*k)) -
      Real.sin x / x^2 *
      (∑ k ∈ Finset.range n, (-1 : ℝ)^k * (2*k+1).factorial / x^(2*k)))| ≤
      (2*n).factorial / x^(2*n+1) + (2*n+1).factorial / x^(2*n+2) := by
  have h0 := lapI_expand 0 hx n
  have h1 := lapI_expand 1 hx n
  have e0 : Real.cos x / x * (∑ k ∈ Finset.range n, (-1 : ℝ)^k * (2*k).factorial / x^(2*k)) =
      Real.cos x * ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * (2 * k + 0).factorial / x ^ (2 * k + 0 + 1) := by
    rw [div_mul_eq_mul_div, mul_div_assoc, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [add_zero, pow_succ]; field_simp
  have e1 : Real.sin x / x^2 * (∑ k ∈ Finset.range n, (-1 : ℝ)^k * (2*k+1).factorial / x^(2*k)) =
      Real.sin x * ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * (2 * k + 1).factorial / x ^ (2 * k + 1 + 1) := by
    rw [div_mul_eq_mul_div, mul_div_assoc, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring, pow_add]; field_simp
  rw [e0, e1, Si_eq_laplace hx]
  have key : Real.pi / 2 - lapI x 0 * Real.cos x - lapI x 1 * Real.sin x -
      (Real.pi / 2 - Real.cos x * (∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * (2 * k + 0).factorial /
        x ^ (2 * k + 0 + 1)) - Real.sin x * ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k *
          (2 * k + 1).factorial / x ^ (2 * k + 1 + 1)) =
      -((-1) ^ n * lapI x (2 * n + 0) * Real.cos x) - (-1) ^ n * lapI x (2 * n + 1) * Real.sin x := by
    rw [h0, h1]; ring
  rw [key]
  have hp : |(-1 : ℝ) ^ n| = 1 := by simp
  have a0 := lapI_le (2 * n + 0) hx
  have a1 := lapI_le (2 * n + 1) hx
  have n0 := lapI_nonneg (2 * n + 0) x
  have n1 := lapI_nonneg (2 * n + 1) x
  have c := Real.abs_cos_le_one x
  have s := Real.abs_sin_le_one x
  simp only [add_zero] at a0 n0 ⊢
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring] at a1
  refine (abs_sub _ _).trans ?_
  rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_mul, hp, one_mul, one_mul,
    abs_of_nonneg n0, abs_of_nonneg n1]
  have := mul_le_mul a0 c (abs_nonneg _) (by positivity)
  have := mul_le_mul a1 s (abs_nonneg _) (by positivity)
  linarith

end SpecialFunctions


end

namespace SpecialFunctions

/-- Real/complex compatibility and entire analyticity, including eta's filled pole. -/
theorem entire_agrees :
    (∀ f ∈ [Complex.erf, Complex.Si, Complex.dirichletEta, Complex.airyAi],
      AnalyticOnNhd ℂ f Set.univ) ∧
    (∀ x : ℝ, Complex.erf x = (Real.erf x : ℂ) ∧
      Complex.Si x = (Real.Si x : ℂ) ∧
      Complex.dirichletEta x = (Real.dirichletEta x : ℂ) ∧
      Complex.airyAi x = (Real.airyAi x : ℂ)) := by
  refine ⟨?_, fun x => ⟨erf_ofReal x, Si_ofReal x, dirichletEta_ofReal x, airyAi_ofReal x⟩⟩
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact analyticOnNhd_erf
  · exact analyticOnNhd_Si
  · exact fun z _ => analyticAt_dirichletEta z
  · exact analyticOnNhd_airyAi

private theorem real_erf_lipschitz (x y : ℝ) : |Real.erf x - Real.erf y| ≤ 2*|x-y| := by
  have hpi : 1 ≤ Real.sqrt Real.pi := by
    rw [Real.one_le_sqrt]; linarith [Real.pi_gt_three]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Real.erf) (C := 2)
    (s := Set.univ) (fun t _ => (hasDerivAt_real_erf t).hasDerivWithinAt)
    (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 : Real.exp (-t^2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have h2 : 2 / Real.sqrt Real.pi ≤ 2 := div_le_self (by norm_num) hpi
      calc 2 / Real.sqrt Real.pi * Real.exp (-t^2) ≤ 2 * 1 := by
            gcongr
        _ = 2 := by ring) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

private theorem real_Si_lipschitz (x y : ℝ) : |Real.Si x - Real.Si y| ≤ |x-y| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Real.Si) (C := 1)
    (s := Set.univ) (fun t _ => (hasDerivAt_real_Si t).hasDerivWithinAt)
    (fun t _ => by
      calc ‖(sincC t).re‖ ≤ ‖sincC t‖ := by
            rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
        _ ≤ Real.exp |(t : ℂ).im| := norm_sincC_le _
        _ = 1 := by simp) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

/-- Airy part of `real_lipschitz`. Crude power-series bounds do not suffice for
large positive arguments: the bound needs the decay of `Ai`. -/
private theorem real_airyAi_lipschitz (x y : ℝ) :
    |Real.airyAi x - Real.airyAi y| ≤
      (2 + |x| + |y|) * Real.exp (|x| + |y|) * |x-y| :=
  real_airyAi_lipschitz_aux x y

/-- Real derivative bounds used to transport a midpoint enclosure. -/

theorem real_lipschitz (x y : ℝ) :
    |Real.erf x - Real.erf y| ≤ 2*|x-y| ∧
    |Real.Si x - Real.Si y| ≤ |x-y| ∧
    |Real.airyAi x - Real.airyAi y| ≤
      (2 + |x| + |y|) * Real.exp (|x| + |y|) * |x-y| :=
  ⟨real_erf_lipschitz x y, real_Si_lipschitz x y, real_airyAi_lipschitz x y⟩

/-- Bounds for integration ellipses; no oscillatory real phase is evaluated. -/

theorem complex_bounds (z : ℂ) :
    ‖Complex.erf z‖ ≤ 1 + 2*|z.im| *Real.exp (z.im^2) ∧
    ‖Complex.Si z‖ ≤ ‖z‖ * Real.exp |z.im| ∧
    ‖Complex.airyAi z‖ ≤ (1+‖z‖) * Real.exp (‖z‖^2+1) := by
  exact ⟨norm_erf_bound z, norm_Si_bound z, norm_airyAi_bound z⟩

def airyConstScale : ℕ := 10^400
def airyConstA : ℤ := 3550280538878172392600631860041831763979791741991772405833265103008100424501267129571742460540402716884204487303494958397582926704461619371050402400225853863840099026010357128190515682032902491696447661823279677702418989594796173489086406257323897601417640056780397387733804863176108754520253233492223889696310797677817018407651352099370413155733915331326628757170039713556080491748639102813585025352
def airyConstB : ℤ := -2588194037928067984051835601892039634790911383549345822100018138561027726767902806541964058272753843133711932117891333812750359521676260147850509898484194466320296448888056018783833051269505251282933424979998835707490792590601589510509443220893840596735777193280251066501701756898365786075255831135478171318620449582927213325913268210520314000118299672244516610304438553000396853595369554995929031115

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
set_option cbv.maxSteps 100000000 in
set_option exponentiation.threshold 8192 in
theorem airy_constants :
    (airyConstA : ℝ) / airyConstScale ≤ airyA ∧
    airyA ≤ (airyConstA+1 : ℝ) / airyConstScale ∧
    (airyConstB : ℝ) / airyConstScale ≤ airyB ∧
    airyB ≤ (airyConstB+1 : ℝ) / airyConstScale := by
  open scoped Lynth.Interval.AiryProof.Kernel in
  open Lynth.Interval Lynth.Interval.Fns Lynth.Interval.AiryProof in
  exact by
    let p : ℕ := 1344
    let c := Ctx.make (p + 32)
    let G := gammaForNormalization c (Ival.ofRat p (1/3))
    let G2 := Ival.div p (Ival.div p c.pi
      (Ival.divNat p (Ival.sqrt p (Ival.ofRat p 3)) 2)) G
    let A := Ival.inv p (Ival.mul p
      (rpowIval c (Ival.ofRat p 3) (Ival.ofRat p (2/3))) G2)
    let B := Ival.neg (Ival.inv p (Ival.mul p
      (rpowIval c (Ival.ofRat p 3) (Ival.ofRat p (1/3))) G))
    have hG : Real.Gamma (1/3) ∈ G := by
      simpa [G] using mem_gammaForNormalization (Ctx.make_valid (p + 32))
        (Ival.mem_ofRat p (1/3))
    have hG2 : Real.Gamma (2/3) ∈ G2 := by
      rw [gamma_two_thirds_reflection]
      have hthree : (3 : ℝ) ∈ Ival.ofRat p 3 := by simpa using Ival.mem_ofRat p 3
      exact Ival.mem_div (Ival.mem_div (Ctx.make_valid _).pi_mem
        (Ival.mem_divNat (Ival.mem_sqrt hthree) (by decide))) hG
    have hA : airyA ∈ A := by
      simpa [airyA, A, one_div] using Ival.mem_inv
        (Ival.mem_mul (mem_rpowIval (Ctx.make_valid _) (Ival.mem_ofRat _ 3)
          (Ival.mem_ofRat _ (2/3))) hG2)
    have hB : airyB ∈ B := by
      simpa [airyB, B, one_div, neg_div] using Ival.mem_neg (Ival.mem_inv
        (Ival.mem_mul (mem_rpowIval (Ctx.make_valid _) (Ival.mem_ofRat _ 3)
          (Ival.mem_ofRat _ (1/3))) hG))
    have hcheck : (rationalBounds A (airyConstA / (airyConstScale : ℚ)) ((airyConstA + 1) / (airyConstScale : ℚ)) &&
        rationalBounds B (airyConstB / (airyConstScale : ℚ)) ((airyConstB + 1) / (airyConstScale : ℚ))) = true := by
      dsimp only [A, B, G2, G, c, p]
      decide_cbv
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hcheck
    have hAr := rationalBounds_sound hA ha
    have hBr := rationalBounds_sound hB hb
    push_cast at hAr hBr
    exact ⟨hAr.1, hAr.2, hBr.1, hBr.2⟩

/-- Vertical ODE transport from the real axis avoids exponential growth in
|Re z| when bounding Airy on a thin quadrature ellipse. -/
theorem airy_complex_vertical (z : ℂ) :
    ‖Complex.airyAi z‖ ≤ (2+|z.re|) *
      Real.exp ((1+|z.re|+|z.im|)*|z.im|) :=
  airy_complex_vertical_aux z

/-- Uniform real-axis bound sufficient for the exponentially damped Airy tail. -/

theorem airy_real_bound (x : ℝ) : |Real.airyAi x| ≤ 1 :=
  real_airy_abs_le_one x

theorem erf_range (x : ℝ) : -1 ≤ Real.erf x ∧ Real.erf x ≤ 1 := by
  exact real_erf_range x

/-- Real Gaussian tail for erf. -/

theorem erf_tail (x : ℝ) (hx : 0 < x) :
    |Real.erf x - 1| ≤ Real.exp (-x^2) / x := by
  exact real_erf_tail hx

/-- Laplace-integral asymptotics with the two first omitted terms bounded
separately. Unlike a convergence assumption this holds for every n. -/

theorem erf_odd (x : ℝ) : Real.erf (-x) = -Real.erf x := by
  simp [Real.erf]

theorem si_odd (x : ℝ) : Real.Si (-x) = -Real.Si x := by
  simp [Real.Si]

/-- Laplace-integral asymptotics with the two first omitted terms bounded
separately. Unlike a convergence assumption this holds for every n. -/
theorem si_asymptotic (x : ℝ) (hx : 0 < x) (n : ℕ) :
    |Real.Si x - (Real.pi/2 - Real.cos x / x *
      (∑ k ∈ Finset.range n, (-1 : ℝ)^k * (2*k).factorial / x^(2*k)) -
      Real.sin x / x^2 *
      (∑ k ∈ Finset.range n, (-1 : ℝ)^k * (2*k+1).factorial / x^(2*k)))| ≤
      (2*n).factorial / x^(2*n+1) + (2*n+1).factorial / x^(2*n+2) :=
  si_asymptotic_of_laplace x hx n

noncomputable def hornerR (xs : List ℚ) (x : ℝ) : ℝ :=
  match xs with
  | [] => 0
  | q :: qs => q + x * hornerR qs x

def siCoeffs (n : ℕ) (sine : Bool) : List ℚ :=
  (List.range n).map fun k => (-1 : ℚ)^k * ((2*k + if sine then 1 else 0).factorial : ℚ)

private theorem hornerR_map_range (g : ℕ → ℚ) (y : ℝ) (n : ℕ) :
    hornerR ((List.range n).map g) y = ∑ k ∈ Finset.range n, (g k : ℝ) * y ^ k := by
  induction n generalizing g with
  | zero => simp [hornerR]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, hornerR, ih,
      Finset.sum_range_succ', Finset.mul_sum]
    simp only [Function.comp_apply, pow_zero, mul_one, pow_succ]
    rw [add_comm]; congr 1
    refine Finset.sum_congr rfl fun k _ => by ring


theorem si_asymptotic_horner (x : ℝ) (hx : 0 < x) (n : ℕ) :
    |Real.Si x - (Real.pi/2 - Real.cos x / x * hornerR (siCoeffs n false) (x^2)⁻¹ -
      Real.sin x / x^2 * hornerR (siCoeffs n true) (x^2)⁻¹)| ≤
      (2*n).factorial / x^(2*n+1) + (2*n+1).factorial / x^(2*n+2) := by
  have key : ∀ s : Bool, hornerR (siCoeffs n s) (x^2)⁻¹ =
      ∑ k ∈ Finset.range n, (-1 : ℝ)^k * (2*k + if s then 1 else 0).factorial / x^(2*k) := by
    intro s
    rw [siCoeffs, hornerR_map_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    rw [inv_pow, ← pow_mul, div_eq_mul_inv]
  rw [key, key]
  simpa using si_asymptotic x hx n

/-- Linear-time weights for the first n Euler-transformed eta terms. -/

def etaWeights (n : ℕ) : List (ℕ × ℚ) := Id.run do
  let scale := 2^n
  let mut binom := 1
  let mut total := 0
  let mut out := []
  for k in [0:n] do
    total := total + binom
    let w : ℚ := (scale-total : ℕ) / (scale : ℚ)
    out := (k+1, if k % 2 = 0 then w else -w) :: out
    binom := binom * (n-k) / (k+1)
  return out.reverse

noncomputable def etaApproxR (s : ℝ) (n : ℕ) : ℝ :=
  ((etaWeights n).map fun (k,w) => (w : ℝ) * (k : ℝ)^(-s)).sum
noncomputable def etaApproxC (s : ℂ) (n : ℕ) : ℂ :=
  ((etaWeights n).map fun (k,w) => (w : ℂ) * (k : ℂ)^(-s)).sum

end SpecialFunctions

section
/- Eta proof support ported from the archive. -/

/-! The Euler-transformed series for the Dirichlet eta function and its truncation
error. The definitions `etaWeights`, `etaApproxR` and `etaApproxC` used by
`SpecialFunctions.lean` live here so that the error analysis can refer to them.

The main facts proved here are:
* `etaWeights_eq`: the imperative loop computes `etaEntry n k` for `k < n`;
* `etaApproxC_eq_sum`: the truncation is the partial sum of the Euler series
  `∑ j, 2^{-(j+1)} Δ_j(s)`, with `Δ_j(s) = ∑_{i ≤ j} (-1)^i C(j,i) (i+1)^{-s}`;
* `norm_etaDelta_le`: `|Δ_j(s)| ≤ (j+1)^m exp(τ²/2 ((σ+m)⁻² + (σ+m)⁻¹))`;
* `dirichletEta_eq_euler`: `η(s) = ∑ j, 2^{-(j+1)} Δ_j(s)` for every `s`;
* `eta_euler_error_aux`: the truncation error bound.
-/

namespace SpecialFunctions

private def etaEntry (n k : ℕ) : ℕ × ℚ :=
  let w : ℚ := (2^n - ∑ i ∈ Finset.range (k+1), n.choose i : ℕ) / (2^n : ℚ)
  (k+1, if k % 2 = 0 then w else -w)

private theorem etaWeights_loop (n a len : ℕ) (o : List (ℕ × ℚ)) :
    (forIn (m := Id) (List.range' a len) (n.choose a, ∑ i ∈ Finset.range a, n.choose i, o)
      fun k (s : ℕ × ℕ × List (ℕ × ℚ)) => pure (ForInStep.yield
        (s.1 * (n - k) / (k + 1), s.2.1 + s.1,
          (k + 1, if k % 2 = 0 then ((2 ^ n - (s.2.1 + s.1) : ℕ) : ℚ) / ((2 ^ n : ℕ) : ℚ)
            else -(((2 ^ n - (s.2.1 + s.1) : ℕ) : ℚ) / ((2 ^ n : ℕ) : ℚ))) :: s.2.2))) =
      (n.choose (a+len), ∑ i ∈ Finset.range (a+len), n.choose i,
        ((List.range' a len).map (etaEntry n)).reverse ++ o) := by
  induction len generalizing a o with
  | zero => rfl
  | succ len ih =>
    rw [List.range'_succ, List.forIn_cons]
    have hc : n.choose a * (n - a) / (a + 1) = n.choose (a+1) := by
      rw [← Nat.choose_succ_right_eq]; simp
    have hs : ∑ i ∈ Finset.range a, n.choose i + n.choose a =
        ∑ i ∈ Finset.range (a+1), n.choose i := by
      rw [Finset.sum_range_succ]
    have := ih (a+1) ((a + 1, if a % 2 = 0 then
        ((2 ^ n - ∑ i ∈ Finset.range (a + 1), n.choose i : ℕ) : ℚ) / ((2 ^ n : ℕ) : ℚ)
      else -(((2 ^ n - ∑ i ∈ Finset.range (a + 1), n.choose i : ℕ) : ℚ) / ((2 ^ n : ℕ) : ℚ)))
        :: o)
    simp only [pure, bind] at this ⊢
    rw [hc, hs, this]
    simp [etaEntry, Nat.add_assoc, Nat.add_comm 1 len]

private theorem etaWeights_eq (n : ℕ) : etaWeights n = (List.range n).map (etaEntry n) := by
  unfold etaWeights
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have := etaWeights_loop n 0 n []
  simp only [Nat.choose_zero_right, Finset.range_zero, Finset.sum_empty, zero_add,
    List.append_nil] at this
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [List.range_eq_range']
  erw [this]
  exact List.reverse_reverse _

/-! ### The Euler series -/

open Filter Topology MeasureTheory

/-- The `j`-th term of the Euler transform: `∑_{i ≤ j} (-1)^i C(j,i) (i+1)^{-s}`. -/
private noncomputable def etaDelta (j : ℕ) (s : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (j+1), (-1:ℂ)^i * (j.choose i : ℂ) * ((i+1 : ℕ) : ℂ)^(-s)

private theorem partial_choose_succ (n i : ℕ) :
    ∑ l ∈ Finset.range (i+1), (n+1).choose l + n.choose i =
      2 * ∑ l ∈ Finset.range (i+1), n.choose l := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun l => n.choose l), Nat.choose_succ_succ']
    linarith

private theorem partial_choose_le (n i : ℕ) : ∑ l ∈ Finset.range (i+1), n.choose l ≤ 2^n := by
  rcases le_or_gt (i+1) (n+1) with h | h
  · rw [← Nat.sum_range_choose]
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)
  · rw [← Nat.sum_range_choose]
    rw [← Finset.sum_range_add_sum_Ico _ h.le]
    have : ∑ k ∈ Finset.Ico (n+1) (i+1), n.choose k = 0 :=
      Finset.sum_eq_zero fun k hk => Nat.choose_eq_zero_of_lt (by simp at hk; omega)
    omega

private theorem choose_geom_sum (n i : ℕ) :
    ∑ j ∈ Finset.range n, (j.choose i : ℝ) / 2^(j+1) =
      ((2^n - ∑ l ∈ Finset.range (i+1), n.choose l : ℕ) : ℝ) / 2^n := by
  induction n with
  | zero => simp [Finset.sum_range_succ']
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.cast_sub (partial_choose_le _ _),
      Nat.cast_sub (partial_choose_le _ _)]
    have h := partial_choose_succ n i
    have h' : ((∑ l ∈ Finset.range (i+1), (n+1).choose l : ℕ) : ℝ) =
        2 * ((∑ l ∈ Finset.range (i+1), n.choose l : ℕ) : ℝ) - (n.choose i : ℝ) := by
      rw [eq_sub_iff_add_eq]; exact_mod_cast h
    rw [h']
    push_cast
    field_simp
    ring

private theorem list_sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

private theorem etaApproxC_eq_sum (s : ℂ) (n : ℕ) :
    etaApproxC s n = ∑ j ∈ Finset.range n, (1/2:ℂ)^(j+1) * etaDelta j s := by
  unfold etaApproxC
  rw [etaWeights_eq, List.map_map, list_sum_map_range]
  unfold etaDelta
  have h1 : ∀ j ∈ Finset.range n, (1/2:ℂ)^(j+1) * ∑ i ∈ Finset.range (j+1),
      (-1:ℂ)^i * (j.choose i : ℂ) * ((i+1 : ℕ) : ℂ)^(-s) =
      ∑ i ∈ Finset.range n, (1/2:ℂ)^(j+1) *
        ((-1:ℂ)^i * (j.choose i : ℂ) * ((i+1 : ℕ) : ℂ)^(-s)) := by
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_subset
    · intro i hi; simp at hi hj ⊢; omega
    · intro i _ hi
      simp at hi
      simp [Nat.choose_eq_zero_of_lt (show j < i by omega)]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 := choose_geom_sum n i
  have h3 : ∑ j ∈ Finset.range n, (1/2:ℂ)^(j+1) *
      ((-1:ℂ)^i * (j.choose i : ℂ) * ((i+1 : ℕ) : ℂ)^(-s)) =
      (-1:ℂ)^i * ((i+1 : ℕ) : ℂ)^(-s) *
        ((∑ j ∈ Finset.range n, (j.choose i : ℝ) / 2^(j+1) : ℝ) : ℂ) := by
    push_cast; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_div, inv_pow]; field_simp
  rw [h3, h2]
  simp only [Function.comp_apply, etaEntry]
  split_ifs with h
  · rw [Even.neg_one_pow (Nat.even_iff.2 h)]
    push_cast; ring
  · rw [Odd.neg_one_pow (Nat.odd_iff.2 (by omega))]
    push_cast; ring

/-! ### Bounding `Δ_j` through a Laplace integral -/

section PsiBound

open Polynomial

private noncomputable def etaB (j i : ℕ) : ℝ[X] := X^(i+1) * (1 - X)^(j-i)

private noncomputable def etaQ (j : ℕ) (c : ℕ → ℝ) : ℝ[X] :=
  ∑ i ∈ Finset.range (j+1), C (c i) * etaB j i

private noncomputable def etaT (j : ℕ) (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => c 0
  | i+1 => (i+2) * c (i+1) - ((j - i : ℕ) : ℝ) * c i

private noncomputable def etaP (j m : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (j+1), C ((-1:ℝ)^i * (j.choose i : ℝ) * ((i+1 : ℕ) : ℝ)^m) * X^(i+1)

private theorem X_mul_derivative_etaB (j i : ℕ) :
    X * derivative (etaB j i) = C ((i:ℝ)+1) * etaB j i - C ((j - i : ℕ) : ℝ) * etaB j (i+1) := by
  unfold etaB
  rcases h : j - i with _ | k
  · have h' : j - (i+1) = 0 := by omega
    simp [h']
    ring
  · have h' : j - (i+1) = k := by omega
    rw [h', derivative_mul, derivative_X_pow, derivative_pow]
    simp only [derivative_sub, derivative_one, derivative_X, zero_sub]
    push_cast
    simp only [map_add, map_natCast, map_one]
    ring

private theorem X_mul_derivative_etaQ (j : ℕ) (c : ℕ → ℝ) :
    X * derivative (etaQ j c) = etaQ j (etaT j c) := by
  unfold etaQ
  rw [derivative_sum, Finset.mul_sum]
  have h1 : ∀ i ∈ Finset.range (j+1), X * derivative (C (c i) * etaB j i) =
      C ((i+1) * c i) * etaB j i - C (((j - i : ℕ) : ℝ) * c i) * etaB j (i+1) := by
    intro i _
    rw [derivative_C_mul, ← mul_assoc, mul_comm X, mul_assoc, X_mul_derivative_etaB]
    simp only [map_mul]; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ' (fun i => C (etaT j c i) * etaB j i)]
  rw [Finset.sum_range_succ' (fun i => C ((↑i + 1) * c i) * etaB j i)]
  rw [Finset.sum_range_succ (fun i => C (((j - i : ℕ) : ℝ) * c i) * etaB j (i+1))]
  simp only [Nat.sub_self, Nat.cast_zero, zero_mul, map_zero, add_zero, etaT]
  push_cast
  simp only [map_sub, map_mul, sub_mul]
  rw [Finset.sum_sub_distrib]
  simp only [map_add, map_natCast, map_one, map_ofNat]
  ring_nf
  simp

private theorem X_mul_derivative_etaP (j m : ℕ) : X * derivative (etaP j m) = etaP j (m+1) := by
  unfold etaP
  rw [derivative_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [derivative_C_mul, derivative_X_pow]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  push_cast
  ring

private theorem etaP_zero (j : ℕ) : etaP j 0 = etaQ j (fun i => if i = 0 then 1 else 0) := by
  unfold etaP etaQ etaB
  conv_rhs => rw [Finset.sum_eq_single 0 (by intro b _ hb; simp [hb]) (by simp)]
  simp only [pow_zero, mul_one, ite_true, map_one, one_mul, zero_add, pow_one, Nat.sub_zero]
  rw [sub_eq_add_neg, add_comm (1:ℝ[X]), add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (C ((-1:ℝ) ^ i * (j.choose i : ℝ)) : ℝ[X]) = (-1) ^ i * (j.choose i : ℝ[X]) := by
    rw [C_mul, C_pow, C_neg, C_1, map_natCast]
  rw [one_pow, mul_one, this, neg_pow (X : ℝ[X])]
  ring

private theorem etaP_eq_etaQ (j m : ℕ) : ∃ c : ℕ → ℝ, etaP j m = etaQ j c ∧
    ∑ i ∈ Finset.range (j+1), |c i| ≤ ((j:ℝ)+1)^m := by
  induction m with
  | zero =>
    refine ⟨_, etaP_zero j, ?_⟩
    rw [Finset.sum_eq_single 0 (by intro b _ hb; simp [hb]) (by simp)]
    simp
  | succ m ih =>
    obtain ⟨c, hc, hb⟩ := ih
    refine ⟨etaT j c, ?_, ?_⟩
    · rw [← X_mul_derivative_etaP, hc, X_mul_derivative_etaQ]
    · have h1 : ∀ i ∈ Finset.range j, |etaT j c (i+1)| ≤
          ((i+1:ℕ):ℝ) * |c (i+1)| + |c (i+1)| + ((j - i : ℕ) : ℝ) * |c i| := by
        intro i _
        simp only [etaT]
        calc |((i:ℝ) + 2) * c (i+1) - ((j - i : ℕ) : ℝ) * c i|
            ≤ |((i:ℝ) + 2) * c (i+1)| + |((j - i : ℕ) : ℝ) * c i| := abs_sub _ _
          _ = _ := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ i + 2),
              abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (j - i))]
            push_cast; ring
      have h2 : ∑ i ∈ Finset.range (j+1), |etaT j c i| ≤
          ∑ i ∈ Finset.range (j+1), (((i:ℕ):ℝ) * |c i| + |c i|) +
            ∑ i ∈ Finset.range (j+1), ((j - i : ℕ) : ℝ) * |c i| := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun i => (((i:ℕ):ℝ) * |c i| + |c i|)),
          Finset.sum_range_succ (fun i => ((j - i : ℕ) : ℝ) * |c i|)]
        have := Finset.sum_le_sum h1
        rw [Finset.sum_add_distrib] at this
        simp only [etaT, Nat.sub_self, zero_mul, add_zero, CharP.cast_eq_zero,
          zero_add] at this ⊢
        linarith
      have h3 : ∑ i ∈ Finset.range (j+1), (((i:ℕ):ℝ) * |c i| + |c i|) +
            ∑ i ∈ Finset.range (j+1), ((j - i : ℕ) : ℝ) * |c i| =
          ((j:ℝ)+1) * ∑ i ∈ Finset.range (j+1), |c i| := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have : i ≤ j := by simp at hi; omega
        rw [Nat.cast_sub this]; ring
      rw [pow_succ]
      calc _ ≤ _ := h2
        _ = _ := h3
        _ ≤ ((j:ℝ)+1) * ((j:ℝ)+1)^m := by gcongr
        _ = _ := by ring


private noncomputable def etaPsi (j m : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (j+1),
    (-1:ℝ)^i * (j.choose i : ℝ) * ((i+1 : ℕ) : ℝ)^m * Real.exp (-((i+1 : ℕ) * t))

private theorem abs_eval_etaQ_le (j : ℕ) (c : ℕ → ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |(etaQ j c).eval x| ≤ (∑ i ∈ Finset.range (j+1), |c i|) * x := by
  unfold etaQ etaB
  rw [eval_finsetSum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one, abs_mul]
  rw [abs_of_nonneg (pow_nonneg hx0 (i+1)), abs_of_nonneg (pow_nonneg (sub_nonneg.2 hx1) (j-i))]
  gcongr
  calc x ^ (i+1) * (1-x)^(j-i) ≤ x * 1 := by
        gcongr
        · exact pow_le_of_le_one hx0 hx1 (by omega) |>.trans (by simp)
        · exact pow_le_one₀ (by linarith) (by linarith)
    _ = x := mul_one x

private theorem etaPsi_bound (j m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |etaPsi j m t| ≤ ((j:ℝ)+1)^m * Real.exp (-t) := by
  obtain ⟨c, hc, hb⟩ := etaP_eq_etaQ j m
  have h : etaPsi j m t = (etaP j m).eval (Real.exp (-t)) := by
    unfold etaPsi etaP
    rw [eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [h, hc]
  refine (abs_eval_etaQ_le j c (Real.exp_pos _).le ?_).trans ?_
  · exact Real.exp_le_one_iff.2 (by linarith)
  · gcongr

end PsiBound

private theorem gamma_mul_etaDelta (j m : ℕ) (s : ℂ) (h : 0 < s.re + m) :
    Complex.Gamma (s + m) * etaDelta j s = mellin (fun t => (etaPsi j m t : ℂ)) (s + m) := by
  have hs : 0 < (s + m).re := by simpa using h
  set a : ℕ → ℂ := fun i => (-1:ℂ)^i * (j.choose i : ℂ) * ((i+1 : ℕ) : ℂ)^m with ha
  have hsupp : ∀ i ∉ Finset.range (j+1), a i = 0 := by
    intro i hi
    simp only [Finset.mem_range, not_lt] at hi
    simp [ha, Nat.choose_eq_zero_of_lt (show j < i by omega)]
  have key := hasSum_mellin (a := a) (p := fun i => ((i+1 : ℕ) : ℝ))
    (F := fun t => (etaPsi j m t : ℂ)) (s := s + m) (fun i => Or.inr (by positivity)) hs
    (fun t _ => by
      have : HasSum (fun i => a i * Real.exp (-((i+1 : ℕ) : ℝ) * t))
          (∑ i ∈ Finset.range (j+1), a i * Real.exp (-((i+1 : ℕ) : ℝ) * t)) :=
        hasSum_sum_of_ne_finset_zero (fun i hi => by simp [hsupp i hi])
      convert this using 1
      unfold etaPsi
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ha]; push_cast; ring_nf)
    (summable_of_ne_finset_zero (s := Finset.range (j+1)) (fun i hi => by simp [hsupp i hi]))
  rw [← key.tsum_eq, tsum_eq_sum (s := Finset.range (j+1)) (fun i hi => by simp [hsupp i hi]),
    etaDelta, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hne : ((i+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero i)
  simp only [ha]
  push_cast
  rw [Complex.cpow_add _ _ (by exact_mod_cast hne), Complex.cpow_natCast, Complex.cpow_neg]
  field_simp

private theorem norm_gamma_mul_etaDelta_le (j m : ℕ) (s : ℂ) (h : 0 < s.re + m) :
    ‖Complex.Gamma (s + m)‖ * ‖etaDelta j s‖ ≤ ((j:ℝ)+1)^m * Real.Gamma (s.re + m) := by
  rw [← norm_mul, gamma_mul_etaDelta j m s h, mellin, Real.Gamma_eq_integral h,
    ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((Real.GammaIntegral_convergent h).const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
    Real.norm_eq_abs]
  have := etaPsi_bound j m ht.le
  have h2 : (s + m - 1).re = s.re + m - 1 := by simp
  rw [h2]
  calc t ^ (s.re + m - 1) * |etaPsi j m t| ≤ t ^ (s.re + m - 1) * (((j:ℝ)+1)^m * Real.exp (-t)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

private theorem sum_inv_sq_le (x : ℝ) (hx : 0 < x) (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), ((x + k)^2)⁻¹ ≤ x⁻¹^2 + x⁻¹ - (x + n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : ((x + ((n+1 : ℕ) : ℝ))^2)⁻¹ ≤ (x + n)⁻¹ - (x + ((n+1:ℕ):ℝ))⁻¹ := by
      push_cast
      have hxn : 0 < x + n := by positivity
      rw [inv_sub_inv hxn.ne' (by positivity), inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

private theorem norm_add_nat_le (x y : ℝ) (k : ℕ) (hx : 0 < x) :
    ‖((x:ℂ) + y * Complex.I) + k‖ ≤ (x + k) * Real.exp (y^2 / 2 * ((x+k)^2)⁻¹) := by
  have hxk : 0 < x + k := by positivity
  have : ((x:ℂ) + y * Complex.I) + k = ((x + k : ℝ) : ℂ) + y * Complex.I := by push_cast; ring
  rw [this, Complex.norm_add_mul_I, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h2 : Real.exp (y^2 / 2 * ((x+k)^2)⁻¹)^2 = Real.exp (y^2 * ((x+k)^2)⁻¹) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have h3 := Real.add_one_le_exp (y^2 * ((x+k)^2)⁻¹)
  rw [mul_pow, h2]
  have h4 : (x + k)^2 + y^2 = (x+k)^2 * (y^2 * ((x+k)^2)⁻¹ + 1) := by
    field_simp; ring
  rw [h4]
  gcongr

/-- The Gamma ratio bound coming from the Weierstrass product. -/
private theorem real_gamma_le_exp_mul_norm_gamma (x y : ℝ) (hx : 0 < x) :
    Real.Gamma x ≤
      Real.exp (y^2/2 * (x⁻¹^2 + x⁻¹)) * ‖Complex.Gamma (x + y * Complex.I)‖ := by
  set w : ℂ := x + y * Complex.I with hw
  have h1 := (Complex.GammaSeq_tendsto_Gamma (x:ℂ)).norm
  have h2 := ((Complex.GammaSeq_tendsto_Gamma w).norm).const_mul (Real.exp (y^2/2 * (x⁻¹^2 + x⁻¹)))
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.Gamma_pos_of_pos hx).le] at h1
  refine le_of_tendsto_of_tendsto h1 h2 (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : 0 < n := hn
  simp only [Complex.GammaSeq]
  rw [norm_div, norm_div, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn0,
    Complex.norm_natCast_cpow_of_pos hn0, norm_prod, norm_prod]
  have hwre : w.re = x := by simp [hw]
  rw [hwre, Complex.ofReal_re]
  have hP : ∀ k ∈ Finset.range (n+1), ‖(x:ℂ) + k‖ = x + k := by
    intro k _
    rw [show (x:ℂ) + k = ((x + k : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [Finset.prod_congr rfl hP]
  have hQ : ∏ k ∈ Finset.range (n+1), ‖w + k‖ ≤
      (∏ k ∈ Finset.range (n+1), (x + k)) * Real.exp (y^2/2 * (x⁻¹^2 + x⁻¹)) := by
    calc ∏ k ∈ Finset.range (n+1), ‖w + k‖
        ≤ ∏ k ∈ Finset.range (n+1), ((x + k) * Real.exp (y^2 / 2 * ((x+k)^2)⁻¹)) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => norm_add_nat_le x y k hx
      _ = (∏ k ∈ Finset.range (n+1), (x + k)) *
            Real.exp (y^2 / 2 * ∑ k ∈ Finset.range (n+1), ((x+k)^2)⁻¹) := by
          rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]
      _ ≤ _ := by
          gcongr
          have := sum_inv_sq_le x hx n
          have : 0 < (x + n)⁻¹ := by positivity
          linarith
  have hPpos : 0 < ∏ k ∈ Finset.range (n+1), (x + (k:ℝ)) :=
    Finset.prod_pos fun k _ => by positivity
  have hQpos : 0 < ∏ k ∈ Finset.range (n+1), ‖w + k‖ := by
    refine Finset.prod_pos fun k _ => norm_pos_iff.2 ?_
    intro h0
    have := congrArg Complex.re h0
    simp [hw] at this
    linarith [show (0:ℝ) ≤ k from Nat.cast_nonneg k]
  have hA : 0 ≤ (n:ℝ)^x * ‖((n.factorial : ℕ) : ℂ)‖ := by positivity
  rw [mul_div_assoc', le_div_iff₀ hQpos, div_mul_eq_mul_div, div_le_iff₀ hPpos]
  calc (n:ℝ)^x * ‖((n.factorial : ℕ) : ℂ)‖ * ∏ k ∈ Finset.range (n+1), ‖w + k‖
      ≤ (n:ℝ)^x * ‖((n.factorial : ℕ) : ℂ)‖ *
        ((∏ k ∈ Finset.range (n+1), (x + k)) * Real.exp (y^2/2 * (x⁻¹^2 + x⁻¹))) :=
        mul_le_mul_of_nonneg_left hQ hA
    _ = _ := by ring

private theorem norm_etaDelta_le (j m : ℕ) (s : ℂ) (h : 0 < s.re + m) :
    ‖etaDelta j s‖ ≤
      ((j:ℝ)+1)^m * Real.exp (s.im^2/2 * ((s.re+m)⁻¹^2 + (s.re+m)⁻¹)) := by
  have hG := norm_gamma_mul_etaDelta_le j m s h
  have hR := real_gamma_le_exp_mul_norm_gamma (s.re + m) s.im h
  have hs : (((s.re + m : ℝ) : ℂ) + (s.im : ℂ) * Complex.I) = s + m := by
    apply Complex.ext <;> simp
  rw [hs] at hR
  have hpos : 0 < ‖Complex.Gamma (s + m)‖ :=
    norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by simpa using h))
  have hj : (0:ℝ) ≤ ((j:ℝ)+1)^m := by positivity
  have := hG.trans (mul_le_mul_of_nonneg_left hR hj)
  rw [mul_comm ‖Complex.Gamma (s + m)‖, ← mul_assoc] at this
  exact le_of_mul_le_mul_right this hpos

/-! ### The Euler series represents eta everywhere -/

private theorem differentiable_etaDelta (j : ℕ) : Differentiable ℂ (etaDelta j) := by
  intro s
  unfold etaDelta
  refine DifferentiableAt.fun_sum fun i _ => ?_
  refine (differentiableAt_const _).mul ?_
  exact (differentiableAt_id.neg).const_cpow (Or.inl (Nat.cast_ne_zero.2 (Nat.succ_ne_zero i)))

private theorem summable_geom_pow (m : ℕ) :
    Summable fun j : ℕ => (1/2:ℝ)^(j+1) * ((j:ℝ)+1)^m := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) m (r := 1/2) (by norm_num)
  have := (summable_nat_add_iff 1).2 h
  convert this using 2 with j
  push_cast; ring

private theorem norm_euler_term_le (j m : ℕ) (s : ℂ) (h : 0 < s.re + m) :
    ‖(1/2:ℂ)^(j+1) * etaDelta j s‖ ≤
      Real.exp (s.im^2/2 * ((s.re+m)⁻¹^2 + (s.re+m)⁻¹)) * ((1/2:ℝ)^(j+1) * ((j:ℝ)+1)^m) := by
  rw [norm_mul, norm_pow, norm_div, norm_one, Complex.norm_ofNat]
  have := norm_etaDelta_le j m s h
  calc (1/2:ℝ)^(j+1) * ‖etaDelta j s‖ ≤ (1/2:ℝ)^(j+1) *
        (((j:ℝ)+1)^m * Real.exp (s.im^2/2 * ((s.re+m)⁻¹^2 + (s.re+m)⁻¹))) := by gcongr
    _ = _ := by ring

private theorem summable_etaDelta (s : ℂ) : Summable fun j => (1/2:ℂ)^(j+1) * etaDelta j s := by
  obtain ⟨m, hm⟩ := exists_nat_gt (-s.re)
  refine Summable.of_norm_bounded ((summable_geom_pow m).mul_left
    (Real.exp (s.im^2/2 * ((s.re+m)⁻¹^2 + (s.re+m)⁻¹)))) fun j => ?_
  exact norm_euler_term_le j m s (by linarith)

private theorem differentiable_eulerSeries :
    Differentiable ℂ (fun s => ∑' j, (1/2:ℂ)^(j+1) * etaDelta j s) := by
  intro s0
  obtain ⟨m, hm⟩ := exists_nat_gt (2 - s0.re)
  set C := Real.exp ((|s0.im| + 1)^2) with hC
  have hU : DifferentiableOn ℂ (fun s => ∑' j, (1/2:ℂ)^(j+1) * etaDelta j s) (Metric.ball s0 1) := by
    refine Complex.differentiableOn_tsum_of_summable_norm ((summable_geom_pow m).mul_left C)
      (fun j => ((differentiable_etaDelta j).const_mul _).differentiableOn) Metric.isOpen_ball ?_
    intro j w hw
    have hd : ‖w - s0‖ < 1 := by simpa [dist_eq_norm] using hw
    have hre : |w.re - s0.re| < 1 := by
      have := Complex.abs_re_le_norm (w - s0); simp at this; linarith
    have him : |w.im - s0.im| < 1 := by
      have := Complex.abs_im_le_norm (w - s0); simp at this; linarith
    have hx : 1 ≤ w.re + m := by
      have := (abs_lt.1 hre).1; linarith
    refine (norm_euler_term_le j m w (by linarith)).trans ?_
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
    have h1 : (w.re + m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
    have h2 : (w.re + m)⁻¹^2 + (w.re + m)⁻¹ ≤ 2 := by
      have : 0 ≤ (w.re + m)⁻¹ := by positivity
      nlinarith
    have h3 : w.im^2 ≤ (|s0.im| + 1)^2 := by
      have : |w.im| ≤ |s0.im| + 1 := by
        have := abs_sub_abs_le_abs_sub w.im s0.im; linarith
      rw [← sq_abs]; gcongr
    have h4 : 0 ≤ w.im^2 := sq_nonneg _
    calc w.im^2/2 * ((w.re + m)⁻¹^2 + (w.re + m)⁻¹) ≤ w.im^2/2 * 2 := by gcongr
      _ ≤ (|s0.im| + 1)^2 := by linarith
  exact (hU s0 (Metric.mem_ball_self one_pos)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))

private theorem summable_nat_succ_cpow_neg (s : ℂ) (hs : 1 < s.re) :
    Summable fun k : ℕ => ((k+1 : ℕ) : ℂ)^(-s) := by
  have h := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hs)
  convert h using 2 with k
  rw [Complex.cpow_neg, one_div]

private theorem dirichletEta_eq_alt (s : ℂ) (hs : 1 < s.re) :
    Complex.dirichletEta s = ∑' k : ℕ, (-1:ℂ)^k * ((k+1 : ℕ) : ℂ)^(-s) := by
  set a : ℕ → ℂ := fun k => ((k+1 : ℕ) : ℂ)^(-s) with ha
  have hA : Summable a := summable_nat_succ_cpow_neg s hs
  have hAn : Summable fun k => ‖a k‖ := by
    have : Summable fun k : ℕ => ((k:ℝ)+1)^(-s.re) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (show -s.re < -1 by linarith))
      convert this using 2 with k; push_cast; ring_nf
    convert this using 2 with k
    simp only [ha]
    rw [show ((k+1 : ℕ) : ℂ) = (((k:ℝ)+1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
  have hinj2 : Function.Injective fun k : ℕ => 2 * k := fun x y h => by simpa using h
  have hinj2' : Function.Injective fun k : ℕ => 2 * k + 1 := fun x y h => by simpa using h
  have hE : Summable fun k => a (2*k) := (hAn.comp_injective hinj2).of_norm
  have hO : Summable fun k => a (2*k+1) := (hAn.comp_injective hinj2').of_norm
  have hodd : ∀ k, a (2*k+1) = (2:ℂ)^(-s) * a k := by
    intro k
    simp only [ha]
    rw [show ((2*k+1+1 : ℕ) : ℂ) = ((2:ℝ):ℂ) * (((k+1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
      Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    push_cast; rfl
  have hz : riemannZeta s = ∑' k, a k := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    refine tsum_congr fun k => ?_
    simp only [ha]; push_cast; rw [Complex.cpow_neg, one_div]
  have h1 : ∑' k, a k = ∑' k, a (2*k) + ∑' k, a (2*k+1) := (tsum_even_add_odd hE hO).symm
  have h2 : ∑' k : ℕ, (-1:ℂ)^k * a k = ∑' k, a (2*k) - ∑' k, a (2*k+1) := by
    rw [← tsum_even_add_odd (f := fun k => (-1:ℂ)^k * a k)]
    · have he : ∀ k, (-1:ℂ)^(2*k) * a (2*k) = a (2*k) := fun k => by simp [pow_mul]
      have ho : ∀ k, (-1:ℂ)^(2*k+1) * a (2*k+1) = -a (2*k+1) := fun k => by
        simp [pow_succ, pow_mul]
      rw [tsum_congr he, tsum_congr ho, tsum_neg, sub_eq_add_neg]
    · simpa [pow_mul] using hE
    · simpa [pow_mul, pow_succ] using hO.neg
  have h3 : ∑' k, a (2*k+1) = (2:ℂ)^(-s) * riemannZeta s := by
    rw [hz, ← tsum_mul_left]; exact tsum_congr hodd
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  simp only [Complex.dirichletEta, hs1, ite_false]
  rw [h2]
  have h4 : ∑' k, a (2*k) = riemannZeta s - (2:ℂ)^(-s) * riemannZeta s := by
    rw [← h3, hz, h1]; ring
  rw [h4, h3, show (1:ℂ) - s = 1 + (-s) by ring,
    Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  ring


private theorem hasSum_choose_half (k : ℕ) :
    HasSum (fun j : ℕ => (1/2:ℝ)^(j+1) * (j.choose k : ℝ)) 1 := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) k (r := 1/2) (by norm_num)
  have h2 : HasSum (fun n : ℕ => (1/2:ℝ)^(n + k + 1) * ((n + k).choose k : ℝ)) 1 := by
    convert h.mul_left ((1/2:ℝ)^(k+1)) using 1
    · funext n; rw [pow_add, pow_add]; ring
    · norm_num
  rw [← hasSum_nat_add_iff' k]
  convert h2 using 1
  rw [Finset.sum_eq_zero fun i hi => by
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hi)]]
  simp

private theorem alt_eq_eulerSeries (s : ℂ) (hs : 1 < s.re) :
    ∑' k : ℕ, (-1:ℂ)^k * ((k+1 : ℕ) : ℂ)^(-s) = ∑' j, (1/2:ℂ)^(j+1) * etaDelta j s := by
  set a : ℕ → ℂ := fun k => ((k+1 : ℕ) : ℂ)^(-s) with ha
  set F : ℕ → ℕ → ℂ := fun j k => (1/2:ℂ)^(j+1) * ((-1:ℂ)^k * (j.choose k : ℂ) * a k) with hF
  have hAn : Summable fun k => ‖a k‖ := by
    have : Summable fun k : ℕ => ((k:ℝ)+1)^(-s.re) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (show -s.re < -1 by linarith))
      convert this using 2 with k; push_cast; ring_nf
    convert this using 2 with k
    simp only [ha]
    rw [show ((k+1 : ℕ) : ℂ) = (((k:ℝ)+1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
  have hnorm : ∀ j k, ‖F j k‖ = (1/2:ℝ)^(j+1) * (j.choose k : ℝ) * ‖a k‖ := by
    intro j k
    simp only [hF, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast,
      norm_div, Complex.norm_ofNat]
    ring
  have hsum : Summable (Function.uncurry F) := by
    refine Summable.of_norm ?_
    rw [← (Equiv.prodComm ℕ ℕ).summable_iff]
    refine (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2 ⟨fun k => ?_, ?_⟩
    · simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair, hnorm]
      exact ((hasSum_choose_half k).mul_right ‖a k‖).summable
    · convert hAn using 1
      funext k
      simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair, hnorm]
      exact ((hasSum_choose_half k).mul_right ‖a k‖).tsum_eq.trans (one_mul _)
  have hinner : ∀ k, ∑' j, F j k = (-1:ℂ)^k * a k := by
    intro k
    have h' : HasSum (fun j => F j k) ((-1:ℂ)^k * a k) := by
      have := ((Complex.ofRealCLM.hasSum (hasSum_choose_half k)).mul_right ((-1:ℂ)^k * a k))
      convert this using 1
      · funext j; simp only [hF, Complex.ofRealCLM_apply]; push_cast; ring
      · simp
    exact h'.tsum_eq
  have houter : ∀ j, ∑' k, F j k = (1/2:ℂ)^(j+1) * etaDelta j s := by
    intro j
    rw [tsum_eq_sum (s := Finset.range (j+1)) (fun k hk => by
      simp only [Finset.mem_range, not_lt] at hk
      simp [hF, Nat.choose_eq_zero_of_lt (show j < k by omega)])]
    rw [etaDelta, Finset.mul_sum]
  rw [← tsum_congr hinner, hsum.tsum_comm]
  exact tsum_congr houter


private theorem dirichletEta_eq_eulerSeries (s : ℂ) :
    Complex.dirichletEta s = ∑' j, (1/2:ℂ)^(j+1) * etaDelta j s := by
  have hη : AnalyticOnNhd ℂ Complex.dirichletEta Set.univ := fun z _ => analyticAt_dirichletEta z
  have hT : AnalyticOnNhd ℂ (fun s => ∑' j, (1/2:ℂ)^(j+1) * etaDelta j s) Set.univ :=
    differentiable_eulerSeries.differentiableOn.analyticOnNhd isOpen_univ
  have heq : Complex.dirichletEta =ᶠ[𝓝 2] (fun s => ∑' j, (1/2:ℂ)^(j+1) * etaDelta j s) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1:ℝ) < (2:ℂ).re by norm_num)] with z hz
    rw [dirichletEta_eq_alt z hz, alt_eq_eulerSeries z hz]
  exact hη.eqOn_of_preconnected_of_eventuallyEq hT isPreconnected_univ (Set.mem_univ 2) heq
    (Set.mem_univ s)

/-! ### The truncation error -/

private theorem exp_quarter_le : Real.exp (1/4) ≤ 3/2 := by
  have h1 : Real.exp (1/4) ^ 4 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 : Real.exp (1/4) ^ 4 ≤ (3/2 : ℝ)^4 := by rw [h1]; norm_num at h2 ⊢; linarith
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num)).1 h3

private theorem succ_pow_le (m N : ℕ) (h : 4 * m ≤ N + 1) :
    ((N:ℝ) + 2)^m ≤ 3/2 * ((N:ℝ) + 1)^m := by
  have hN : (0:ℝ) < N + 1 := by positivity
  have e1 : ((N:ℝ) + 2) = (N + 1) * (1 + 1/(N+1)) := by field_simp; ring
  rw [e1, mul_pow, mul_comm (3/2 : ℝ)]
  gcongr
  calc (1 + 1/((N:ℝ)+1))^m ≤ (Real.exp (1/((N:ℝ)+1)))^m := by
        gcongr; linarith [Real.add_one_le_exp (1/((N:ℝ)+1))]
    _ = Real.exp (m/((N:ℝ)+1)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (1/4) := by
        refine Real.exp_le_exp.2 ?_
        rw [div_le_iff₀ hN]
        have : (4 * m : ℝ) ≤ N + 1 := by exact_mod_cast h
        linarith
    _ ≤ 3/2 := exp_quarter_le

private theorem euler_tail_bound (m n : ℕ) (hn : 4*m ≤ n) :
    Summable (fun j : ℕ => (1/2:ℝ)^(n+j+1) * (((n+j:ℕ):ℝ)+1)^m) ∧
    ∑' j : ℕ, (1/2:ℝ)^(n+j+1) * (((n+j:ℕ):ℝ)+1)^m ≤ 2 * ((n:ℝ)+1)^m / 2^n := by
  set t : ℕ → ℝ := fun j => (1/2:ℝ)^(n+j+1) * (((n+j:ℕ):ℝ)+1)^m with ht
  have hstep : ∀ j, t (j+1) ≤ 3/4 * t j := by
    intro j
    simp only [ht]
    have := succ_pow_le m (n+j) (by omega)
    have e : (((n+(j+1):ℕ):ℝ)+1) = ((n+j:ℕ):ℝ) + 2 := by push_cast; ring
    rw [e, show n + (j+1) + 1 = (n+j+1) + 1 by ring, pow_succ]
    have hp : (0:ℝ) ≤ (1/2)^(n+j+1) := by positivity
    calc (1/2:ℝ)^(n+j+1) * (1/2) * (((n+j:ℕ):ℝ) + 2)^m
        ≤ (1/2:ℝ)^(n+j+1) * (1/2) * (3/2 * (((n+j:ℕ):ℝ) + 1)^m) := by gcongr
      _ = _ := by ring
  have hgeom : ∀ j, t j ≤ t 0 * (3/4)^j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc t (j+1) ≤ 3/4 * t j := hstep j
        _ ≤ 3/4 * (t 0 * (3/4)^j) := by gcongr
        _ = _ := by ring
  have hnn : ∀ j, 0 ≤ t j := fun j => by positivity
  have hsum : Summable (fun j : ℕ => t 0 * (3/4:ℝ)^j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hS : Summable t := Summable.of_nonneg_of_le hnn hgeom hsum
  refine ⟨hS, ?_⟩
  calc ∑' j, t j ≤ ∑' j, t 0 * (3/4:ℝ)^j := hS.tsum_le_tsum hgeom hsum
    _ = t 0 * 4 := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
    _ = _ := by
        simp only [ht, Nat.add_zero]
        rw [pow_succ, one_div, inv_pow]
        field_simp
        ring

private theorem eta_euler_error_aux (s : ℂ) (m n : ℕ) (hm : 0 < s.re + m) (hn : 4*m ≤ n) :
    ‖Complex.dirichletEta s - etaApproxC s n‖ ≤
      2 * Real.exp (s.im^2/2 * ((s.re+m)⁻¹^2 + (s.re+m)⁻¹)) *
        (n+1 : ℝ)^m / 2^n := by
  set E := Real.exp (s.im^2/2 * ((s.re+m)⁻¹^2 + (s.re+m)⁻¹)) with hE
  set f : ℕ → ℂ := fun j => (1/2:ℂ)^(j+1) * etaDelta j s with hf
  obtain ⟨hS, hT⟩ := euler_tail_bound m n hn
  have hsplit : Complex.dirichletEta s - etaApproxC s n = ∑' k, f (k + n) := by
    rw [dirichletEta_eq_eulerSeries, etaApproxC_eq_sum, ← Summable.sum_add_tsum_nat_add n
      (summable_etaDelta s)]
    ring
  rw [hsplit]
  have hb : ∀ k, ‖f (k + n)‖ ≤ E * ((1/2:ℝ)^(n+k+1) * (((n+k:ℕ):ℝ)+1)^m) := by
    intro k
    simp only [hf]
    rw [norm_mul, norm_pow, norm_div, norm_one, Complex.norm_ofNat]
    have := norm_etaDelta_le (k+n) m s (by linarith)
    rw [show k + n = n + k by ring] at this ⊢
    rw [← hE] at this
    calc (1/2:ℝ)^(n+k+1) * ‖etaDelta (n+k) s‖ ≤ (1/2:ℝ)^(n+k+1) * ((((n+k:ℕ):ℝ)+1)^m * E) := by
          gcongr
      _ = _ := by ring
  refine (tsum_of_norm_bounded (hS.mul_left E).hasSum hb).trans ?_
  rw [tsum_mul_left]
  calc E * ∑' k : ℕ, (1/2:ℝ)^(n+k+1) * (((n+k:ℕ):ℝ)+1)^m ≤ E * (2 * ((n:ℝ)+1)^m / 2^n) := by
        gcongr
    _ = _ := by ring

end SpecialFunctions


end

section

/-! Proof of the bound `‖η(s) - log 2‖ ≤ ‖s-1‖/(4-‖s-1‖)` for `‖s-1‖ < 4`.

Write `A(s) = etaApproxC s 40` and `h = η - A`.
* By `eta_euler_error_aux` (with `m = 5`, `n = 40`), `‖h‖ ≤ 1/500` on the disc
  `‖s-1‖ < 4`, so by the Schwarz lemma `‖h(s) - h(1)‖ ≤ ‖s-1‖/1000`.
* `A(1+z) = ∑_p (-z)^p/p! · S_p` with `S_p = ∑_i c_i log(i+1)^p` an explicit finite sum.
  A rational interval certificate, checked by the kernel, gives `|S_1| ≤ 0.249` and
  `|S_p|/p! ≤ 4^{-p}` for `2 ≤ p ≤ 42`, using enclosures of `log k` (`k ≤ 40`) that are
  themselves certified through Taylor bounds for `exp`. For `p ≥ 43` the crude bound
  `|S_p| ≤ 4·4^p ≤ p!/4^p` suffices.
* Since `η(1) = log 2`, summing gives `0.25·r + ∑_{p≥2} (r/4)^p = r/(4-r)`.
-/

namespace SpecialFunctions

/-- Upper bound for `exp y`, valid for `0 ≤ y ≤ 1` (Taylor polynomial plus remainder). -/
private def expUpperQ (y : ℚ) : ℚ :=
  ∑ i ∈ Finset.range 30, y^i / (i.factorial : ℚ) + y^30 * (31 / ((30).factorial * 30 : ℚ))

/-- Lower bound for `exp y`, valid for `0 ≤ y`. -/
private def expLowerQ (y : ℚ) : ℚ := ∑ i ∈ Finset.range 30, y^i / (i.factorial : ℚ)

private def etaLogTable : List (ℚ × ℚ) := [
  (0, 0),
  (693147180559945309417231/10^24, 693147180559945309417234/10^24),
  (1098612288668109691395244/10^24, 1098612288668109691395247/10^24),
  (1386294361119890618834463/10^24, 1386294361119890618834466/10^24),
  (1609437912434100374600758/10^24, 1609437912434100374600761/10^24),
  (1791759469228055000812476/10^24, 1791759469228055000812479/10^24),
  (1945910149055313305105351/10^24, 1945910149055313305105354/10^24),
  (2079441541679835928251695/10^24, 2079441541679835928251698/10^24),
  (2197224577336219382790489/10^24, 2197224577336219382790492/10^24),
  (2302585092994045684017990/10^24, 2302585092994045684017993/10^24),
  (2397895272798370544061942/10^24, 2397895272798370544061945/10^24),
  (2484906649788000310229708/10^24, 2484906649788000310229711/10^24),
  (2564949357461536736053486/10^24, 2564949357461536736053489/10^24),
  (2639057329615258614522583/10^24, 2639057329615258614522586/10^24),
  (2708050201102210065996003/10^24, 2708050201102210065996006/10^24),
  (2772588722239781237668927/10^24, 2772588722239781237668930/10^24),
  (2833213344056216080249533/10^24, 2833213344056216080249536/10^24),
  (2890371757896164692207721/10^24, 2890371757896164692207724/10^24),
  (2944438979166440460009026/10^24, 2944438979166440460009029/10^24),
  (2995732273553990993435222/10^24, 2995732273553990993435225/10^24),
  (3044522437723422996500596/10^24, 3044522437723422996500599/10^24),
  (3091042453358315853479174/10^24, 3091042453358315853479177/10^24),
  (3135494215929149690806751/10^24, 3135494215929149690806754/10^24),
  (3178053830347945619646940/10^24, 3178053830347945619646943/10^24),
  (3218875824868200749201517/10^24, 3218875824868200749201520/10^24),
  (3258096538021482045470718/10^24, 3258096538021482045470721/10^24),
  (3295836866004329074185734/10^24, 3295836866004329074185737/10^24),
  (3332204510175203923939815/10^24, 3332204510175203923939818/10^24),
  (3367295829986474027183271/10^24, 3367295829986474027183274/10^24),
  (3401197381662155375413235/10^24, 3401197381662155375413238/10^24),
  (3433987204485146245929163/10^24, 3433987204485146245929166/10^24),
  (3465735902799726547086159/10^24, 3465735902799726547086162/10^24),
  (3496507561466480235457187/10^24, 3496507561466480235457190/10^24),
  (3526360524616161389666765/10^24, 3526360524616161389666768/10^24),
  (3555348061489413679706111/10^24, 3555348061489413679706114/10^24),
  (3583518938456110001624953/10^24, 3583518938456110001624956/10^24),
  (3610917912644224444368094/10^24, 3610917912644224444368097/10^24),
  (3637586159726385769426258/10^24, 3637586159726385769426261/10^24),
  (3663561646129646427448731/10^24, 3663561646129646427448734/10^24),
  (3688879454113936302852454/10^24, 3688879454113936302852457/10^24)]

private def etaLogLo (i : ℕ) : ℚ := (etaLogTable.getD i (0, 0)).1
private def etaLogHi (i : ℕ) : ℚ := (etaLogTable.getD i (0, 0)).2

/-- Coefficient of `(i+1)^{-s}` in `etaApproxC s 40`, divided by `i+1`. -/
private def etaC (i : ℕ) : ℚ := (etaEntry 40 i).2 / ((i:ℚ) + 1)

private def logOK (k : ℕ) (lo hi : ℚ) : Bool :=
  0 ≤ lo && lo ≤ hi && hi ≤ 4 && (expUpperQ (lo/8))^8 ≤ k && (k:ℚ) ≤ (expLowerQ (hi/8))^8

private def etaSL (p : ℕ) : ℚ := ∑ i ∈ Finset.range 40,
  if 0 ≤ etaC i then etaC i * etaLogLo i ^ p else etaC i * etaLogHi i ^ p
private def etaSU (p : ℕ) : ℚ := ∑ i ∈ Finset.range 40,
  if 0 ≤ etaC i then etaC i * etaLogHi i ^ p else etaC i * etaLogLo i ^ p

private def etaBnd (p : ℕ) : ℚ := if p = 1 then 249/1000 else 1/4^p

/- The following enclosures are used only to prove the fixed rational certificate. -/
section EtaCertificate
open Lynth.Interval

private def etaTaylorLowerI (p : ℕ) (y : ℚ) : Ival :=
  Lynth.Interval.EtaProof.horner p (Ival.ofRat p y) (fun i => Ival.ofRat p (1 / (i.factorial : ℚ))) 0 30

private def etaTaylorUpperI (p : ℕ) (y : ℚ) : Ival :=
  Ival.add p (etaTaylorLowerI p y) (Ival.mul p (Ival.npow p (Ival.ofRat p y) 30)
    (Ival.ofRat p (31 / ((30).factorial * 30 : ℚ))))

private theorem etaTaylorLowerI_sound (p : ℕ) (y : ℚ) : (expLowerQ y : ℝ) ∈ etaTaylorLowerI p y := by
  have h := Lynth.Interval.EtaProof.horner_sound (p := p) (Ival.mem_ofRat p y)
    (fun i => Ival.mem_ofRat p (1 / (i.factorial : ℚ))) 0 30
  simpa only [etaTaylorLowerI, expLowerQ, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_one, Rat.cast_mul, Rat.cast_inv, Nat.zero_add, div_eq_mul_inv, one_mul] using h

private theorem etaTaylorUpperI_sound (p : ℕ) (y : ℚ) : (expUpperQ y : ℝ) ∈ etaTaylorUpperI p y := by
  have h := Ival.mem_add (p := p) (etaTaylorLowerI_sound p y)
    (Ival.mem_mul (p := p) (Ival.mem_npow (p := p) (Ival.mem_ofRat p y) 30)
      (Ival.mem_ofRat p (31 / ((30).factorial * 30 : ℚ))))
  simpa only [etaTaylorUpperI, expUpperQ, expLowerQ, Rat.cast_sum, Rat.cast_add,
    Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] using h

private def etaLogIntervalCheck (k : ℕ) (lo hi : ℚ) : Bool :=
  Ival.leB (Ival.npow 96 (etaTaylorUpperI 96 (lo/8)) 8) (Ival.ofRat 96 k) &&
  Ival.leB (Ival.ofRat 96 k) (Ival.npow 96 (etaTaylorLowerI 96 (hi/8)) 8)

private theorem etaLogIntervalCheck_sound (k : ℕ) (lo hi : ℚ) (h : etaLogIntervalCheck k lo hi = true) :
    (expUpperQ (lo/8))^8 ≤ k ∧ (k:ℚ) ≤ (expLowerQ (hi/8))^8 := by
  simp only [etaLogIntervalCheck, Bool.and_eq_true] at h
  constructor
  · apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_pow, Rat.cast_natCast] using
      Ival.le_of_leB (Ival.mem_npow (p := 96) (etaTaylorUpperI_sound 96 _) 8) (Ival.mem_ofRat 96 (k : ℚ)) h.1
  · apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_pow, Rat.cast_natCast] using
      Ival.le_of_leB (Ival.mem_ofRat 96 (k : ℚ)) (Ival.mem_npow (p := 96) (etaTaylorLowerI_sound 96 _) 8) h.2


private def etaCoefficientEndpoint (upper : Bool) (i : ℕ) : ℚ :=
  if 0 ≤ etaC i then (if upper then etaLogHi i else etaLogLo i)
  else (if upper then etaLogLo i else etaLogHi i)

private def etaCoefficientInterval (p : ℕ) (upper : Bool) : Ival :=
  Expr.sumLoop .real 64 (fun i => Ival.mul 64 (Ival.ofRat 64 (etaC i))
    (Ival.npow 64 (Ival.ofRat 64 (etaCoefficientEndpoint upper i)) p)) 40

private theorem etaCoefficientInterval_sound (p : ℕ) (upper : Bool) :
    ((∑ i ∈ Finset.range 40, etaC i * etaCoefficientEndpoint upper i ^ p : ℚ) : ℝ) ∈ etaCoefficientInterval p upper := by
  have h := Expr.sumLoop_sound .real 64
    (fun i => Ival.mul 64 (Ival.ofRat 64 (etaC i))
      (Ival.npow 64 (Ival.ofRat 64 (etaCoefficientEndpoint upper i)) p))
    (fun i => (etaC i : ℝ) * (etaCoefficientEndpoint upper i : ℝ)^p)
    (fun i => Ival.mem_mul (Ival.mem_ofRat _ _)
      (Ival.mem_npow (Ival.mem_ofRat _ _) p)) 40
  simpa only [etaCoefficientInterval, Ty.Mem, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow] using h

private def etaCoefficientCheck (p : ℕ) : Bool :=
  let b := Ival.ofRat 64 (etaBnd p * p.factorial)
  Ival.leB (Ival.abs (etaCoefficientInterval p false)) b &&
  Ival.leB (Ival.abs (etaCoefficientInterval p true)) b

private theorem etaCoefficientCheck_sound (p : ℕ) (h : etaCoefficientCheck p = true) :
    max |etaSL p| |etaSU p| ≤ etaBnd p * p.factorial := by
  have hL : (etaSL p : ℝ) ∈ etaCoefficientInterval p false := by
    simpa only [etaSL, etaCoefficientEndpoint, Bool.false_eq_true, ite_false, ite_pow, mul_ite] using
      etaCoefficientInterval_sound p false
  have hU : (etaSU p : ℝ) ∈ etaCoefficientInterval p true := by
    simpa only [etaSU, etaCoefficientEndpoint, ite_true, ite_pow, mul_ite] using etaCoefficientInterval_sound p true
  simp only [etaCoefficientCheck, Bool.and_eq_true] at h
  apply (Rat.cast_le (K := ℝ)).mp
  simp only [Rat.cast_max, Rat.cast_abs]
  exact max_le
    (Ival.le_of_leB (Ival.mem_abs hL) (Ival.mem_ofRat _ _) h.1)
    (Ival.le_of_leB (Ival.mem_abs hU) (Ival.mem_ofRat _ _) h.2)

private def etaCoefficientMassInterval : Ival := Expr.sumLoop .real 64 (fun i => Ival.abs (Ival.ofRat 64 (etaC i))) 40

private theorem etaCoefficientMassInterval_sound : ((∑ i ∈ Finset.range 40, |etaC i| : ℚ) : ℝ) ∈ etaCoefficientMassInterval := by
  have h := Expr.sumLoop_sound .real 64 (fun i => Ival.abs (Ival.ofRat 64 (etaC i)))
    (fun i => |(etaC i : ℝ)|) (fun i => Ival.mem_abs (Ival.mem_ofRat _ _)) 40
  simpa only [etaCoefficientMassInterval, Ty.Mem, Rat.cast_sum, Rat.cast_abs] using h

private theorem etaCoefficientMassCheck_sound (h : Ival.leB etaCoefficientMassInterval (Ival.ofRat 64 4) = true) :
    ∑ i ∈ Finset.range 40, |etaC i| ≤ 4 := by
  apply (Rat.cast_le (K := ℝ)).mp
  exact Ival.le_of_leB etaCoefficientMassInterval_sound (Ival.mem_ofRat _ _) h
private def etaLogCertificateCheck (k : ℕ) (lo hi : ℚ) : Bool :=
  0 ≤ lo && lo ≤ hi && hi ≤ 4 && etaLogIntervalCheck k lo hi

private theorem etaLogCertificateCheck_sound (k : ℕ) (lo hi : ℚ) (h : etaLogCertificateCheck k lo hi = true) :
    logOK k lo hi = true := by
  simp only [etaLogCertificateCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hb := etaLogIntervalCheck_sound k lo hi h.2
  simp only [logOK, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨h.1,hb.1⟩,hb.2⟩

open scoped Lynth.Interval.AiryProof.Kernel Lynth.Interval.EtaProof.Kernel
set_option maxRecDepth 1000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 10000000

private theorem etaLogChecks_eq :
    (List.range 40).all (fun i => etaLogCertificateCheck (i+1) (etaLogLo i) (etaLogHi i)) = true := by
  eta_certificate

private theorem etaCoefficientChecks_eq :
    (List.range 42).all (fun q => etaCoefficientCheck (q+1)) = true := by
  eta_certificate

private theorem etaMassCheck_eq :
    Ival.leB etaCoefficientMassInterval (Ival.ofRat 64 4) = true := by
  eta_certificate

end EtaCertificate

private def etaCertOK : Bool :=
  (List.range 40).all (fun i => logOK (i+1) (etaLogLo i) (etaLogHi i)) &&
  (List.range 42).all (fun q => max |etaSL (q+1)| |etaSU (q+1)| ≤ etaBnd (q+1) * (q+1).factorial) &&
  decide (∑ i ∈ Finset.range 40, |etaC i| ≤ 4)

private theorem etaCertOK_eq : etaCertOK = true := by
  have hl := etaLogChecks_eq
  have hc := etaCoefficientChecks_eq
  simp only [List.all_eq_true, List.mem_range] at hl hc
  simp only [etaCertOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, etaCoefficientMassCheck_sound etaMassCheck_eq⟩
  · intro i hi
    exact etaLogCertificateCheck_sound (i+1) (etaLogLo i) (etaLogHi i) (hl i hi)
  · intro q hq
    exact etaCoefficientCheck_sound (q+1) (hc q hq)

/-! ### Consequences of the certificate -/

private theorem expUpperQ_spec {y : ℚ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : Real.exp y ≤ (expUpperQ y : ℝ) := by
  have hy0 : (0:ℝ) ≤ y := by exact_mod_cast h0
  have hy1 : (y:ℝ) ≤ 1 := by exact_mod_cast h1
  have h := Real.exp_bound (x := (y:ℝ)) (by rw [abs_of_nonneg hy0]; exact hy1) (n := 30) (by norm_num)
  rw [abs_of_nonneg hy0] at h
  have h2 := (abs_le.1 h).2
  have e : (expUpperQ y : ℝ) = ∑ i ∈ Finset.range 30, (y:ℝ)^i / (i.factorial : ℝ) +
      (y:ℝ)^30 * ((Nat.succ 30 : ℕ) / ((30).factorial * 30 : ℕ)) := by
    simp only [expUpperQ]; push_cast; ring
  rw [e]; push_cast at h2 ⊢; linarith

private theorem expLowerQ_spec {y : ℚ} (h0 : 0 ≤ y) : (expLowerQ y : ℝ) ≤ Real.exp y := by
  have hy0 : (0:ℝ) ≤ y := by exact_mod_cast h0
  have := Real.sum_le_exp_of_nonneg hy0 30
  simp only [expLowerQ]; push_cast; exact this

private theorem log_bounds_of_logOK {k : ℕ} {lo hi : ℚ} (hk : 0 < k) (h : logOK k lo hi = true) :
    (lo:ℝ) ≤ Real.log k ∧ Real.log k ≤ hi ∧ (0:ℝ) ≤ lo ∧ (hi:ℝ) ≤ 4 := by
  simp only [logOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h0, hlh⟩, h4⟩, hU⟩, hL⟩ := h
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  refine ⟨?_, ?_, by exact_mod_cast h0, by exact_mod_cast h4⟩
  · rw [Real.le_log_iff_exp_le hkR]
    have e : Real.exp lo = Real.exp ((lo/8 : ℚ) : ℝ) ^ 8 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e]
    have hb := expUpperQ_spec (y := lo/8) (by positivity) (by linarith)
    calc Real.exp ((lo/8 : ℚ) : ℝ) ^ 8 ≤ (expUpperQ (lo/8) : ℝ) ^ 8 :=
          pow_le_pow_left₀ (Real.exp_pos _).le hb 8
      _ ≤ (k:ℝ) := by exact_mod_cast hU
  · rw [Real.log_le_iff_le_exp hkR]
    have e : Real.exp hi = Real.exp ((hi/8 : ℚ) : ℝ) ^ 8 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e]
    have hb := expLowerQ_spec (y := hi/8) (by have := h0.trans hlh; positivity)
    calc (k:ℝ) ≤ (expLowerQ (hi/8) : ℝ) ^ 8 := by exact_mod_cast hL
      _ ≤ _ := by
          gcongr
          exact_mod_cast (show (0:ℚ) ≤ expLowerQ (hi/8) by
            unfold expLowerQ
            exact Finset.sum_nonneg fun i _ => by
              have := h0.trans hlh; positivity)

private theorem etaCert_parts :
    (∀ i < 40, logOK (i+1) (etaLogLo i) (etaLogHi i) = true) ∧
    (∀ q < 42, max |etaSL (q+1)| |etaSU (q+1)| ≤ etaBnd (q+1) * (q+1).factorial) ∧
    ∑ i ∈ Finset.range 40, |etaC i| ≤ 4 := by
  have h := etaCertOK_eq
  simp only [etaCertOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

private theorem etaLog_bounds (i : ℕ) (hi : i < 40) :
    (etaLogLo i : ℝ) ≤ Real.log ((i:ℝ)+1) ∧ Real.log ((i:ℝ)+1) ≤ etaLogHi i ∧
      (0:ℝ) ≤ etaLogLo i ∧ (etaLogHi i : ℝ) ≤ 4 := by
  have := log_bounds_of_logOK (Nat.succ_pos i) (etaCert_parts.1 i hi)
  push_cast at this
  exact this

/-- `S_p = ∑ c_i log(i+1)^p`, the (scaled) Taylor coefficients of the truncation at `s = 1`. -/
private noncomputable def etaS (p : ℕ) : ℝ := ∑ i ∈ Finset.range 40, (etaC i : ℝ) * Real.log ((i:ℝ)+1) ^ p

private theorem abs_etaS_le_cert (p : ℕ) : |etaS p| ≤ max |(etaSL p : ℝ)| |(etaSU p : ℝ)| := by
  apply abs_le_max_abs_abs
  · unfold etaS etaSL; push_cast
    refine Finset.sum_le_sum fun i hi => ?_
    obtain ⟨h1, h2, h3, -⟩ := etaLog_bounds i (Finset.mem_range.1 hi)
    have hp1 : (etaLogLo i : ℝ)^p ≤ Real.log ((i:ℝ)+1)^p := pow_le_pow_left₀ h3 h1 p
    have hp2 : Real.log ((i:ℝ)+1)^p ≤ (etaLogHi i : ℝ)^p := pow_le_pow_left₀ (h3.trans h1) h2 p
    split_ifs with hc
    · push_cast; exact mul_le_mul_of_nonneg_left hp1 (by exact_mod_cast hc)
    · push_cast
      exact mul_le_mul_of_nonpos_left hp2 (by exact_mod_cast (not_le.1 hc).le)
  · unfold etaS etaSU; push_cast
    refine Finset.sum_le_sum fun i hi => ?_
    obtain ⟨h1, h2, h3, -⟩ := etaLog_bounds i (Finset.mem_range.1 hi)
    have hp1 : (etaLogLo i : ℝ)^p ≤ Real.log ((i:ℝ)+1)^p := pow_le_pow_left₀ h3 h1 p
    have hp2 : Real.log ((i:ℝ)+1)^p ≤ (etaLogHi i : ℝ)^p := pow_le_pow_left₀ (h3.trans h1) h2 p
    split_ifs with hc
    · push_cast; exact mul_le_mul_of_nonneg_left hp2 (by exact_mod_cast hc)
    · push_cast
      exact mul_le_mul_of_nonpos_left hp1 (by exact_mod_cast (not_le.1 hc).le)

private theorem four_mul_sixteen_pow_le (p : ℕ) (hp : 43 ≤ p) : (4:ℝ) * 16^p ≤ p.factorial := by
  induction p, hp using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ p hp ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have : (16:ℝ) ≤ (p+1 : ℕ) := by exact_mod_cast (show 16 ≤ p + 1 by omega)
    nlinarith [Nat.cast_nonneg (α := ℝ) p.factorial]

private theorem etaS_bound (p : ℕ) (hp : 1 ≤ p) : |etaS p| / p.factorial ≤ etaBnd p := by
  have hf : (0:ℝ) < p.factorial := by exact_mod_cast p.factorial_pos
  rw [div_le_iff₀ hf]
  rcases le_or_gt p 42 with h | h
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have := etaCert_parts.2.1 q (by omega)
    refine (abs_etaS_le_cert (q+1)).trans ?_
    have h' : ((max |etaSL (q+1)| |etaSU (q+1)| : ℚ) : ℝ) ≤
        ((etaBnd (q+1) * (q+1).factorial : ℚ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    exact h'
  · have hsum := etaCert_parts.2.2
    have hsumR : ∑ i ∈ Finset.range 40, |(etaC i : ℝ)| ≤ 4 := by exact_mod_cast hsum
    have h1 : |etaS p| ≤ 4 * 4^p := by
      unfold etaS
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ Finset.range 40, |(etaC i : ℝ) * Real.log ((i:ℝ)+1) ^ p|
          ≤ ∑ i ∈ Finset.range 40, |(etaC i : ℝ)| * 4^p := by
            refine Finset.sum_le_sum fun i hi => ?_
            obtain ⟨h1, h2, h3, h4⟩ := etaLog_bounds i (Finset.mem_range.1 hi)
            rw [abs_mul, abs_pow, abs_of_nonneg (h3.trans h1)]
            gcongr <;> linarith
        _ = (∑ i ∈ Finset.range 40, |(etaC i : ℝ)|) * 4^p := by rw [Finset.sum_mul]
        _ ≤ 4 * 4^p := by gcongr
    have h2 := four_mul_sixteen_pow_le p (by omega)
    have hb : (etaBnd p : ℝ) = 1 / 4^p := by
      simp only [etaBnd, show p ≠ 1 by omega, ite_false]; push_cast; ring
    rw [hb]
    have h16 : (16:ℝ)^p = 4^p * 4^p := by rw [← mul_pow]; norm_num
    have h4p : (0:ℝ) < 4^p := by positivity
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h4p]
    nlinarith

/-! ### Power series of the truncation around `s = 1` -/

open Filter Topology

private theorem etaApproxC_one_add (z : ℂ) :
    etaApproxC (1 + z) 40 =
      ∑ i ∈ Finset.range 40, (etaC i : ℂ) * Complex.exp (-(z * (Real.log ((i:ℝ)+1) : ℂ))) := by
  unfold etaApproxC
  rw [etaWeights_eq, List.map_map, list_sum_map_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, etaEntry, etaC]
  have hpos : (0:ℝ) < (i:ℝ) + 1 := by positivity
  have hne : (((i+1 : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero i)
  rw [Complex.cpow_def_of_ne_zero hne]
  have hlog : Complex.log ((i+1 : ℕ) : ℂ) = (Real.log ((i:ℝ)+1) : ℂ) := by
    rw [Complex.ofReal_log hpos.le]; push_cast; ring_nf
  rw [hlog]
  have hexp : Complex.exp (-(Real.log ((i:ℝ)+1) : ℂ)) = (((i:ℚ) + 1)⁻¹ : ℚ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hpos]
    push_cast; ring
  rw [show (Real.log ((i:ℝ)+1) : ℂ) * -(1 + z) =
      -(Real.log ((i:ℝ)+1) : ℂ) + -(z * (Real.log ((i:ℝ)+1) : ℂ)) by ring,
    Complex.exp_add, hexp]
  push_cast
  split_ifs <;> ring

private theorem hasSum_etaApproxC_one_add (z : ℂ) :
    HasSum (fun p => (-z)^p / (p.factorial : ℂ) * (etaS p : ℂ)) (etaApproxC (1 + z) 40) := by
  rw [etaApproxC_one_add]
  have h : ∀ i ∈ Finset.range 40, HasSum (fun p => (etaC i : ℂ) *
      ((-(z * (Real.log ((i:ℝ)+1) : ℂ)))^p / (p.factorial : ℂ)))
      ((etaC i : ℂ) * Complex.exp (-(z * (Real.log ((i:ℝ)+1) : ℂ)))) := by
    intro i _
    have := NormedSpace.expSeries_div_hasSum_exp (-(z * (Real.log ((i:ℝ)+1) : ℂ)))
    rw [← Complex.exp_eq_exp_ℂ] at this
    exact this.mul_left _
  convert hasSum_sum h using 1
  funext p
  unfold etaS
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_mul_eq_neg_mul, mul_pow]
  ring

private theorem etaApproxC_one : etaApproxC 1 40 = (etaS 0 : ℂ) := by
  have := etaApproxC_one_add 0
  rw [add_zero] at this
  rw [this]
  unfold etaS
  push_cast
  simp

private theorem norm_etaApproxC_sub_le (z : ℂ) (hz : ‖z‖ < 4) :
    ‖etaApproxC (1 + z) 40 - etaApproxC 1 40‖ ≤
      249/1000 * ‖z‖ + (‖z‖/4)^2 * (1 - ‖z‖/4)⁻¹ := by
  set T : ℕ → ℂ := fun p => (-z)^p / (p.factorial : ℂ) * (etaS p : ℂ) with hT
  have h := hasSum_etaApproxC_one_add z
  have h2 := (hasSum_nat_add_iff' 2).2 h
  have hsplit : etaApproxC (1 + z) 40 - etaApproxC 1 40 =
      T 1 + ∑' p, T (p + 2) := by
    rw [h2.tsum_eq, etaApproxC_one]
    simp [Finset.sum_range_succ, hT]
    ring
  have hnormT : ∀ p, ‖T p‖ = ‖z‖^p * (|etaS p| / p.factorial) := by
    intro p
    simp only [hT, norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs]
    ring
  have hr4 : ‖z‖/4 < 1 := by linarith
  have hr0 : 0 ≤ ‖z‖/4 := by positivity
  have hb : ∀ p, ‖T (p + 2)‖ ≤ (‖z‖/4)^2 * (‖z‖/4)^p := by
    intro p
    rw [hnormT]
    have := etaS_bound (p+2) (by omega)
    simp only [etaBnd, show p + 2 ≠ 1 by omega, ite_false] at this
    push_cast at this
    calc ‖z‖^(p+2) * (|etaS (p+2)| / ((p+2).factorial : ℝ)) ≤ ‖z‖^(p+2) * (1/4^(p+2)) := by
          gcongr
      _ = _ := by rw [div_pow, div_pow]; field_simp; ring
  have hgeom := (hasSum_geometric_of_lt_one hr0 hr4).mul_left ((‖z‖/4)^2)
  have htail := tsum_of_norm_bounded hgeom hb
  have h1 : ‖T 1‖ ≤ 249/1000 * ‖z‖ := by
    rw [hnormT]
    have := etaS_bound 1 le_rfl
    simp only [etaBnd, ite_true] at this
    push_cast at this
    rw [pow_one, mul_comm]
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add h1 htail)

/-! ### The truncation error on the disc, and the final bound -/

private theorem norm_eta_sub_approx_le (s : ℂ) (hs : ‖s - 1‖ < 4) :
    ‖Complex.dirichletEta s - etaApproxC s 40‖ ≤ 1/500 := by
  have hsq : (s.re - 1)^2 + s.im^2 < 16 := by
    have h1 : ‖s - 1‖^2 < 16 := by
      have := norm_nonneg (s - 1); nlinarith
    rw [Complex.sq_norm, Complex.normSq_apply] at h1
    simp at h1; nlinarith
  have hx : 2 < s.re + 5 := by nlinarith [sq_nonneg s.im]
  have h := eta_euler_error_aux s 5 40 (by push_cast; linarith) (by norm_num)
  push_cast at h
  set x := s.re + 5 with hxdef
  have hphi : s.im^2/2 * (x⁻¹^2 + x⁻¹) ≤ 2 := by
    have hxpos : 0 < x := by linarith
    have hτ : s.im^2 ≤ 16 - (x - 6)^2 := by rw [hxdef]; nlinarith
    rw [show x⁻¹^2 + x⁻¹ = (1 + x) / x^2 by field_simp]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    have : s.im^2 * (1 + x) ≤ (16 - (x - 6)^2) * (1 + x) :=
      mul_le_mul_of_nonneg_right hτ (by linarith)
    nlinarith [mul_nonneg (sq_nonneg (x - 4)) (show (0:ℝ) ≤ x + 1 by linarith)]
  have he2 : Real.exp 2 ≤ 739/100 := by
    have h1 := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  have hE : Real.exp (s.im^2/2 * (x⁻¹^2 + x⁻¹)) ≤ 739/100 :=
    (Real.exp_le_exp.2 hphi).trans he2
  refine h.trans ?_
  have : 2 * Real.exp (s.im^2/2 * (x⁻¹^2 + x⁻¹)) * (40 + 1 : ℝ)^5 / 2^40 ≤
      2 * (739/100) * (40 + 1 : ℝ)^5 / 2^40 := by gcongr
  refine this.trans ?_
  norm_num

private theorem differentiable_etaApproxC (n : ℕ) : Differentiable ℂ (fun s => etaApproxC s n) := by
  have : (fun s => etaApproxC s n) =
      fun s => ∑ j ∈ Finset.range n, (1/2:ℂ)^(j+1) * etaDelta j s := by
    funext s; exact etaApproxC_eq_sum s n
  rw [this]
  exact Differentiable.fun_sum fun j _ => (differentiable_etaDelta j).const_mul _

private theorem eta_near_one_aux (s : ℂ) (hs : ‖s-1‖ < 4) :
    ‖Complex.dirichletEta s - (Real.log 2 : ℂ)‖ ≤ ‖s-1‖/(4-‖s-1‖) := by
  set h : ℂ → ℂ := fun w => Complex.dirichletEta w - etaApproxC w 40 with hh
  have hdiff : DifferentiableOn ℂ h (Metric.ball 1 4) := by
    refine (DifferentiableOn.sub ?_ (differentiable_etaApproxC 40).differentiableOn)
    exact fun w _ => (analyticAt_dirichletEta w).differentiableAt.differentiableWithinAt
  have hball : ∀ w ∈ Metric.ball (1:ℂ) 4, ‖h w‖ ≤ 1/500 := by
    intro w hw
    have : ‖w - 1‖ < 4 := by simpa [dist_eq_norm] using hw
    exact norm_eta_sub_approx_le w this
  have h1mem : (1:ℂ) ∈ Metric.ball (1:ℂ) 4 := Metric.mem_ball_self (by norm_num)
  have hmaps : Set.MapsTo h (Metric.ball 1 4) (Metric.closedBall (h 1) (2/500)) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖h w - h 1‖ ≤ ‖h w‖ + ‖h 1‖ := norm_sub_le _ _
      _ ≤ 1/500 + 1/500 := add_le_add (hball w hw) (hball 1 h1mem)
      _ = 2/500 := by norm_num
  have hsmem : s ∈ Metric.ball (1:ℂ) 4 := by simpa [dist_eq_norm] using hs
  have hschwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmaps hsmem
  rw [dist_eq_norm, dist_eq_norm] at hschwarz
  have happrox := norm_etaApproxC_sub_le (s - 1) hs
  rw [show 1 + (s - 1) = s by ring] at happrox
  have heta1 : Complex.dirichletEta 1 = (Real.log 2 : ℂ) := by simp [Complex.dirichletEta]
  have hsplit : Complex.dirichletEta s - (Real.log 2 : ℂ) =
      (etaApproxC s 40 - etaApproxC 1 40) + (h s - h 1) := by
    simp only [hh, heta1]; ring
  rw [hsplit]
  set r := ‖s - 1‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have h4r : 0 < 4 - r := by linarith
  calc ‖(etaApproxC s 40 - etaApproxC 1 40) + (h s - h 1)‖
      ≤ ‖etaApproxC s 40 - etaApproxC 1 40‖ + ‖h s - h 1‖ := norm_add_le _ _
    _ ≤ (249/1000 * r + (r/4)^2 * (1 - r/4)⁻¹) + (2/500)/4 * r := add_le_add happrox hschwarz
    _ ≤ r / (4 - r) := by
        have e : (r/4)^2 * (1 - r/4)⁻¹ = r^2 / (4 * (4 - r)) := by
          field_simp
        have e2 : r / (4 - r) = r/4 + r^2 / (4 * (4 - r)) := by
          field_simp; ring
        rw [e, e2]
        linarith

end SpecialFunctions


end

namespace SpecialFunctions

/-- Integrate by parts m times in the finite-difference Laplace integral.
The mth derivative of e^-t (1-e^-t)^n has modulus at most (n+1)^m e^-t.
For n >= 4m, the weighted polynomial tail is at most twice its first term.
The complex Gamma ratio is bounded using its Weierstrass product. -/

theorem eta_euler_error (s : ℂ) (m n : ℕ) (hm : 0 < s.re + m) (hn : 4*m ≤ n) :
    ‖Complex.dirichletEta s - etaApproxC s n‖ ≤
      2 * Real.exp (s.im^2/2 * ((s.re+m)⁻¹^2 + (s.re+m)⁻¹)) *
        (n+1 : ℝ)^m / 2^n :=
  eta_euler_error_aux s m n hm hn

theorem norm_etaApproxC_le (s : ℂ) (m n : ℕ) (hm : 0 < s.re + m) :
    ‖etaApproxC s n‖ ≤ (n : ℝ) * (n + 1 : ℝ)^m := by
  unfold etaApproxC
  rw [etaWeights_eq, List.map_map, list_sum_map_range]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k ∈ Finset.range n, ‖((fun (x : ℕ × ℚ) => (x.2 : ℂ) * (x.1 : ℂ) ^ (-s)) ∘ etaEntry n) k‖
      ≤ (n + 1 : ℝ)^m := by
    intro k hk
    rw [Finset.mem_range] at hk
    simp only [Function.comp_apply, etaEntry]
    generalize hw0 : (((2^n - ∑ i ∈ Finset.range (k+1), n.choose i : ℕ) : ℚ) / (2^n : ℚ)) = w
    have h1 : w ≤ 1 := by
      rw [← hw0, div_le_one (by positivity)]
      have : (2^n - ∑ i ∈ Finset.range (k+1), n.choose i : ℕ) ≤ 2^n := Nat.sub_le _ _
      exact_mod_cast this
    have h0 : 0 ≤ w := by rw [← hw0]; positivity
    have hw : ‖(((if k % 2 = 0 then w else -w) : ℚ) : ℂ)‖ ≤ 1 := by
      rw [norm_ratCast_eq, ← Rat.cast_abs]
      have : |(if k % 2 = 0 then w else -w)| ≤ 1 := by
        split_ifs
        · rw [abs_of_nonneg h0]; exact h1
        · rw [abs_neg, abs_of_nonneg h0]; exact h1
      exact_mod_cast this
    rw [norm_mul]
    have hc : ‖(((k + 1 : ℕ) : ℂ)) ^ (-s)‖ ≤ (n + 1 : ℝ)^m := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      simp only [Complex.neg_re]
      calc ((k + 1 : ℕ) : ℝ) ^ (-s.re) ≤ ((k + 1 : ℕ) : ℝ) ^ (m : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_cast; omega) (by linarith)
        _ = ((k + 1 : ℕ) : ℝ) ^ m := Real.rpow_natCast _ _
        _ ≤ (n + 1 : ℝ)^m := by
            gcongr; push_cast; exact_mod_cast (by omega : k + 1 ≤ n + 1)
    calc _ ≤ 1 * (n + 1 : ℝ)^m := mul_le_mul hw hc (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  refine (Finset.sum_le_sum this).trans ?_
  simp

private theorem etaApproxC_ofReal (s : ℝ) (n : ℕ) : etaApproxC (s : ℂ) n = (etaApproxR s n : ℂ) := by
  unfold etaApproxC etaApproxR
  induction etaWeights n with
  | nil => simp
  | cons kw L ih =>
    obtain ⟨k, w⟩ := kw
    simp only [List.map_cons, List.sum_cons, ih]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast; rfl


theorem eta_euler_error_real (s : ℝ) (m n : ℕ) (hm : 0 < s + m) (hn : 4*m ≤ n) :
    |Real.dirichletEta s - etaApproxR s n| ≤ 2 * (n+1 : ℝ)^m / 2^n := by
  have h := eta_euler_error (s : ℂ) m n (by simpa using hm) hn
  rw [dirichletEta_ofReal, etaApproxC_ofReal, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at h
  simpa using h

/-- FLINT's coefficient bound at the removable singularity s=1. -/

theorem eta_near_one (s : ℂ) (hs : ‖s-1‖ < 4) :
    ‖Complex.dirichletEta s - (Real.log 2 : ℂ)‖ ≤ ‖s-1‖/(4-‖s-1‖) :=
  eta_near_one_aux s hs

end SpecialFunctions
