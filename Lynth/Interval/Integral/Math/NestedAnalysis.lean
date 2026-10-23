module

import all Lynth.Interval.Integral.Math.NestedDefs
import all Lynth.Interval.Integral.Math.IntgrlDefs

/-! Portable proof obligations for recursive real quadrature. No interval
representation, search state or tactic code occurs in these statements.
The placeholders are deliberately isolated for independent Mathlib proofs. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Intgrl

theorem parametric_finite_analytic {F : ℂ → ℂ → ℂ} {z : ℂ}
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AnalyticAt ℂ (fun p : ℂ × ℂ => F p.1 p.2) (z,(t : ℂ))) :
    AnalyticAt ℂ (fun w => ∫ t in (0 : ℝ)..1, F w t) z := by
  set G : ℂ × ℂ → ℂ := fun p => F p.1 p.2 with hGdef
  set A := {p : ℂ × ℂ | AnalyticAt ℂ G p}
  have hA : IsOpen A := isOpen_analyticAt ℂ G
  set K := (fun t : ℝ => (z, (t : ℂ))) '' Set.Icc (0:ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hKA : K ⊆ A := by rintro _ ⟨t, ht, rfl⟩; exact hF t ht
  obtain ⟨δ, hδ, hδA⟩ := hK.exists_cthickening_subset_open hA hKA
  have hmem : ∀ w ∈ Metric.closedBall z δ, ∀ t ∈ Set.Icc (0:ℝ) 1,
      AnalyticAt ℂ G (w, (t:ℂ)) := by
    intro w hw t ht
    apply hδA
    apply Metric.mem_cthickening_of_dist_le (w, (t:ℂ)) (z, (t:ℂ)) δ K ⟨t, ht, rfl⟩
    rw [Prod.dist_eq]
    simpa [max_eq_left dist_nonneg] using hw
  set D : ℂ → ℝ → ℂ := fun w t => fderiv ℂ G (w, (t:ℂ)) (1, 0)
  have hderiv : ∀ w ∈ Metric.closedBall z δ, ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt (fun w => F w t) (D w t) w := by
    intro w hw t ht
    have h1 := (hmem w hw t ht).differentiableAt.hasFDerivAt
    have h2 : HasDerivAt (fun w : ℂ => (w, (t:ℂ))) (1, 0) w :=
      (hasDerivAt_id w).prodMk (hasDerivAt_const w _)
    exact h1.comp_hasDerivAt w h2
  have hDcont : ContinuousOn (fun p : ℂ × ℝ => D p.1 p.2)
      (Metric.closedBall z δ ×ˢ Set.Icc 0 1) := by
    have hAn : AnalyticOnNhd ℂ G A := fun p hp => hp
    have hfd : ContinuousOn (fderiv ℂ G) A := (hAn.fderiv).continuousOn
    have : ContinuousOn (fun p : ℂ × ℝ => fderiv ℂ G (p.1, (p.2:ℂ)))
        (Metric.closedBall z δ ×ˢ Set.Icc 0 1) := by
      refine hfd.comp (by fun_prop) ?_
      rintro ⟨w, t⟩ ⟨hw, ht⟩; exact hmem w hw t ht
    exact this.clm_apply continuousOn_const
  obtain ⟨C, hC⟩ := (isCompact_closedBall z δ |>.prod isCompact_Icc).exists_bound_of_continuousOn
    hDcont
  have hFcont : ∀ w ∈ Metric.closedBall z δ,
      ContinuousOn (fun t : ℝ => F w t) (Set.Icc 0 1) := by
    intro w hw t ht
    have := (hmem w hw t ht).continuousAt.comp (x := (t:ℝ)) (g := G)
      (f := fun t : ℝ => (w, (t:ℂ))) (by fun_prop)
    exact this.continuousWithinAt
  have hsub : Set.uIoc (0:ℝ) 1 ⊆ Set.Icc 0 1 := by
    rw [Set.uIoc_of_le zero_le_one]; exact Set.Ioc_subset_Icc_self
  have hdiff : DifferentiableOn ℂ (fun w => ∫ t in (0 : ℝ)..1, F w t)
      (Metric.ball z (δ/2)) := by
    intro w0 hw0
    have hball : ∀ x ∈ Metric.ball w0 (δ/2), x ∈ Metric.closedBall z δ := by
      intro x hx
      rw [Metric.mem_ball] at hx hw0; rw [Metric.mem_closedBall]
      linarith [dist_triangle x w0 z]
    have hw0' : w0 ∈ Metric.closedBall z δ := hball w0 (Metric.mem_ball_self (by linarith))
    have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := 0) (b := 1) (F := fun w (t:ℝ) => F w t) (F' := D) (x₀ := w0)
      (bound := fun _ => C)
      (s := Metric.ball w0 (δ/2)) (Metric.ball_mem_nhds w0 (by linarith)) ?_ ?_ ?_ ?_ ?_ ?_
    · exact this.2.differentiableAt.differentiableWithinAt
    · filter_upwards [Metric.ball_mem_nhds w0 (by linarith : (0:ℝ) < δ/2)] with x hx
      exact ((hFcont x (hball x hx)).mono hsub).aestronglyMeasurable measurableSet_uIoc
    · exact (hFcont w0 hw0').intervalIntegrable_of_Icc zero_le_one
    · have : ContinuousOn (fun t : ℝ => D w0 t) (Set.Icc 0 1) :=
        hDcont.comp (f := fun t : ℝ => (w0, t)) (by fun_prop) (fun t ht => ⟨hw0', ht⟩)
      exact (this.mono hsub).aestronglyMeasurable measurableSet_uIoc
    · refine Eventually.of_forall fun t ht x hx => ?_
      exact hC (x, t) ⟨hball x hx, hsub ht⟩
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun t ht x hx => ?_
      exact hderiv x (hball x hx) t (hsub ht)
  exact hdiff.analyticAt (Metric.ball_mem_nhds z (by linarith))

/-- Applied to truncated improper integrals whose endpoint majorants are
uniform on a complex parameter neighborhood. Pointwise convergence alone
is deliberately insufficient. -/

theorem parametric_finite_norm {F : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hi : IntervalIntegrable F volume 0 1)
    (hb : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ‖F t‖ ≤ M) :
    ‖∫ t in (0 : ℝ)..1, F t‖ ≤ M := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have hgM : IntervalIntegrable (fun _ : ℝ => M) volume (0:ℝ) 1 := intervalIntegrable_const
  have hmono : (∫ t in (0:ℝ)..1, ‖F t‖) ≤ ∫ t in (0:ℝ)..1, M := by
    exact intervalIntegral.integral_mono_on_of_le_Ioo h01 hi.norm hgM hb
  have hval : ∫ t in (0:ℝ)..1, M = M := by
    rw [intervalIntegral.integral_const M]
    simp
  exact le_trans (intervalIntegral.norm_integral_le_integral_norm h01)
    (le_trans hmono (le_of_eq hval))

/-- Applied to truncated improper integrals whose endpoint majorants are
uniform on a complex parameter neighborhood. Pointwise convergence alone
is deliberately insufficient. -/
theorem parametric_improper_analytic {U : Set ℂ} (hU : IsOpen U)
    {F : ℂ → ℂ} {G : ℕ → ℂ → ℂ}
    (hG : ∀ n, AnalyticOnNhd ℂ (G n) U)
    (hlim : TendstoLocallyUniformlyOn G F atTop U) : AnalyticOnNhd ℂ F U := by
  rw [Complex.analyticOnNhd_iff_differentiableOn hU]
  exact hlim.differentiableOn (Eventually.of_forall fun n => (hG n).differentiableOn) hU

set_option maxHeartbeats 1000000 in
theorem right_substitution {f : ℝ → ℝ} {a : ℝ} (hm : Measurable f) :
    IntegrableOn f (Set.Ioi a) ↔
      IntervalIntegrable (fun t => f (a+t/(1-t))/(1-t)^2) volume 0 1 := open Set in by
    let σ : ℕ → ℝ := fun i => 1 - 1 / ((i + 2 : ℕ) : ℝ)
    have σ_lt_one : ∀ (i : ℕ), σ i < 1 := by
      intro i
      have hpos : (0:ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      have h : (0:ℝ) < 1 / ((i + 2 : ℕ) : ℝ) := div_pos (by norm_num) hpos
      simp only [σ]
      linarith
    have σ_nonneg : ∀ (i : ℕ), 0 ≤ σ i := by
      intro i
      have h : (1:ℝ) ≤ ((i + 2 : ℕ) : ℝ) := by norm_cast; omega
      have h2 : (0:ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      have h3 : 1 / ((i + 2 : ℕ) : ℝ) ≤ 1 := (div_le_one h2).mpr h
      simp only [σ]
      linarith
    have σ_monotone : Monotone σ := by
      intro i j hij
      have h1 : ((i + 2 : ℕ) : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hij 2
      have h2 : (0:ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      have h3 : (0:ℝ) < ((j + 2 : ℕ) : ℝ) := by positivity
      have h4 : 1 / ((j + 2 : ℕ) : ℝ) ≤ 1 / ((i + 2 : ℕ) : ℝ) := by
        rw [one_div, one_div]
        exact (inv_le_inv₀ h3 h2).mpr h1
      simp only [σ]
      linarith
    have σ_frac : ∀ (i : ℕ), σ i / (1 - σ i) = ((i + 1 : ℕ) : ℝ) := by
      intro i
      have hne : ((i + 2 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero (i + 1))
      simp only [σ]
      field_simp [hne]
      push_cast
      ring
    have σ_tendsto : Tendsto σ atTop (𝓝 1) := by
      have h0 : Tendsto (fun i : ℕ => ((i + 2 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
      have hsub : Tendsto (fun i : ℕ => (1:ℝ) - ((i + 2 : ℕ) : ℝ)⁻¹) atTop (𝓝 ((1:ℝ) - 0)) :=
        tendsto_const_nhds.sub h0
      rw [sub_zero] at hsub
      have hσ : ∀ i, σ i = (1:ℝ) - ((i + 2 : ℕ) : ℝ)⁻¹ := by
        intro i
        simp only [σ, one_div]
      exact Tendsto.congr (fun i => (hσ i).symm) hsub
    have tendsto_add_nat_atTop : ∀ (a : ℝ), Tendsto (fun i : ℕ => a + ((i + 1 : ℕ) : ℝ)) atTop atTop := by
      intro a
      rw [tendsto_atTop_atTop]
      intro b
      obtain ⟨m, hm⟩ := exists_nat_ge (b - a)
      refine ⟨m, fun a' ha' => ?_⟩
      have hle : ((m : ℕ) : ℝ) ≤ ((a' : ℕ) : ℝ) := by exact_mod_cast ha'
      have hcast1 : ((a' + 1 : ℕ) : ℝ) = ((a' : ℕ) : ℝ) + 1 := by norm_cast
      have hcast2 : ((m + 1 : ℕ) : ℝ) = ((m : ℕ) : ℝ) + 1 := by norm_cast
      linarith [hm]
    have tendsto_sub_nat_atBot : ∀ (a : ℝ), Tendsto (fun i : ℕ => a - ((i + 1 : ℕ) : ℝ)) atTop atBot := by
      intro a
      rw [tendsto_atTop_atBot]
      intro b
      obtain ⟨m, hm⟩ := exists_nat_ge (a - b)
      refine ⟨m, fun a' ha' => ?_⟩
      have hle : ((m : ℕ) : ℝ) ≤ ((a' : ℕ) : ℝ) := by exact_mod_cast ha'
      have hcast1 : ((a' + 1 : ℕ) : ℝ) = ((a' : ℕ) : ℝ) + 1 := by norm_cast
      have hcast2 : ((m + 1 : ℕ) : ℝ) = ((m : ℕ) : ℝ) + 1 := by norm_cast
      linarith [hm]
    have smul_eq_div : ∀ (z X : ℝ), (1 / X) • z = z / X := by
      intro z X
      rw [show ∀ r z : ℝ, r • z = r * z from fun _ _ => rfl, div_eq_mul_inv, div_eq_mul_inv,
        one_mul, mul_comm]
    have neg_smul_key : ∀ (z X : ℝ), z / X = -((-1 / X) • z) := by
      intro z X
      rw [show ∀ r z : ℝ, r • z = r * z from fun _ _ => rfl, neg_div, neg_mul, neg_neg,
        div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
    have norm_eq_div : ∀ {z X : ℝ} (hX : 0 < X), ‖z / X‖ = ‖z‖ / X := by
      intro z X
      intro hX
      rw [norm_div]
      simp only [Real.norm_eq_abs, abs_of_pos hX]
    have hasDerivAt_phi : ∀ (a t : ℝ) (ht : t < 1), HasDerivAt (fun u : ℝ => a + u / (1 - u)) (1 / (1 - t) ^ 2) t := by
      intro a t
      intro ht
      have hne : 1 - t ≠ 0 := by linarith
      have hden : HasDerivAt (fun u : ℝ => 1 - u) (0 - 1) t :=
        (hasDerivAt_const t 1).sub (hasDerivAt_id t)
      have hq : HasDerivAt (fun u : ℝ => u / (1 - u)) (1 / (1 - t) ^ 2) t := by
        have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
        have h := hid.fun_div hden hne
        rw [show (1 * (1 - t) - t * (0 - 1)) = 1 by ring] at h
        exact h
      exact hq.const_add a
    have hasDerivAt_psi : ∀ (a t : ℝ) (ht : t < 1), HasDerivAt (fun u : ℝ => a - u / (1 - u)) (-1 / (1 - t) ^ 2) t := by
      intro a t
      intro ht
      have hne : 1 - t ≠ 0 := by linarith
      have hden : HasDerivAt (fun u : ℝ => 1 - u) (0 - 1) t :=
        (hasDerivAt_const t 1).sub (hasDerivAt_id t)
      have hq : HasDerivAt (fun u : ℝ => u / (1 - u)) (1 / (1 - t) ^ 2) t := by
        have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
        have h := hid.fun_div hden hne
        rw [show (1 * (1 - t) - t * (0 - 1)) = 1 by ring] at h
        exact h
      have h := hq.const_sub a
      rw [← neg_div] at h
      exact h
    have continuousOn_phi : ∀ (a T : ℝ) (hT1 : T < 1), ContinuousOn (fun u : ℝ => a + u / (1 - u)) (Set.Icc 0 T) := by
      intro a T
      intro hT1
      refine continuousOn_of_forall_continuousAt fun x hx => ?_
      exact (hasDerivAt_phi a x (by linarith [hx.2, hT1])).continuousAt
    have continuousOn_psi : ∀ (a T : ℝ) (hT1 : T < 1), ContinuousOn (fun u : ℝ => a - u / (1 - u)) (Set.Icc 0 T) := by
      intro a T
      intro hT1
      refine continuousOn_of_forall_continuousAt fun x hx => ?_
      exact (hasDerivAt_psi a x (by linarith [hx.2, hT1])).continuousAt
    have nonneg_inv_sq : ∀ {t : ℝ} (ht : t < 1), 0 ≤ 1 / (1 - t) ^ 2 := by
      intro t
      intro ht
      have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith)
      exact div_nonneg (by norm_num) hpos.le
    have nonpos_neg_inv_sq : ∀ {t : ℝ} (ht : t < 1), -1 / (1 - t) ^ 2 ≤ 0 := by
      intro t
      intro ht
      have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith)
      exact div_nonpos_iff.mpr (Or.inr ⟨by norm_num, hpos.le⟩)
    have rkey : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, f (a + t / (1 - t)) / (1 - t) ^ 2
      = ∫ x in Set.Icc a (a + T / (1 - T)), f x := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          f (a + t / (1 - t)) / (1 - t) ^ 2 = (1 / (1 - t) ^ 2) • f (a + t / (1 - t)) :=
        fun t _ => (smul_eq_div (f (a + t / (1 - t))) ((1 - t) ^ 2)).symm
      have hL : ∫ t in Set.Icc 0 T, f (a + t / (1 - t)) / (1 - t) ^ 2
          = ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • f (a + t / (1 - t)) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • f (a + t / (1 - t))
          = ∫ x in Set.Icc (a + 0 / (1 - 0)) (a + T / (1 - T)), f x :=
        integral_Icc_deriv_smul_of_deriv_nonneg (f := fun u : ℝ => a + u / (1 - u))
          (f' := fun t : ℝ => 1 / (1 - t) ^ 2) (g := f)
          (continuousOn_phi a T hT1) (fun x hx => hasDerivAt_phi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonneg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, add_zero] at hR
      exact hL.trans hR
    have rkey_norm : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖
      = ∫ x in Set.Icc a (a + T / (1 - T)), ‖f x‖ := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖ = (1 / (1 - t) ^ 2) • ‖f (a + t / (1 - t))‖ := by
        intro t ht
        have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith [ht.2, hT1])
        rw [norm_eq_div hpos]
        exact (smul_eq_div _ _).symm
      have hL : ∫ t in Set.Icc 0 T, ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖
          = ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • ‖f (a + t / (1 - t))‖ :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • ‖f (a + t / (1 - t))‖
          = ∫ x in Set.Icc (a + 0 / (1 - 0)) (a + T / (1 - T)), ‖f x‖ :=
        integral_Icc_deriv_smul_of_deriv_nonneg (f := fun u : ℝ => a + u / (1 - u))
          (f' := fun t : ℝ => 1 / (1 - t) ^ 2) (g := fun x => ‖f x‖)
          (continuousOn_phi a T hT1) (fun x hx => hasDerivAt_phi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonneg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, add_zero] at hR
      exact hL.trans hR
    have rkey_integrable : ∀ {f : ℝ → ℝ} {a : ℝ} {i : ℕ}, IntegrableOn f (Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)))
      ↔ IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) := by
      intro f
      intro a
      intro i
      have hsig : σ i / (1 - σ i) = ((i + 1 : ℕ) : ℝ) := σ_frac i
      have hT1 : σ i < 1 := σ_lt_one i
      have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
      have hiff :
          IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a + t / (1 - t))) (Set.Icc 0 (σ i))
            ↔ IntegrableOn f (Set.Icc a (a + ((i + 1 : ℕ) : ℝ))) := by
        have h0 := integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg
          (f := fun u : ℝ => a + u / (1 - u)) (f' := fun t : ℝ => 1 / (1 - t) ^ 2) (g := f)
          (continuousOn_phi a (σ i) hT1) (fun x hx => hasDerivAt_phi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonneg_inv_sq (by linarith [hx.2, hT1])) hT0
        simpa only [zero_div, add_zero, hsig] using h0
      have h1 : IntegrableOn f (Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)))
          ↔ IntegrableOn f (Set.Icc a (a + ((i + 1 : ℕ) : ℝ))) :=
        (integrableOn_Icc_iff_integrableOn_Ioc (f := f) (a := a)
          (b := a + ((i + 1 : ℕ) : ℝ))).symm
      have h2 : IntegrableOn f (Set.Icc a (a + ((i + 1 : ℕ) : ℝ)))
          ↔ IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a + t / (1 - t))) (Set.Icc 0 (σ i)) :=
        hiff.symm
      have h3 : IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a + t / (1 - t)))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i)) :=
        integrableOn_congr_fun
          (fun t _ => smul_eq_div (f (a + t / (1 - t))) ((1 - t) ^ 2)) measurableSet_Icc
      have h4 : IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) :=
        integrableOn_Icc_iff_integrableOn_Ioc
      exact h1.trans h2 |>.trans h3 |>.trans h4
    have lkey : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, f (a - t / (1 - t)) / (1 - t) ^ 2
      = ∫ x in Set.Icc (a - T / (1 - T)) a, f x := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          f (a - t / (1 - t)) / (1 - t) ^ 2 = -((-1 / (1 - t) ^ 2) • f (a - t / (1 - t))) :=
        fun t _ => neg_smul_key (f (a - t / (1 - t))) ((1 - t) ^ 2)
      have hL : ∫ t in Set.Icc 0 T, f (a - t / (1 - t)) / (1 - t) ^ 2
          = ∫ t in Set.Icc 0 T, -((-1 / (1 - t) ^ 2) • f (a - t / (1 - t))) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (-1 / (1 - t) ^ 2) • f (a - t / (1 - t))
          = -∫ x in Set.Icc (a - T / (1 - T)) (a - 0 / (1 - 0)), f x :=
        integral_Icc_deriv_smul_of_deriv_nonpos (f := fun u : ℝ => a - u / (1 - u))
          (f' := fun t : ℝ => -1 / (1 - t) ^ 2) (g := f)
          (continuousOn_psi a T hT1) (fun x hx => hasDerivAt_psi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonpos_neg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, sub_zero] at hR
      rw [hL, MeasureTheory.integral_neg, hR, neg_neg]
    have lkey_norm : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, ‖f (a - t / (1 - t)) / (1 - t) ^ 2‖
      = ∫ x in Set.Icc (a - T / (1 - T)) a, ‖f x‖ := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          ‖f (a - t / (1 - t)) / (1 - t) ^ 2‖
            = -((-1 / (1 - t) ^ 2) • ‖f (a - t / (1 - t))‖) := by
        intro t ht
        have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith [ht.2, hT1])
        rw [norm_eq_div hpos]
        exact neg_smul_key _ _
      have hL : ∫ t in Set.Icc 0 T, ‖f (a - t / (1 - t)) / (1 - t) ^ 2‖
          = ∫ t in Set.Icc 0 T, -((-1 / (1 - t) ^ 2) • ‖f (a - t / (1 - t))‖) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (-1 / (1 - t) ^ 2) • ‖f (a - t / (1 - t))‖
          = -∫ x in Set.Icc (a - T / (1 - T)) (a - 0 / (1 - 0)), ‖f x‖ :=
        integral_Icc_deriv_smul_of_deriv_nonpos (f := fun u : ℝ => a - u / (1 - u))
          (f' := fun t : ℝ => -1 / (1 - t) ^ 2) (g := fun x => ‖f x‖)
          (continuousOn_psi a T hT1) (fun x hx => hasDerivAt_psi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonpos_neg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, sub_zero] at hR
      rw [hL, MeasureTheory.integral_neg, hR, neg_neg]
    have lkey_integrable : ∀ {f : ℝ → ℝ} {a : ℝ} {i : ℕ}, IntegrableOn f (Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a)
      ↔ IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) := by
      intro f
      intro a
      intro i
      have hsig : σ i / (1 - σ i) = ((i + 1 : ℕ) : ℝ) := σ_frac i
      have hT1 : σ i < 1 := σ_lt_one i
      have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
      have hiff :
          IntegrableOn (fun t : ℝ => (-1 / (1 - t) ^ 2) • f (a - t / (1 - t))) (Set.Icc 0 (σ i))
            ↔ IntegrableOn f (Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a) := by
        have h0 := integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos
          (f := fun u : ℝ => a - u / (1 - u)) (f' := fun t : ℝ => -1 / (1 - t) ^ 2) (g := f)
          (continuousOn_psi a (σ i) hT1) (fun x hx => hasDerivAt_psi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonpos_neg_inv_sq (by linarith [hx.2, hT1])) hT0
        simpa only [zero_div, sub_zero, hsig] using h0
      have h1 : IntegrableOn f (Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a)
          ↔ IntegrableOn f (Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a) :=
        (integrableOn_Icc_iff_integrableOn_Ioc (f := f)
          (a := a - ((i + 1 : ℕ) : ℝ)) (b := a)).symm
      have h2 : IntegrableOn f (Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a)
          ↔ IntegrableOn (fun t : ℝ => (-1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
              (Set.Icc 0 (σ i)) :=
        hiff.symm
      have h3 : IntegrableOn (fun t : ℝ => (-1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => -((1 / (1 - t) ^ 2) • f (a - t / (1 - t))))
              (Set.Icc 0 (σ i)) :=
        integrableOn_congr_fun (fun t _ => by rw [neg_div, neg_smul]) measurableSet_Icc
      have h3b : IntegrableOn (fun t : ℝ => -((1 / (1 - t) ^ 2) • f (a - t / (1 - t))))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
              (Set.Icc 0 (σ i)) :=
        integrableOn_neg_iff
      have h3c : IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i)) :=
        integrableOn_congr_fun
          (fun t _ => smul_eq_div (f (a - t / (1 - t))) ((1 - t) ^ 2)) measurableSet_Icc
      have h4 : IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) :=
        integrableOn_Icc_iff_integrableOn_Ioc
      exact h1.trans h2 |>.trans h3 |>.trans h3b |>.trans h3c |>.trans h4
    have tendsto_sigma_integral : ∀ (g : ℝ → ℝ) (hint : IntervalIntegrable g volume 0 1), Tendsto (fun i : ℕ => ∫ t in (0:ℝ)..σ i, g t) atTop (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
      intro g
      intro hint
      have hmono : Monotone (fun i : ℕ => Set.Ioo 0 (σ i)) := by
        intro i j hij x hx
        exact Set.mem_Ioo.2 ⟨hx.1, lt_of_lt_of_le hx.2 (σ_monotone hij)⟩
      have hunion : (⋃ n : ℕ, Set.Ioo 0 (σ n)) = Set.Ioo 0 1 := by
        apply Set.Subset.antisymm
        · refine Set.iUnion_subset fun n x hx => ?_
          exact Set.mem_Ioo.2 ⟨hx.1, (hx.2).trans (σ_lt_one n)⟩
        · intro x hx
          obtain ⟨N, hN⟩ : ∃ N : ℕ, x < σ N := by
            have h1x : 0 < 1 - x := by linarith [hx.2]
            obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - x))
            have hne : ((N + 2 : ℕ) : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.succ_ne_zero (N + 1))
            refine ⟨N, ?_⟩
            have h1 : (1:ℝ) / (1 - x) < ((N + 2 : ℕ) : ℝ) :=
              lt_of_lt_of_le hN (by exact_mod_cast Nat.le_add_right N 2)
            have h2 : (1:ℝ) < ((N + 2 : ℕ) : ℝ) * (1 - x) := (div_lt_iff₀ h1x).mp h1
            rw [mul_comm] at h2
            have h3 : (1:ℝ) / ((N + 2 : ℕ) : ℝ) < 1 - x :=
              (div_lt_iff₀ (by positivity)).mpr (by linarith)
            simp only [σ]
            linarith
          exact Set.mem_iUnion.2 ⟨N, Set.mem_Ioo.2 ⟨hx.1, hN⟩⟩
      have hfiU : IntegrableOn g (⋃ n, Set.Ioo 0 (σ n)) := by
        rw [hunion]
        have h1 : IntegrableOn g (Set.Ioc 0 1) :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp hint
        exact h1.mono_set Set.Ioo_subset_Ioc_self
      have h := MeasureTheory.tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioo) hmono hfiU
      rw [hunion] at h
      have heq : ∫ x in Set.Ioo 0 1, g x = ∫ t in (0:ℝ)..1, g t :=
        MeasureTheory.integral_Ioc_eq_integral_Ioo.symm.trans
          (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm
      rw [heq] at h
      have hpt : ∀ i : ℕ, ∫ t in (0:ℝ)..σ i, g t = ∫ x in Set.Ioo 0 (σ i), g x := fun i =>
        (intervalIntegral.integral_of_le (σ_nonneg i)).trans
          MeasureTheory.integral_Ioc_eq_integral_Ioo
      exact Tendsto.congr (fun i => (hpt i).symm) h
    have r_iff_fwd : ∀ {f : ℝ → ℝ} {a : ℝ} (hi : IntegrableOn f (Set.Ioi a)), IntervalIntegrable (fun t => f (a+t/(1-t))/(1-t)^2) volume 0 1 := by
      intro f
      intro a
      intro hi
      have hsub : ∀ i : ℕ, Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)) ⊆ Set.Ioi a :=
        fun i _ hx => hx.1
      have hfi : ∀ i : ℕ,
          IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) := by
        intro i
        exact (rkey_integrable (f := f) (a := a) (i := i)).mp (hi.mono_set (hsub i))
      have hbound : ∀ i : ℕ,
          ∫ x in Set.Ioc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖
            ≤ ∫ x in Set.Ioi a, ‖f x‖ := by
        intro i
        have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
        have hT1 : σ i < 1 := σ_lt_one i
        have hn : IntegrableOn (fun x : ℝ => ‖f x‖) (Set.Ioi a) :=
          (show Integrable f (volume.restrict _) from hi).norm
        calc ∫ x in Set.Ioc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖
            = ∫ x in Set.Icc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc.symm
          _ = ∫ x in Set.Icc a (a + σ i / (1 - σ i)), ‖f x‖ := rkey_norm hT0 hT1
          _ = ∫ x in Set.Icc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ := by rw [σ_frac i]
          _ = ∫ x in Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc
          _ ≤ ∫ x in Set.Ioi a, ‖f x‖ :=
                MeasureTheory.setIntegral_mono_set hn (ae_of_all _ (fun _ => norm_nonneg _))
                  ((hsub i).eventuallySubset)
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr ?_
      exact MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
        (I := ∫ x in Set.Ioi a, ‖f x‖) (b := σ) hfi σ_tendsto
        (Filter.Eventually.of_forall hbound)
    have r_iff_rev : ∀ {f : ℝ → ℝ} {a : ℝ} (hi : IntervalIntegrable (fun t => f (a+t/(1-t))/(1-t)^2) volume 0 1), IntegrableOn f (Set.Ioi a) := by
      intro f
      intro a
      intro hi
      have hfi0 : IntegrableOn
          (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 1) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp hi
      have hsub : ∀ i : ℕ, Set.Ioc 0 (σ i) ⊆ Set.Ioc 0 1 :=
        fun i => Set.Ioc_subset_Ioc le_rfl (le_of_lt (σ_lt_one i))
      have hfi : ∀ i : ℕ, IntegrableOn f (Set.Ioc a (a + ((i + 1 : ℕ) : ℝ))) := by
        intro i
        exact (rkey_integrable (f := f) (a := a) (i := i)).mpr (hfi0.mono_set (hsub i))
      have hbound : ∀ i : ℕ,
          ∫ x in a..(a + ((i + 1 : ℕ) : ℝ)), ‖f x‖
            ≤ ∫ x in Set.Ioc 0 1, ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ := by
        intro i
        have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
        have hT1 : σ i < 1 := σ_lt_one i
        have hn : IntegrableOn
            (fun x : ℝ => ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖) (Set.Ioc 0 1) :=
          (show Integrable (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2)
            (volume.restrict _) from hfi0).norm
        have hge : (0:ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
        calc ∫ x in a..(a + ((i + 1 : ℕ) : ℝ)), ‖f x‖
            = ∫ x in Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ :=
                intervalIntegral.integral_of_le (by linarith)
          _ = ∫ x in Set.Icc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc.symm
          _ = ∫ x in Set.Icc a (a + σ i / (1 - σ i)), ‖f x‖ := by rw [← σ_frac i]
          _ = ∫ t in Set.Icc 0 (σ i), ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖ :=
                (rkey_norm hT0 hT1).symm
          _ = ∫ x in Set.Ioc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc
          _ ≤ ∫ x in Set.Ioc 0 1, ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.setIntegral_mono_set hn (ae_of_all _ (fun _ => norm_nonneg _))
                  ((hsub i).eventuallySubset)
      exact MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded
        (I := ∫ x in Set.Ioc 0 1, ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖) (a := a) hfi
        (tendsto_add_nat_atTop a) (Filter.Eventually.of_forall hbound)
    exact ⟨r_iff_fwd, r_iff_rev⟩

set_option maxHeartbeats 1000000 in
theorem right_substitution_value {f : ℝ → ℝ} {a : ℝ}
    (hi : IntegrableOn f (Set.Ioi a)) :
    (∫ x in Set.Ioi a, f x) =
      ∫ t in (0 : ℝ)..1, f (a+t/(1-t))/(1-t)^2 := open Set in by
    let σ : ℕ → ℝ := fun i => 1 - 1 / ((i + 2 : ℕ) : ℝ)
    have σ_lt_one : ∀ (i : ℕ), σ i < 1 := by
      intro i
      have hpos : (0:ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      have h : (0:ℝ) < 1 / ((i + 2 : ℕ) : ℝ) := div_pos (by norm_num) hpos
      simp only [σ]
      linarith
    have σ_nonneg : ∀ (i : ℕ), 0 ≤ σ i := by
      intro i
      have h : (1:ℝ) ≤ ((i + 2 : ℕ) : ℝ) := by norm_cast; omega
      have h2 : (0:ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      have h3 : 1 / ((i + 2 : ℕ) : ℝ) ≤ 1 := (div_le_one h2).mpr h
      simp only [σ]
      linarith
    have σ_monotone : Monotone σ := by
      intro i j hij
      have h1 : ((i + 2 : ℕ) : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hij 2
      have h2 : (0:ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      have h3 : (0:ℝ) < ((j + 2 : ℕ) : ℝ) := by positivity
      have h4 : 1 / ((j + 2 : ℕ) : ℝ) ≤ 1 / ((i + 2 : ℕ) : ℝ) := by
        rw [one_div, one_div]
        exact (inv_le_inv₀ h3 h2).mpr h1
      simp only [σ]
      linarith
    have σ_frac : ∀ (i : ℕ), σ i / (1 - σ i) = ((i + 1 : ℕ) : ℝ) := by
      intro i
      have hne : ((i + 2 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero (i + 1))
      simp only [σ]
      field_simp [hne]
      push_cast
      ring
    have σ_tendsto : Tendsto σ atTop (𝓝 1) := by
      have h0 : Tendsto (fun i : ℕ => ((i + 2 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
      have hsub : Tendsto (fun i : ℕ => (1:ℝ) - ((i + 2 : ℕ) : ℝ)⁻¹) atTop (𝓝 ((1:ℝ) - 0)) :=
        tendsto_const_nhds.sub h0
      rw [sub_zero] at hsub
      have hσ : ∀ i, σ i = (1:ℝ) - ((i + 2 : ℕ) : ℝ)⁻¹ := by
        intro i
        simp only [σ, one_div]
      exact Tendsto.congr (fun i => (hσ i).symm) hsub
    have tendsto_add_nat_atTop : ∀ (a : ℝ), Tendsto (fun i : ℕ => a + ((i + 1 : ℕ) : ℝ)) atTop atTop := by
      intro a
      rw [tendsto_atTop_atTop]
      intro b
      obtain ⟨m, hm⟩ := exists_nat_ge (b - a)
      refine ⟨m, fun a' ha' => ?_⟩
      have hle : ((m : ℕ) : ℝ) ≤ ((a' : ℕ) : ℝ) := by exact_mod_cast ha'
      have hcast1 : ((a' + 1 : ℕ) : ℝ) = ((a' : ℕ) : ℝ) + 1 := by norm_cast
      have hcast2 : ((m + 1 : ℕ) : ℝ) = ((m : ℕ) : ℝ) + 1 := by norm_cast
      linarith [hm]
    have tendsto_sub_nat_atBot : ∀ (a : ℝ), Tendsto (fun i : ℕ => a - ((i + 1 : ℕ) : ℝ)) atTop atBot := by
      intro a
      rw [tendsto_atTop_atBot]
      intro b
      obtain ⟨m, hm⟩ := exists_nat_ge (a - b)
      refine ⟨m, fun a' ha' => ?_⟩
      have hle : ((m : ℕ) : ℝ) ≤ ((a' : ℕ) : ℝ) := by exact_mod_cast ha'
      have hcast1 : ((a' + 1 : ℕ) : ℝ) = ((a' : ℕ) : ℝ) + 1 := by norm_cast
      have hcast2 : ((m + 1 : ℕ) : ℝ) = ((m : ℕ) : ℝ) + 1 := by norm_cast
      linarith [hm]
    have smul_eq_div : ∀ (z X : ℝ), (1 / X) • z = z / X := by
      intro z X
      rw [show ∀ r z : ℝ, r • z = r * z from fun _ _ => rfl, div_eq_mul_inv, div_eq_mul_inv,
        one_mul, mul_comm]
    have neg_smul_key : ∀ (z X : ℝ), z / X = -((-1 / X) • z) := by
      intro z X
      rw [show ∀ r z : ℝ, r • z = r * z from fun _ _ => rfl, neg_div, neg_mul, neg_neg,
        div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
    have norm_eq_div : ∀ {z X : ℝ} (hX : 0 < X), ‖z / X‖ = ‖z‖ / X := by
      intro z X
      intro hX
      rw [norm_div]
      simp only [Real.norm_eq_abs, abs_of_pos hX]
    have hasDerivAt_phi : ∀ (a t : ℝ) (ht : t < 1), HasDerivAt (fun u : ℝ => a + u / (1 - u)) (1 / (1 - t) ^ 2) t := by
      intro a t
      intro ht
      have hne : 1 - t ≠ 0 := by linarith
      have hden : HasDerivAt (fun u : ℝ => 1 - u) (0 - 1) t :=
        (hasDerivAt_const t 1).sub (hasDerivAt_id t)
      have hq : HasDerivAt (fun u : ℝ => u / (1 - u)) (1 / (1 - t) ^ 2) t := by
        have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
        have h := hid.fun_div hden hne
        rw [show (1 * (1 - t) - t * (0 - 1)) = 1 by ring] at h
        exact h
      exact hq.const_add a
    have hasDerivAt_psi : ∀ (a t : ℝ) (ht : t < 1), HasDerivAt (fun u : ℝ => a - u / (1 - u)) (-1 / (1 - t) ^ 2) t := by
      intro a t
      intro ht
      have hne : 1 - t ≠ 0 := by linarith
      have hden : HasDerivAt (fun u : ℝ => 1 - u) (0 - 1) t :=
        (hasDerivAt_const t 1).sub (hasDerivAt_id t)
      have hq : HasDerivAt (fun u : ℝ => u / (1 - u)) (1 / (1 - t) ^ 2) t := by
        have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
        have h := hid.fun_div hden hne
        rw [show (1 * (1 - t) - t * (0 - 1)) = 1 by ring] at h
        exact h
      have h := hq.const_sub a
      rw [← neg_div] at h
      exact h
    have continuousOn_phi : ∀ (a T : ℝ) (hT1 : T < 1), ContinuousOn (fun u : ℝ => a + u / (1 - u)) (Set.Icc 0 T) := by
      intro a T
      intro hT1
      refine continuousOn_of_forall_continuousAt fun x hx => ?_
      exact (hasDerivAt_phi a x (by linarith [hx.2, hT1])).continuousAt
    have continuousOn_psi : ∀ (a T : ℝ) (hT1 : T < 1), ContinuousOn (fun u : ℝ => a - u / (1 - u)) (Set.Icc 0 T) := by
      intro a T
      intro hT1
      refine continuousOn_of_forall_continuousAt fun x hx => ?_
      exact (hasDerivAt_psi a x (by linarith [hx.2, hT1])).continuousAt
    have nonneg_inv_sq : ∀ {t : ℝ} (ht : t < 1), 0 ≤ 1 / (1 - t) ^ 2 := by
      intro t
      intro ht
      have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith)
      exact div_nonneg (by norm_num) hpos.le
    have nonpos_neg_inv_sq : ∀ {t : ℝ} (ht : t < 1), -1 / (1 - t) ^ 2 ≤ 0 := by
      intro t
      intro ht
      have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith)
      exact div_nonpos_iff.mpr (Or.inr ⟨by norm_num, hpos.le⟩)
    have rkey : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, f (a + t / (1 - t)) / (1 - t) ^ 2
      = ∫ x in Set.Icc a (a + T / (1 - T)), f x := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          f (a + t / (1 - t)) / (1 - t) ^ 2 = (1 / (1 - t) ^ 2) • f (a + t / (1 - t)) :=
        fun t _ => (smul_eq_div (f (a + t / (1 - t))) ((1 - t) ^ 2)).symm
      have hL : ∫ t in Set.Icc 0 T, f (a + t / (1 - t)) / (1 - t) ^ 2
          = ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • f (a + t / (1 - t)) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • f (a + t / (1 - t))
          = ∫ x in Set.Icc (a + 0 / (1 - 0)) (a + T / (1 - T)), f x :=
        integral_Icc_deriv_smul_of_deriv_nonneg (f := fun u : ℝ => a + u / (1 - u))
          (f' := fun t : ℝ => 1 / (1 - t) ^ 2) (g := f)
          (continuousOn_phi a T hT1) (fun x hx => hasDerivAt_phi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonneg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, add_zero] at hR
      exact hL.trans hR
    have rkey_norm : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖
      = ∫ x in Set.Icc a (a + T / (1 - T)), ‖f x‖ := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖ = (1 / (1 - t) ^ 2) • ‖f (a + t / (1 - t))‖ := by
        intro t ht
        have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith [ht.2, hT1])
        rw [norm_eq_div hpos]
        exact (smul_eq_div _ _).symm
      have hL : ∫ t in Set.Icc 0 T, ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖
          = ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • ‖f (a + t / (1 - t))‖ :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • ‖f (a + t / (1 - t))‖
          = ∫ x in Set.Icc (a + 0 / (1 - 0)) (a + T / (1 - T)), ‖f x‖ :=
        integral_Icc_deriv_smul_of_deriv_nonneg (f := fun u : ℝ => a + u / (1 - u))
          (f' := fun t : ℝ => 1 / (1 - t) ^ 2) (g := fun x => ‖f x‖)
          (continuousOn_phi a T hT1) (fun x hx => hasDerivAt_phi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonneg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, add_zero] at hR
      exact hL.trans hR
    have rkey_integrable : ∀ {f : ℝ → ℝ} {a : ℝ} {i : ℕ}, IntegrableOn f (Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)))
      ↔ IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) := by
      intro f
      intro a
      intro i
      have hsig : σ i / (1 - σ i) = ((i + 1 : ℕ) : ℝ) := σ_frac i
      have hT1 : σ i < 1 := σ_lt_one i
      have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
      have hiff :
          IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a + t / (1 - t))) (Set.Icc 0 (σ i))
            ↔ IntegrableOn f (Set.Icc a (a + ((i + 1 : ℕ) : ℝ))) := by
        have h0 := integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg
          (f := fun u : ℝ => a + u / (1 - u)) (f' := fun t : ℝ => 1 / (1 - t) ^ 2) (g := f)
          (continuousOn_phi a (σ i) hT1) (fun x hx => hasDerivAt_phi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonneg_inv_sq (by linarith [hx.2, hT1])) hT0
        simpa only [zero_div, add_zero, hsig] using h0
      have h1 : IntegrableOn f (Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)))
          ↔ IntegrableOn f (Set.Icc a (a + ((i + 1 : ℕ) : ℝ))) :=
        (integrableOn_Icc_iff_integrableOn_Ioc (f := f) (a := a)
          (b := a + ((i + 1 : ℕ) : ℝ))).symm
      have h2 : IntegrableOn f (Set.Icc a (a + ((i + 1 : ℕ) : ℝ)))
          ↔ IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a + t / (1 - t))) (Set.Icc 0 (σ i)) :=
        hiff.symm
      have h3 : IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a + t / (1 - t)))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i)) :=
        integrableOn_congr_fun
          (fun t _ => smul_eq_div (f (a + t / (1 - t))) ((1 - t) ^ 2)) measurableSet_Icc
      have h4 : IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) :=
        integrableOn_Icc_iff_integrableOn_Ioc
      exact h1.trans h2 |>.trans h3 |>.trans h4
    have lkey : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, f (a - t / (1 - t)) / (1 - t) ^ 2
      = ∫ x in Set.Icc (a - T / (1 - T)) a, f x := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          f (a - t / (1 - t)) / (1 - t) ^ 2 = -((-1 / (1 - t) ^ 2) • f (a - t / (1 - t))) :=
        fun t _ => neg_smul_key (f (a - t / (1 - t))) ((1 - t) ^ 2)
      have hL : ∫ t in Set.Icc 0 T, f (a - t / (1 - t)) / (1 - t) ^ 2
          = ∫ t in Set.Icc 0 T, -((-1 / (1 - t) ^ 2) • f (a - t / (1 - t))) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (-1 / (1 - t) ^ 2) • f (a - t / (1 - t))
          = -∫ x in Set.Icc (a - T / (1 - T)) (a - 0 / (1 - 0)), f x :=
        integral_Icc_deriv_smul_of_deriv_nonpos (f := fun u : ℝ => a - u / (1 - u))
          (f' := fun t : ℝ => -1 / (1 - t) ^ 2) (g := f)
          (continuousOn_psi a T hT1) (fun x hx => hasDerivAt_psi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonpos_neg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, sub_zero] at hR
      rw [hL, MeasureTheory.integral_neg, hR, neg_neg]
    have lkey_norm : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, ‖f (a - t / (1 - t)) / (1 - t) ^ 2‖
      = ∫ x in Set.Icc (a - T / (1 - T)) a, ‖f x‖ := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          ‖f (a - t / (1 - t)) / (1 - t) ^ 2‖
            = -((-1 / (1 - t) ^ 2) • ‖f (a - t / (1 - t))‖) := by
        intro t ht
        have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith [ht.2, hT1])
        rw [norm_eq_div hpos]
        exact neg_smul_key _ _
      have hL : ∫ t in Set.Icc 0 T, ‖f (a - t / (1 - t)) / (1 - t) ^ 2‖
          = ∫ t in Set.Icc 0 T, -((-1 / (1 - t) ^ 2) • ‖f (a - t / (1 - t))‖) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (-1 / (1 - t) ^ 2) • ‖f (a - t / (1 - t))‖
          = -∫ x in Set.Icc (a - T / (1 - T)) (a - 0 / (1 - 0)), ‖f x‖ :=
        integral_Icc_deriv_smul_of_deriv_nonpos (f := fun u : ℝ => a - u / (1 - u))
          (f' := fun t : ℝ => -1 / (1 - t) ^ 2) (g := fun x => ‖f x‖)
          (continuousOn_psi a T hT1) (fun x hx => hasDerivAt_psi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonpos_neg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, sub_zero] at hR
      rw [hL, MeasureTheory.integral_neg, hR, neg_neg]
    have lkey_integrable : ∀ {f : ℝ → ℝ} {a : ℝ} {i : ℕ}, IntegrableOn f (Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a)
      ↔ IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) := by
      intro f
      intro a
      intro i
      have hsig : σ i / (1 - σ i) = ((i + 1 : ℕ) : ℝ) := σ_frac i
      have hT1 : σ i < 1 := σ_lt_one i
      have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
      have hiff :
          IntegrableOn (fun t : ℝ => (-1 / (1 - t) ^ 2) • f (a - t / (1 - t))) (Set.Icc 0 (σ i))
            ↔ IntegrableOn f (Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a) := by
        have h0 := integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos
          (f := fun u : ℝ => a - u / (1 - u)) (f' := fun t : ℝ => -1 / (1 - t) ^ 2) (g := f)
          (continuousOn_psi a (σ i) hT1) (fun x hx => hasDerivAt_psi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonpos_neg_inv_sq (by linarith [hx.2, hT1])) hT0
        simpa only [zero_div, sub_zero, hsig] using h0
      have h1 : IntegrableOn f (Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a)
          ↔ IntegrableOn f (Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a) :=
        (integrableOn_Icc_iff_integrableOn_Ioc (f := f)
          (a := a - ((i + 1 : ℕ) : ℝ)) (b := a)).symm
      have h2 : IntegrableOn f (Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a)
          ↔ IntegrableOn (fun t : ℝ => (-1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
              (Set.Icc 0 (σ i)) :=
        hiff.symm
      have h3 : IntegrableOn (fun t : ℝ => (-1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => -((1 / (1 - t) ^ 2) • f (a - t / (1 - t))))
              (Set.Icc 0 (σ i)) :=
        integrableOn_congr_fun (fun t _ => by rw [neg_div, neg_smul]) measurableSet_Icc
      have h3b : IntegrableOn (fun t : ℝ => -((1 / (1 - t) ^ 2) • f (a - t / (1 - t))))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
              (Set.Icc 0 (σ i)) :=
        integrableOn_neg_iff
      have h3c : IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i)) :=
        integrableOn_congr_fun
          (fun t _ => smul_eq_div (f (a - t / (1 - t))) ((1 - t) ^ 2)) measurableSet_Icc
      have h4 : IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) :=
        integrableOn_Icc_iff_integrableOn_Ioc
      exact h1.trans h2 |>.trans h3 |>.trans h3b |>.trans h3c |>.trans h4
    have tendsto_sigma_integral : ∀ (g : ℝ → ℝ) (hint : IntervalIntegrable g volume 0 1), Tendsto (fun i : ℕ => ∫ t in (0:ℝ)..σ i, g t) atTop (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
      intro g
      intro hint
      have hmono : Monotone (fun i : ℕ => Set.Ioo 0 (σ i)) := by
        intro i j hij x hx
        exact Set.mem_Ioo.2 ⟨hx.1, lt_of_lt_of_le hx.2 (σ_monotone hij)⟩
      have hunion : (⋃ n : ℕ, Set.Ioo 0 (σ n)) = Set.Ioo 0 1 := by
        apply Set.Subset.antisymm
        · refine Set.iUnion_subset fun n x hx => ?_
          exact Set.mem_Ioo.2 ⟨hx.1, (hx.2).trans (σ_lt_one n)⟩
        · intro x hx
          obtain ⟨N, hN⟩ : ∃ N : ℕ, x < σ N := by
            have h1x : 0 < 1 - x := by linarith [hx.2]
            obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - x))
            have hne : ((N + 2 : ℕ) : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.succ_ne_zero (N + 1))
            refine ⟨N, ?_⟩
            have h1 : (1:ℝ) / (1 - x) < ((N + 2 : ℕ) : ℝ) :=
              lt_of_lt_of_le hN (by exact_mod_cast Nat.le_add_right N 2)
            have h2 : (1:ℝ) < ((N + 2 : ℕ) : ℝ) * (1 - x) := (div_lt_iff₀ h1x).mp h1
            rw [mul_comm] at h2
            have h3 : (1:ℝ) / ((N + 2 : ℕ) : ℝ) < 1 - x :=
              (div_lt_iff₀ (by positivity)).mpr (by linarith)
            simp only [σ]
            linarith
          exact Set.mem_iUnion.2 ⟨N, Set.mem_Ioo.2 ⟨hx.1, hN⟩⟩
      have hfiU : IntegrableOn g (⋃ n, Set.Ioo 0 (σ n)) := by
        rw [hunion]
        have h1 : IntegrableOn g (Set.Ioc 0 1) :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp hint
        exact h1.mono_set Set.Ioo_subset_Ioc_self
      have h := MeasureTheory.tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioo) hmono hfiU
      rw [hunion] at h
      have heq : ∫ x in Set.Ioo 0 1, g x = ∫ t in (0:ℝ)..1, g t :=
        MeasureTheory.integral_Ioc_eq_integral_Ioo.symm.trans
          (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm
      rw [heq] at h
      have hpt : ∀ i : ℕ, ∫ t in (0:ℝ)..σ i, g t = ∫ x in Set.Ioo 0 (σ i), g x := fun i =>
        (intervalIntegral.integral_of_le (σ_nonneg i)).trans
          MeasureTheory.integral_Ioc_eq_integral_Ioo
      exact Tendsto.congr (fun i => (hpt i).symm) h
    have r_iff_fwd : ∀ {f : ℝ → ℝ} {a : ℝ} (hi : IntegrableOn f (Set.Ioi a)), IntervalIntegrable (fun t => f (a+t/(1-t))/(1-t)^2) volume 0 1 := by
      intro f
      intro a
      intro hi
      have hsub : ∀ i : ℕ, Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)) ⊆ Set.Ioi a :=
        fun i _ hx => hx.1
      have hfi : ∀ i : ℕ,
          IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) := by
        intro i
        exact (rkey_integrable (f := f) (a := a) (i := i)).mp (hi.mono_set (hsub i))
      have hbound : ∀ i : ℕ,
          ∫ x in Set.Ioc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖
            ≤ ∫ x in Set.Ioi a, ‖f x‖ := by
        intro i
        have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
        have hT1 : σ i < 1 := σ_lt_one i
        have hn : IntegrableOn (fun x : ℝ => ‖f x‖) (Set.Ioi a) :=
          (show Integrable f (volume.restrict _) from hi).norm
        calc ∫ x in Set.Ioc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖
            = ∫ x in Set.Icc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc.symm
          _ = ∫ x in Set.Icc a (a + σ i / (1 - σ i)), ‖f x‖ := rkey_norm hT0 hT1
          _ = ∫ x in Set.Icc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ := by rw [σ_frac i]
          _ = ∫ x in Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc
          _ ≤ ∫ x in Set.Ioi a, ‖f x‖ :=
                MeasureTheory.setIntegral_mono_set hn (ae_of_all _ (fun _ => norm_nonneg _))
                  ((hsub i).eventuallySubset)
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr ?_
      exact MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
        (I := ∫ x in Set.Ioi a, ‖f x‖) (b := σ) hfi σ_tendsto
        (Filter.Eventually.of_forall hbound)
    have r_iff_rev : ∀ {f : ℝ → ℝ} {a : ℝ} (hi : IntervalIntegrable (fun t => f (a+t/(1-t))/(1-t)^2) volume 0 1), IntegrableOn f (Set.Ioi a) := by
      intro f
      intro a
      intro hi
      have hfi0 : IntegrableOn
          (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 1) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp hi
      have hsub : ∀ i : ℕ, Set.Ioc 0 (σ i) ⊆ Set.Ioc 0 1 :=
        fun i => Set.Ioc_subset_Ioc le_rfl (le_of_lt (σ_lt_one i))
      have hfi : ∀ i : ℕ, IntegrableOn f (Set.Ioc a (a + ((i + 1 : ℕ) : ℝ))) := by
        intro i
        exact (rkey_integrable (f := f) (a := a) (i := i)).mpr (hfi0.mono_set (hsub i))
      have hbound : ∀ i : ℕ,
          ∫ x in a..(a + ((i + 1 : ℕ) : ℝ)), ‖f x‖
            ≤ ∫ x in Set.Ioc 0 1, ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ := by
        intro i
        have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
        have hT1 : σ i < 1 := σ_lt_one i
        have hn : IntegrableOn
            (fun x : ℝ => ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖) (Set.Ioc 0 1) :=
          (show Integrable (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2)
            (volume.restrict _) from hfi0).norm
        have hge : (0:ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
        calc ∫ x in a..(a + ((i + 1 : ℕ) : ℝ)), ‖f x‖
            = ∫ x in Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ :=
                intervalIntegral.integral_of_le (by linarith)
          _ = ∫ x in Set.Icc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc.symm
          _ = ∫ x in Set.Icc a (a + σ i / (1 - σ i)), ‖f x‖ := by rw [← σ_frac i]
          _ = ∫ t in Set.Icc 0 (σ i), ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖ :=
                (rkey_norm hT0 hT1).symm
          _ = ∫ x in Set.Ioc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc
          _ ≤ ∫ x in Set.Ioc 0 1, ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.setIntegral_mono_set hn (ae_of_all _ (fun _ => norm_nonneg _))
                  ((hsub i).eventuallySubset)
      exact MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded
        (I := ∫ x in Set.Ioc 0 1, ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖) (a := a) hfi
        (tendsto_add_nat_atTop a) (Filter.Eventually.of_forall hbound)
    have hpieces : ∀ i : ℕ,
        ∫ x in a..(a + ((i + 1 : ℕ) : ℝ)), f x
          = ∫ t in (0:ℝ)..σ i, f (a + t / (1 - t)) / (1 - t) ^ 2 := by
      intro i
      have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
      have hT1 : σ i < 1 := σ_lt_one i
      have hge : (0:ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
      have hend : Set.Icc a (a + σ i / (1 - σ i))
          = Set.Icc a (a + ((i + 1 : ℕ) : ℝ)) := by
        rw [σ_frac i]
      calc ∫ x in a..(a + ((i + 1 : ℕ) : ℝ)), f x
          = ∫ x in Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)), f x :=
              intervalIntegral.integral_of_le (by linarith)
        _ = ∫ x in Set.Icc a (a + ((i + 1 : ℕ) : ℝ)), f x :=
              MeasureTheory.integral_Icc_eq_integral_Ioc.symm
        _ = ∫ x in Set.Icc a (a + σ i / (1 - σ i)), f x := by rw [hend]
        _ = ∫ t in Set.Icc 0 (σ i), f (a + t / (1 - t)) / (1 - t) ^ 2 := (rkey hT0 hT1).symm
        _ = ∫ t in Set.Ioc 0 (σ i), f (a + t / (1 - t)) / (1 - t) ^ 2 :=
              MeasureTheory.integral_Icc_eq_integral_Ioc
        _ = ∫ t in (0:ℝ)..σ i, f (a + t / (1 - t)) / (1 - t) ^ 2 :=
              (intervalIntegral.integral_of_le hT0).symm
    have hR : Tendsto (fun i : ℕ => ∫ x in a..(a + ((i + 1 : ℕ) : ℝ)), f x) atTop
        (𝓝 (∫ x in Set.Ioi a, f x)) :=
      MeasureTheory.intervalIntegral_tendsto_integral_Ioi a hi (tendsto_add_nat_atTop a)
    have hL : Tendsto (fun i : ℕ => ∫ t in (0:ℝ)..σ i, f (a + t / (1 - t)) / (1 - t) ^ 2) atTop
        (𝓝 (∫ t in (0:ℝ)..1, f (a + t / (1 - t)) / (1 - t) ^ 2)) :=
      tendsto_sigma_integral _ (r_iff_fwd hi)
    refine tendsto_nhds_unique hR ?_
    exact Tendsto.congr' (Filter.Eventually.of_forall fun i => (hpieces i).symm) hL

set_option maxHeartbeats 1000000 in
theorem left_substitution {f : ℝ → ℝ} {a : ℝ} (hm : Measurable f) :
    IntegrableOn f (Set.Iio a) ↔
      IntervalIntegrable (fun t => f (a-t/(1-t))/(1-t)^2) volume 0 1 := open Set in by
    let σ : ℕ → ℝ := fun i => 1 - 1 / ((i + 2 : ℕ) : ℝ)
    have σ_lt_one : ∀ (i : ℕ), σ i < 1 := by
      intro i
      have hpos : (0:ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      have h : (0:ℝ) < 1 / ((i + 2 : ℕ) : ℝ) := div_pos (by norm_num) hpos
      simp only [σ]
      linarith
    have σ_nonneg : ∀ (i : ℕ), 0 ≤ σ i := by
      intro i
      have h : (1:ℝ) ≤ ((i + 2 : ℕ) : ℝ) := by norm_cast; omega
      have h2 : (0:ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      have h3 : 1 / ((i + 2 : ℕ) : ℝ) ≤ 1 := (div_le_one h2).mpr h
      simp only [σ]
      linarith
    have σ_monotone : Monotone σ := by
      intro i j hij
      have h1 : ((i + 2 : ℕ) : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hij 2
      have h2 : (0:ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      have h3 : (0:ℝ) < ((j + 2 : ℕ) : ℝ) := by positivity
      have h4 : 1 / ((j + 2 : ℕ) : ℝ) ≤ 1 / ((i + 2 : ℕ) : ℝ) := by
        rw [one_div, one_div]
        exact (inv_le_inv₀ h3 h2).mpr h1
      simp only [σ]
      linarith
    have σ_frac : ∀ (i : ℕ), σ i / (1 - σ i) = ((i + 1 : ℕ) : ℝ) := by
      intro i
      have hne : ((i + 2 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero (i + 1))
      simp only [σ]
      field_simp [hne]
      push_cast
      ring
    have σ_tendsto : Tendsto σ atTop (𝓝 1) := by
      have h0 : Tendsto (fun i : ℕ => ((i + 2 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
      have hsub : Tendsto (fun i : ℕ => (1:ℝ) - ((i + 2 : ℕ) : ℝ)⁻¹) atTop (𝓝 ((1:ℝ) - 0)) :=
        tendsto_const_nhds.sub h0
      rw [sub_zero] at hsub
      have hσ : ∀ i, σ i = (1:ℝ) - ((i + 2 : ℕ) : ℝ)⁻¹ := by
        intro i
        simp only [σ, one_div]
      exact Tendsto.congr (fun i => (hσ i).symm) hsub
    have tendsto_add_nat_atTop : ∀ (a : ℝ), Tendsto (fun i : ℕ => a + ((i + 1 : ℕ) : ℝ)) atTop atTop := by
      intro a
      rw [tendsto_atTop_atTop]
      intro b
      obtain ⟨m, hm⟩ := exists_nat_ge (b - a)
      refine ⟨m, fun a' ha' => ?_⟩
      have hle : ((m : ℕ) : ℝ) ≤ ((a' : ℕ) : ℝ) := by exact_mod_cast ha'
      have hcast1 : ((a' + 1 : ℕ) : ℝ) = ((a' : ℕ) : ℝ) + 1 := by norm_cast
      have hcast2 : ((m + 1 : ℕ) : ℝ) = ((m : ℕ) : ℝ) + 1 := by norm_cast
      linarith [hm]
    have tendsto_sub_nat_atBot : ∀ (a : ℝ), Tendsto (fun i : ℕ => a - ((i + 1 : ℕ) : ℝ)) atTop atBot := by
      intro a
      rw [tendsto_atTop_atBot]
      intro b
      obtain ⟨m, hm⟩ := exists_nat_ge (a - b)
      refine ⟨m, fun a' ha' => ?_⟩
      have hle : ((m : ℕ) : ℝ) ≤ ((a' : ℕ) : ℝ) := by exact_mod_cast ha'
      have hcast1 : ((a' + 1 : ℕ) : ℝ) = ((a' : ℕ) : ℝ) + 1 := by norm_cast
      have hcast2 : ((m + 1 : ℕ) : ℝ) = ((m : ℕ) : ℝ) + 1 := by norm_cast
      linarith [hm]
    have smul_eq_div : ∀ (z X : ℝ), (1 / X) • z = z / X := by
      intro z X
      rw [show ∀ r z : ℝ, r • z = r * z from fun _ _ => rfl, div_eq_mul_inv, div_eq_mul_inv,
        one_mul, mul_comm]
    have neg_smul_key : ∀ (z X : ℝ), z / X = -((-1 / X) • z) := by
      intro z X
      rw [show ∀ r z : ℝ, r • z = r * z from fun _ _ => rfl, neg_div, neg_mul, neg_neg,
        div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
    have norm_eq_div : ∀ {z X : ℝ} (hX : 0 < X), ‖z / X‖ = ‖z‖ / X := by
      intro z X
      intro hX
      rw [norm_div]
      simp only [Real.norm_eq_abs, abs_of_pos hX]
    have hasDerivAt_phi : ∀ (a t : ℝ) (ht : t < 1), HasDerivAt (fun u : ℝ => a + u / (1 - u)) (1 / (1 - t) ^ 2) t := by
      intro a t
      intro ht
      have hne : 1 - t ≠ 0 := by linarith
      have hden : HasDerivAt (fun u : ℝ => 1 - u) (0 - 1) t :=
        (hasDerivAt_const t 1).sub (hasDerivAt_id t)
      have hq : HasDerivAt (fun u : ℝ => u / (1 - u)) (1 / (1 - t) ^ 2) t := by
        have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
        have h := hid.fun_div hden hne
        rw [show (1 * (1 - t) - t * (0 - 1)) = 1 by ring] at h
        exact h
      exact hq.const_add a
    have hasDerivAt_psi : ∀ (a t : ℝ) (ht : t < 1), HasDerivAt (fun u : ℝ => a - u / (1 - u)) (-1 / (1 - t) ^ 2) t := by
      intro a t
      intro ht
      have hne : 1 - t ≠ 0 := by linarith
      have hden : HasDerivAt (fun u : ℝ => 1 - u) (0 - 1) t :=
        (hasDerivAt_const t 1).sub (hasDerivAt_id t)
      have hq : HasDerivAt (fun u : ℝ => u / (1 - u)) (1 / (1 - t) ^ 2) t := by
        have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
        have h := hid.fun_div hden hne
        rw [show (1 * (1 - t) - t * (0 - 1)) = 1 by ring] at h
        exact h
      have h := hq.const_sub a
      rw [← neg_div] at h
      exact h
    have continuousOn_phi : ∀ (a T : ℝ) (hT1 : T < 1), ContinuousOn (fun u : ℝ => a + u / (1 - u)) (Set.Icc 0 T) := by
      intro a T
      intro hT1
      refine continuousOn_of_forall_continuousAt fun x hx => ?_
      exact (hasDerivAt_phi a x (by linarith [hx.2, hT1])).continuousAt
    have continuousOn_psi : ∀ (a T : ℝ) (hT1 : T < 1), ContinuousOn (fun u : ℝ => a - u / (1 - u)) (Set.Icc 0 T) := by
      intro a T
      intro hT1
      refine continuousOn_of_forall_continuousAt fun x hx => ?_
      exact (hasDerivAt_psi a x (by linarith [hx.2, hT1])).continuousAt
    have nonneg_inv_sq : ∀ {t : ℝ} (ht : t < 1), 0 ≤ 1 / (1 - t) ^ 2 := by
      intro t
      intro ht
      have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith)
      exact div_nonneg (by norm_num) hpos.le
    have nonpos_neg_inv_sq : ∀ {t : ℝ} (ht : t < 1), -1 / (1 - t) ^ 2 ≤ 0 := by
      intro t
      intro ht
      have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith)
      exact div_nonpos_iff.mpr (Or.inr ⟨by norm_num, hpos.le⟩)
    have rkey : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, f (a + t / (1 - t)) / (1 - t) ^ 2
      = ∫ x in Set.Icc a (a + T / (1 - T)), f x := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          f (a + t / (1 - t)) / (1 - t) ^ 2 = (1 / (1 - t) ^ 2) • f (a + t / (1 - t)) :=
        fun t _ => (smul_eq_div (f (a + t / (1 - t))) ((1 - t) ^ 2)).symm
      have hL : ∫ t in Set.Icc 0 T, f (a + t / (1 - t)) / (1 - t) ^ 2
          = ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • f (a + t / (1 - t)) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • f (a + t / (1 - t))
          = ∫ x in Set.Icc (a + 0 / (1 - 0)) (a + T / (1 - T)), f x :=
        integral_Icc_deriv_smul_of_deriv_nonneg (f := fun u : ℝ => a + u / (1 - u))
          (f' := fun t : ℝ => 1 / (1 - t) ^ 2) (g := f)
          (continuousOn_phi a T hT1) (fun x hx => hasDerivAt_phi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonneg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, add_zero] at hR
      exact hL.trans hR
    have rkey_norm : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖
      = ∫ x in Set.Icc a (a + T / (1 - T)), ‖f x‖ := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖ = (1 / (1 - t) ^ 2) • ‖f (a + t / (1 - t))‖ := by
        intro t ht
        have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith [ht.2, hT1])
        rw [norm_eq_div hpos]
        exact (smul_eq_div _ _).symm
      have hL : ∫ t in Set.Icc 0 T, ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖
          = ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • ‖f (a + t / (1 - t))‖ :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • ‖f (a + t / (1 - t))‖
          = ∫ x in Set.Icc (a + 0 / (1 - 0)) (a + T / (1 - T)), ‖f x‖ :=
        integral_Icc_deriv_smul_of_deriv_nonneg (f := fun u : ℝ => a + u / (1 - u))
          (f' := fun t : ℝ => 1 / (1 - t) ^ 2) (g := fun x => ‖f x‖)
          (continuousOn_phi a T hT1) (fun x hx => hasDerivAt_phi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonneg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, add_zero] at hR
      exact hL.trans hR
    have rkey_integrable : ∀ {f : ℝ → ℝ} {a : ℝ} {i : ℕ}, IntegrableOn f (Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)))
      ↔ IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) := by
      intro f
      intro a
      intro i
      have hsig : σ i / (1 - σ i) = ((i + 1 : ℕ) : ℝ) := σ_frac i
      have hT1 : σ i < 1 := σ_lt_one i
      have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
      have hiff :
          IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a + t / (1 - t))) (Set.Icc 0 (σ i))
            ↔ IntegrableOn f (Set.Icc a (a + ((i + 1 : ℕ) : ℝ))) := by
        have h0 := integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg
          (f := fun u : ℝ => a + u / (1 - u)) (f' := fun t : ℝ => 1 / (1 - t) ^ 2) (g := f)
          (continuousOn_phi a (σ i) hT1) (fun x hx => hasDerivAt_phi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonneg_inv_sq (by linarith [hx.2, hT1])) hT0
        simpa only [zero_div, add_zero, hsig] using h0
      have h1 : IntegrableOn f (Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)))
          ↔ IntegrableOn f (Set.Icc a (a + ((i + 1 : ℕ) : ℝ))) :=
        (integrableOn_Icc_iff_integrableOn_Ioc (f := f) (a := a)
          (b := a + ((i + 1 : ℕ) : ℝ))).symm
      have h2 : IntegrableOn f (Set.Icc a (a + ((i + 1 : ℕ) : ℝ)))
          ↔ IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a + t / (1 - t))) (Set.Icc 0 (σ i)) :=
        hiff.symm
      have h3 : IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a + t / (1 - t)))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i)) :=
        integrableOn_congr_fun
          (fun t _ => smul_eq_div (f (a + t / (1 - t))) ((1 - t) ^ 2)) measurableSet_Icc
      have h4 : IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) :=
        integrableOn_Icc_iff_integrableOn_Ioc
      exact h1.trans h2 |>.trans h3 |>.trans h4
    have lkey : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, f (a - t / (1 - t)) / (1 - t) ^ 2
      = ∫ x in Set.Icc (a - T / (1 - T)) a, f x := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          f (a - t / (1 - t)) / (1 - t) ^ 2 = -((-1 / (1 - t) ^ 2) • f (a - t / (1 - t))) :=
        fun t _ => neg_smul_key (f (a - t / (1 - t))) ((1 - t) ^ 2)
      have hL : ∫ t in Set.Icc 0 T, f (a - t / (1 - t)) / (1 - t) ^ 2
          = ∫ t in Set.Icc 0 T, -((-1 / (1 - t) ^ 2) • f (a - t / (1 - t))) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (-1 / (1 - t) ^ 2) • f (a - t / (1 - t))
          = -∫ x in Set.Icc (a - T / (1 - T)) (a - 0 / (1 - 0)), f x :=
        integral_Icc_deriv_smul_of_deriv_nonpos (f := fun u : ℝ => a - u / (1 - u))
          (f' := fun t : ℝ => -1 / (1 - t) ^ 2) (g := f)
          (continuousOn_psi a T hT1) (fun x hx => hasDerivAt_psi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonpos_neg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, sub_zero] at hR
      rw [hL, MeasureTheory.integral_neg, hR, neg_neg]
    have lkey_norm : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, ‖f (a - t / (1 - t)) / (1 - t) ^ 2‖
      = ∫ x in Set.Icc (a - T / (1 - T)) a, ‖f x‖ := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          ‖f (a - t / (1 - t)) / (1 - t) ^ 2‖
            = -((-1 / (1 - t) ^ 2) • ‖f (a - t / (1 - t))‖) := by
        intro t ht
        have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith [ht.2, hT1])
        rw [norm_eq_div hpos]
        exact neg_smul_key _ _
      have hL : ∫ t in Set.Icc 0 T, ‖f (a - t / (1 - t)) / (1 - t) ^ 2‖
          = ∫ t in Set.Icc 0 T, -((-1 / (1 - t) ^ 2) • ‖f (a - t / (1 - t))‖) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (-1 / (1 - t) ^ 2) • ‖f (a - t / (1 - t))‖
          = -∫ x in Set.Icc (a - T / (1 - T)) (a - 0 / (1 - 0)), ‖f x‖ :=
        integral_Icc_deriv_smul_of_deriv_nonpos (f := fun u : ℝ => a - u / (1 - u))
          (f' := fun t : ℝ => -1 / (1 - t) ^ 2) (g := fun x => ‖f x‖)
          (continuousOn_psi a T hT1) (fun x hx => hasDerivAt_psi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonpos_neg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, sub_zero] at hR
      rw [hL, MeasureTheory.integral_neg, hR, neg_neg]
    have lkey_integrable : ∀ {f : ℝ → ℝ} {a : ℝ} {i : ℕ}, IntegrableOn f (Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a)
      ↔ IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) := by
      intro f
      intro a
      intro i
      have hsig : σ i / (1 - σ i) = ((i + 1 : ℕ) : ℝ) := σ_frac i
      have hT1 : σ i < 1 := σ_lt_one i
      have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
      have hiff :
          IntegrableOn (fun t : ℝ => (-1 / (1 - t) ^ 2) • f (a - t / (1 - t))) (Set.Icc 0 (σ i))
            ↔ IntegrableOn f (Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a) := by
        have h0 := integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos
          (f := fun u : ℝ => a - u / (1 - u)) (f' := fun t : ℝ => -1 / (1 - t) ^ 2) (g := f)
          (continuousOn_psi a (σ i) hT1) (fun x hx => hasDerivAt_psi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonpos_neg_inv_sq (by linarith [hx.2, hT1])) hT0
        simpa only [zero_div, sub_zero, hsig] using h0
      have h1 : IntegrableOn f (Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a)
          ↔ IntegrableOn f (Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a) :=
        (integrableOn_Icc_iff_integrableOn_Ioc (f := f)
          (a := a - ((i + 1 : ℕ) : ℝ)) (b := a)).symm
      have h2 : IntegrableOn f (Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a)
          ↔ IntegrableOn (fun t : ℝ => (-1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
              (Set.Icc 0 (σ i)) :=
        hiff.symm
      have h3 : IntegrableOn (fun t : ℝ => (-1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => -((1 / (1 - t) ^ 2) • f (a - t / (1 - t))))
              (Set.Icc 0 (σ i)) :=
        integrableOn_congr_fun (fun t _ => by rw [neg_div, neg_smul]) measurableSet_Icc
      have h3b : IntegrableOn (fun t : ℝ => -((1 / (1 - t) ^ 2) • f (a - t / (1 - t))))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
              (Set.Icc 0 (σ i)) :=
        integrableOn_neg_iff
      have h3c : IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i)) :=
        integrableOn_congr_fun
          (fun t _ => smul_eq_div (f (a - t / (1 - t))) ((1 - t) ^ 2)) measurableSet_Icc
      have h4 : IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) :=
        integrableOn_Icc_iff_integrableOn_Ioc
      exact h1.trans h2 |>.trans h3 |>.trans h3b |>.trans h3c |>.trans h4
    have tendsto_sigma_integral : ∀ (g : ℝ → ℝ) (hint : IntervalIntegrable g volume 0 1), Tendsto (fun i : ℕ => ∫ t in (0:ℝ)..σ i, g t) atTop (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
      intro g
      intro hint
      have hmono : Monotone (fun i : ℕ => Set.Ioo 0 (σ i)) := by
        intro i j hij x hx
        exact Set.mem_Ioo.2 ⟨hx.1, lt_of_lt_of_le hx.2 (σ_monotone hij)⟩
      have hunion : (⋃ n : ℕ, Set.Ioo 0 (σ n)) = Set.Ioo 0 1 := by
        apply Set.Subset.antisymm
        · refine Set.iUnion_subset fun n x hx => ?_
          exact Set.mem_Ioo.2 ⟨hx.1, (hx.2).trans (σ_lt_one n)⟩
        · intro x hx
          obtain ⟨N, hN⟩ : ∃ N : ℕ, x < σ N := by
            have h1x : 0 < 1 - x := by linarith [hx.2]
            obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - x))
            have hne : ((N + 2 : ℕ) : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.succ_ne_zero (N + 1))
            refine ⟨N, ?_⟩
            have h1 : (1:ℝ) / (1 - x) < ((N + 2 : ℕ) : ℝ) :=
              lt_of_lt_of_le hN (by exact_mod_cast Nat.le_add_right N 2)
            have h2 : (1:ℝ) < ((N + 2 : ℕ) : ℝ) * (1 - x) := (div_lt_iff₀ h1x).mp h1
            rw [mul_comm] at h2
            have h3 : (1:ℝ) / ((N + 2 : ℕ) : ℝ) < 1 - x :=
              (div_lt_iff₀ (by positivity)).mpr (by linarith)
            simp only [σ]
            linarith
          exact Set.mem_iUnion.2 ⟨N, Set.mem_Ioo.2 ⟨hx.1, hN⟩⟩
      have hfiU : IntegrableOn g (⋃ n, Set.Ioo 0 (σ n)) := by
        rw [hunion]
        have h1 : IntegrableOn g (Set.Ioc 0 1) :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp hint
        exact h1.mono_set Set.Ioo_subset_Ioc_self
      have h := MeasureTheory.tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioo) hmono hfiU
      rw [hunion] at h
      have heq : ∫ x in Set.Ioo 0 1, g x = ∫ t in (0:ℝ)..1, g t :=
        MeasureTheory.integral_Ioc_eq_integral_Ioo.symm.trans
          (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm
      rw [heq] at h
      have hpt : ∀ i : ℕ, ∫ t in (0:ℝ)..σ i, g t = ∫ x in Set.Ioo 0 (σ i), g x := fun i =>
        (intervalIntegral.integral_of_le (σ_nonneg i)).trans
          MeasureTheory.integral_Ioc_eq_integral_Ioo
      exact Tendsto.congr (fun i => (hpt i).symm) h
    have r_iff_fwd : ∀ {f : ℝ → ℝ} {a : ℝ} (hi : IntegrableOn f (Set.Ioi a)), IntervalIntegrable (fun t => f (a+t/(1-t))/(1-t)^2) volume 0 1 := by
      intro f
      intro a
      intro hi
      have hsub : ∀ i : ℕ, Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)) ⊆ Set.Ioi a :=
        fun i _ hx => hx.1
      have hfi : ∀ i : ℕ,
          IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) := by
        intro i
        exact (rkey_integrable (f := f) (a := a) (i := i)).mp (hi.mono_set (hsub i))
      have hbound : ∀ i : ℕ,
          ∫ x in Set.Ioc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖
            ≤ ∫ x in Set.Ioi a, ‖f x‖ := by
        intro i
        have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
        have hT1 : σ i < 1 := σ_lt_one i
        have hn : IntegrableOn (fun x : ℝ => ‖f x‖) (Set.Ioi a) :=
          (show Integrable f (volume.restrict _) from hi).norm
        calc ∫ x in Set.Ioc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖
            = ∫ x in Set.Icc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc.symm
          _ = ∫ x in Set.Icc a (a + σ i / (1 - σ i)), ‖f x‖ := rkey_norm hT0 hT1
          _ = ∫ x in Set.Icc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ := by rw [σ_frac i]
          _ = ∫ x in Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc
          _ ≤ ∫ x in Set.Ioi a, ‖f x‖ :=
                MeasureTheory.setIntegral_mono_set hn (ae_of_all _ (fun _ => norm_nonneg _))
                  ((hsub i).eventuallySubset)
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr ?_
      exact MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
        (I := ∫ x in Set.Ioi a, ‖f x‖) (b := σ) hfi σ_tendsto
        (Filter.Eventually.of_forall hbound)
    have r_iff_rev : ∀ {f : ℝ → ℝ} {a : ℝ} (hi : IntervalIntegrable (fun t => f (a+t/(1-t))/(1-t)^2) volume 0 1), IntegrableOn f (Set.Ioi a) := by
      intro f
      intro a
      intro hi
      have hfi0 : IntegrableOn
          (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 1) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp hi
      have hsub : ∀ i : ℕ, Set.Ioc 0 (σ i) ⊆ Set.Ioc 0 1 :=
        fun i => Set.Ioc_subset_Ioc le_rfl (le_of_lt (σ_lt_one i))
      have hfi : ∀ i : ℕ, IntegrableOn f (Set.Ioc a (a + ((i + 1 : ℕ) : ℝ))) := by
        intro i
        exact (rkey_integrable (f := f) (a := a) (i := i)).mpr (hfi0.mono_set (hsub i))
      have hbound : ∀ i : ℕ,
          ∫ x in a..(a + ((i + 1 : ℕ) : ℝ)), ‖f x‖
            ≤ ∫ x in Set.Ioc 0 1, ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ := by
        intro i
        have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
        have hT1 : σ i < 1 := σ_lt_one i
        have hn : IntegrableOn
            (fun x : ℝ => ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖) (Set.Ioc 0 1) :=
          (show Integrable (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2)
            (volume.restrict _) from hfi0).norm
        have hge : (0:ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
        calc ∫ x in a..(a + ((i + 1 : ℕ) : ℝ)), ‖f x‖
            = ∫ x in Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ :=
                intervalIntegral.integral_of_le (by linarith)
          _ = ∫ x in Set.Icc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc.symm
          _ = ∫ x in Set.Icc a (a + σ i / (1 - σ i)), ‖f x‖ := by rw [← σ_frac i]
          _ = ∫ t in Set.Icc 0 (σ i), ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖ :=
                (rkey_norm hT0 hT1).symm
          _ = ∫ x in Set.Ioc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc
          _ ≤ ∫ x in Set.Ioc 0 1, ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.setIntegral_mono_set hn (ae_of_all _ (fun _ => norm_nonneg _))
                  ((hsub i).eventuallySubset)
      exact MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded
        (I := ∫ x in Set.Ioc 0 1, ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖) (a := a) hfi
        (tendsto_add_nat_atTop a) (Filter.Eventually.of_forall hbound)
    have l_iff_fwd : ∀ {f : ℝ → ℝ} {a : ℝ} (hi : IntegrableOn f (Set.Iio a)), IntervalIntegrable (fun t => f (a-t/(1-t))/(1-t)^2) volume 0 1 := by
      intro f
      intro a
      intro hi
      have hsub : ∀ i : ℕ, Set.Ioo (a - ((i + 1 : ℕ) : ℝ)) a ⊆ Set.Iio a :=
        fun i => Set.Ioo_subset_Iio_self
      have hfi : ∀ i : ℕ,
          IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) := by
        intro i
        exact (lkey_integrable (f := f) (a := a) (i := i)).mp
          ((integrableOn_Ioc_iff_integrableOn_Ioo).mpr (hi.mono_set (hsub i)))
      have hbound : ∀ i : ℕ,
          ∫ x in Set.Ioc 0 (σ i), ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖
            ≤ ∫ x in Set.Iio a, ‖f x‖ := by
        intro i
        have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
        have hT1 : σ i < 1 := σ_lt_one i
        have hn : IntegrableOn (fun x : ℝ => ‖f x‖) (Set.Iio a) :=
          (show Integrable f (volume.restrict _) from hi).norm
        have hsub2 : ∀ i : ℕ, Set.Ico (a - ((i + 1 : ℕ) : ℝ)) a ⊆ Set.Iio a :=
          fun i => Set.Ico_subset_Iio_self
        calc ∫ x in Set.Ioc 0 (σ i), ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖
            = ∫ x in Set.Icc 0 (σ i), ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc.symm
          _ = ∫ x in Set.Icc (a - σ i / (1 - σ i)) a, ‖f x‖ := lkey_norm hT0 hT1
          _ = ∫ x in Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a, ‖f x‖ := by rw [← σ_frac i]
          _ = ∫ x in Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a, ‖f x‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc
          _ = ∫ x in Set.Ico (a - ((i + 1 : ℕ) : ℝ)) a, ‖f x‖ := by
                rw [MeasureTheory.integral_Ico_eq_integral_Ioo,
                  MeasureTheory.integral_Ioc_eq_integral_Ioo]
          _ ≤ ∫ x in Set.Iio a, ‖f x‖ :=
                MeasureTheory.setIntegral_mono_set hn (ae_of_all _ (fun _ => norm_nonneg _))
                  ((hsub2 i).eventuallySubset)
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr ?_
      exact MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
        (I := ∫ x in Set.Iio a, ‖f x‖) (b := σ) hfi σ_tendsto
        (Filter.Eventually.of_forall hbound)
    have l_iff_rev : ∀ {f : ℝ → ℝ} {a : ℝ} (hi : IntervalIntegrable (fun t => f (a-t/(1-t))/(1-t)^2) volume 0 1), IntegrableOn f (Set.Iio a) := by
      intro f
      intro a
      intro hi
      have hfi0 : IntegrableOn
          (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 1) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp hi
      have hsub : ∀ i : ℕ, Set.Ioc 0 (σ i) ⊆ Set.Ioc 0 1 :=
        fun i => Set.Ioc_subset_Ioc le_rfl (le_of_lt (σ_lt_one i))
      have hfi : ∀ i : ℕ, IntegrableOn f (Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a) := by
        intro i
        exact (lkey_integrable (f := f) (a := a) (i := i)).mpr (hfi0.mono_set (hsub i))
      have hbound : ∀ i : ℕ,
          ∫ x in (a - ((i + 1 : ℕ) : ℝ))..a, ‖f x‖
            ≤ ∫ x in Set.Ioc 0 1, ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖ := by
        intro i
        have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
        have hT1 : σ i < 1 := σ_lt_one i
        have hn : IntegrableOn
            (fun x : ℝ => ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖) (Set.Ioc 0 1) :=
          (show Integrable (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2)
            (volume.restrict _) from hfi0).norm
        have hge : (0:ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
        calc ∫ x in (a - ((i + 1 : ℕ) : ℝ))..a, ‖f x‖
            = ∫ x in Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a, ‖f x‖ :=
                intervalIntegral.integral_of_le (by linarith)
          _ = ∫ x in Set.Ico (a - ((i + 1 : ℕ) : ℝ)) a, ‖f x‖ := by
                rw [MeasureTheory.integral_Ico_eq_integral_Ioo,
                  MeasureTheory.integral_Ioc_eq_integral_Ioo]
          _ = ∫ x in Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a, ‖f x‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ico.symm
          _ = ∫ x in Set.Icc (a - σ i / (1 - σ i)) a, ‖f x‖ := by rw [← σ_frac i]
          _ = ∫ t in Set.Icc 0 (σ i), ‖f (a - t / (1 - t)) / (1 - t) ^ 2‖ :=
                (lkey_norm hT0 hT1).symm
          _ = ∫ x in Set.Ioc 0 (σ i), ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc
          _ ≤ ∫ x in Set.Ioc 0 1, ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.setIntegral_mono_set hn (ae_of_all _ (fun _ => norm_nonneg _))
                  ((hsub i).eventuallySubset)
      have hIic : IntegrableOn f (Set.Iic a) :=
        MeasureTheory.integrableOn_Iic_of_intervalIntegral_norm_bounded
          (I := ∫ x in Set.Ioc 0 1, ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖)
          (a := fun i : ℕ => a - ((i + 1 : ℕ) : ℝ)) (b := a) hfi (tendsto_sub_nat_atBot a)
          (Filter.Eventually.of_forall hbound)
      have hAE : Set.Iio a =ᵐ[volume] Set.Iic a := Iio_ae_eq_Iic
      exact hIic.congr_set_ae hAE
    exact ⟨l_iff_fwd, l_iff_rev⟩

set_option maxHeartbeats 1000000 in
theorem left_substitution_value {f : ℝ → ℝ} {a : ℝ}
    (hi : IntegrableOn f (Set.Iio a)) :
    (∫ x in Set.Iio a, f x) =
      ∫ t in (0 : ℝ)..1, f (a-t/(1-t))/(1-t)^2 := open Set in by
    let σ : ℕ → ℝ := fun i => 1 - 1 / ((i + 2 : ℕ) : ℝ)
    have σ_lt_one : ∀ (i : ℕ), σ i < 1 := by
      intro i
      have hpos : (0:ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      have h : (0:ℝ) < 1 / ((i + 2 : ℕ) : ℝ) := div_pos (by norm_num) hpos
      simp only [σ]
      linarith
    have σ_nonneg : ∀ (i : ℕ), 0 ≤ σ i := by
      intro i
      have h : (1:ℝ) ≤ ((i + 2 : ℕ) : ℝ) := by norm_cast; omega
      have h2 : (0:ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      have h3 : 1 / ((i + 2 : ℕ) : ℝ) ≤ 1 := (div_le_one h2).mpr h
      simp only [σ]
      linarith
    have σ_monotone : Monotone σ := by
      intro i j hij
      have h1 : ((i + 2 : ℕ) : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hij 2
      have h2 : (0:ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      have h3 : (0:ℝ) < ((j + 2 : ℕ) : ℝ) := by positivity
      have h4 : 1 / ((j + 2 : ℕ) : ℝ) ≤ 1 / ((i + 2 : ℕ) : ℝ) := by
        rw [one_div, one_div]
        exact (inv_le_inv₀ h3 h2).mpr h1
      simp only [σ]
      linarith
    have σ_frac : ∀ (i : ℕ), σ i / (1 - σ i) = ((i + 1 : ℕ) : ℝ) := by
      intro i
      have hne : ((i + 2 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero (i + 1))
      simp only [σ]
      field_simp [hne]
      push_cast
      ring
    have σ_tendsto : Tendsto σ atTop (𝓝 1) := by
      have h0 : Tendsto (fun i : ℕ => ((i + 2 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
      have hsub : Tendsto (fun i : ℕ => (1:ℝ) - ((i + 2 : ℕ) : ℝ)⁻¹) atTop (𝓝 ((1:ℝ) - 0)) :=
        tendsto_const_nhds.sub h0
      rw [sub_zero] at hsub
      have hσ : ∀ i, σ i = (1:ℝ) - ((i + 2 : ℕ) : ℝ)⁻¹ := by
        intro i
        simp only [σ, one_div]
      exact Tendsto.congr (fun i => (hσ i).symm) hsub
    have tendsto_add_nat_atTop : ∀ (a : ℝ), Tendsto (fun i : ℕ => a + ((i + 1 : ℕ) : ℝ)) atTop atTop := by
      intro a
      rw [tendsto_atTop_atTop]
      intro b
      obtain ⟨m, hm⟩ := exists_nat_ge (b - a)
      refine ⟨m, fun a' ha' => ?_⟩
      have hle : ((m : ℕ) : ℝ) ≤ ((a' : ℕ) : ℝ) := by exact_mod_cast ha'
      have hcast1 : ((a' + 1 : ℕ) : ℝ) = ((a' : ℕ) : ℝ) + 1 := by norm_cast
      have hcast2 : ((m + 1 : ℕ) : ℝ) = ((m : ℕ) : ℝ) + 1 := by norm_cast
      linarith [hm]
    have tendsto_sub_nat_atBot : ∀ (a : ℝ), Tendsto (fun i : ℕ => a - ((i + 1 : ℕ) : ℝ)) atTop atBot := by
      intro a
      rw [tendsto_atTop_atBot]
      intro b
      obtain ⟨m, hm⟩ := exists_nat_ge (a - b)
      refine ⟨m, fun a' ha' => ?_⟩
      have hle : ((m : ℕ) : ℝ) ≤ ((a' : ℕ) : ℝ) := by exact_mod_cast ha'
      have hcast1 : ((a' + 1 : ℕ) : ℝ) = ((a' : ℕ) : ℝ) + 1 := by norm_cast
      have hcast2 : ((m + 1 : ℕ) : ℝ) = ((m : ℕ) : ℝ) + 1 := by norm_cast
      linarith [hm]
    have smul_eq_div : ∀ (z X : ℝ), (1 / X) • z = z / X := by
      intro z X
      rw [show ∀ r z : ℝ, r • z = r * z from fun _ _ => rfl, div_eq_mul_inv, div_eq_mul_inv,
        one_mul, mul_comm]
    have neg_smul_key : ∀ (z X : ℝ), z / X = -((-1 / X) • z) := by
      intro z X
      rw [show ∀ r z : ℝ, r • z = r * z from fun _ _ => rfl, neg_div, neg_mul, neg_neg,
        div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
    have norm_eq_div : ∀ {z X : ℝ} (hX : 0 < X), ‖z / X‖ = ‖z‖ / X := by
      intro z X
      intro hX
      rw [norm_div]
      simp only [Real.norm_eq_abs, abs_of_pos hX]
    have hasDerivAt_phi : ∀ (a t : ℝ) (ht : t < 1), HasDerivAt (fun u : ℝ => a + u / (1 - u)) (1 / (1 - t) ^ 2) t := by
      intro a t
      intro ht
      have hne : 1 - t ≠ 0 := by linarith
      have hden : HasDerivAt (fun u : ℝ => 1 - u) (0 - 1) t :=
        (hasDerivAt_const t 1).sub (hasDerivAt_id t)
      have hq : HasDerivAt (fun u : ℝ => u / (1 - u)) (1 / (1 - t) ^ 2) t := by
        have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
        have h := hid.fun_div hden hne
        rw [show (1 * (1 - t) - t * (0 - 1)) = 1 by ring] at h
        exact h
      exact hq.const_add a
    have hasDerivAt_psi : ∀ (a t : ℝ) (ht : t < 1), HasDerivAt (fun u : ℝ => a - u / (1 - u)) (-1 / (1 - t) ^ 2) t := by
      intro a t
      intro ht
      have hne : 1 - t ≠ 0 := by linarith
      have hden : HasDerivAt (fun u : ℝ => 1 - u) (0 - 1) t :=
        (hasDerivAt_const t 1).sub (hasDerivAt_id t)
      have hq : HasDerivAt (fun u : ℝ => u / (1 - u)) (1 / (1 - t) ^ 2) t := by
        have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
        have h := hid.fun_div hden hne
        rw [show (1 * (1 - t) - t * (0 - 1)) = 1 by ring] at h
        exact h
      have h := hq.const_sub a
      rw [← neg_div] at h
      exact h
    have continuousOn_phi : ∀ (a T : ℝ) (hT1 : T < 1), ContinuousOn (fun u : ℝ => a + u / (1 - u)) (Set.Icc 0 T) := by
      intro a T
      intro hT1
      refine continuousOn_of_forall_continuousAt fun x hx => ?_
      exact (hasDerivAt_phi a x (by linarith [hx.2, hT1])).continuousAt
    have continuousOn_psi : ∀ (a T : ℝ) (hT1 : T < 1), ContinuousOn (fun u : ℝ => a - u / (1 - u)) (Set.Icc 0 T) := by
      intro a T
      intro hT1
      refine continuousOn_of_forall_continuousAt fun x hx => ?_
      exact (hasDerivAt_psi a x (by linarith [hx.2, hT1])).continuousAt
    have nonneg_inv_sq : ∀ {t : ℝ} (ht : t < 1), 0 ≤ 1 / (1 - t) ^ 2 := by
      intro t
      intro ht
      have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith)
      exact div_nonneg (by norm_num) hpos.le
    have nonpos_neg_inv_sq : ∀ {t : ℝ} (ht : t < 1), -1 / (1 - t) ^ 2 ≤ 0 := by
      intro t
      intro ht
      have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith)
      exact div_nonpos_iff.mpr (Or.inr ⟨by norm_num, hpos.le⟩)
    have rkey : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, f (a + t / (1 - t)) / (1 - t) ^ 2
      = ∫ x in Set.Icc a (a + T / (1 - T)), f x := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          f (a + t / (1 - t)) / (1 - t) ^ 2 = (1 / (1 - t) ^ 2) • f (a + t / (1 - t)) :=
        fun t _ => (smul_eq_div (f (a + t / (1 - t))) ((1 - t) ^ 2)).symm
      have hL : ∫ t in Set.Icc 0 T, f (a + t / (1 - t)) / (1 - t) ^ 2
          = ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • f (a + t / (1 - t)) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • f (a + t / (1 - t))
          = ∫ x in Set.Icc (a + 0 / (1 - 0)) (a + T / (1 - T)), f x :=
        integral_Icc_deriv_smul_of_deriv_nonneg (f := fun u : ℝ => a + u / (1 - u))
          (f' := fun t : ℝ => 1 / (1 - t) ^ 2) (g := f)
          (continuousOn_phi a T hT1) (fun x hx => hasDerivAt_phi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonneg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, add_zero] at hR
      exact hL.trans hR
    have rkey_norm : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖
      = ∫ x in Set.Icc a (a + T / (1 - T)), ‖f x‖ := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖ = (1 / (1 - t) ^ 2) • ‖f (a + t / (1 - t))‖ := by
        intro t ht
        have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith [ht.2, hT1])
        rw [norm_eq_div hpos]
        exact (smul_eq_div _ _).symm
      have hL : ∫ t in Set.Icc 0 T, ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖
          = ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • ‖f (a + t / (1 - t))‖ :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (1 / (1 - t) ^ 2) • ‖f (a + t / (1 - t))‖
          = ∫ x in Set.Icc (a + 0 / (1 - 0)) (a + T / (1 - T)), ‖f x‖ :=
        integral_Icc_deriv_smul_of_deriv_nonneg (f := fun u : ℝ => a + u / (1 - u))
          (f' := fun t : ℝ => 1 / (1 - t) ^ 2) (g := fun x => ‖f x‖)
          (continuousOn_phi a T hT1) (fun x hx => hasDerivAt_phi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonneg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, add_zero] at hR
      exact hL.trans hR
    have rkey_integrable : ∀ {f : ℝ → ℝ} {a : ℝ} {i : ℕ}, IntegrableOn f (Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)))
      ↔ IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) := by
      intro f
      intro a
      intro i
      have hsig : σ i / (1 - σ i) = ((i + 1 : ℕ) : ℝ) := σ_frac i
      have hT1 : σ i < 1 := σ_lt_one i
      have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
      have hiff :
          IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a + t / (1 - t))) (Set.Icc 0 (σ i))
            ↔ IntegrableOn f (Set.Icc a (a + ((i + 1 : ℕ) : ℝ))) := by
        have h0 := integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg
          (f := fun u : ℝ => a + u / (1 - u)) (f' := fun t : ℝ => 1 / (1 - t) ^ 2) (g := f)
          (continuousOn_phi a (σ i) hT1) (fun x hx => hasDerivAt_phi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonneg_inv_sq (by linarith [hx.2, hT1])) hT0
        simpa only [zero_div, add_zero, hsig] using h0
      have h1 : IntegrableOn f (Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)))
          ↔ IntegrableOn f (Set.Icc a (a + ((i + 1 : ℕ) : ℝ))) :=
        (integrableOn_Icc_iff_integrableOn_Ioc (f := f) (a := a)
          (b := a + ((i + 1 : ℕ) : ℝ))).symm
      have h2 : IntegrableOn f (Set.Icc a (a + ((i + 1 : ℕ) : ℝ)))
          ↔ IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a + t / (1 - t))) (Set.Icc 0 (σ i)) :=
        hiff.symm
      have h3 : IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a + t / (1 - t)))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i)) :=
        integrableOn_congr_fun
          (fun t _ => smul_eq_div (f (a + t / (1 - t))) ((1 - t) ^ 2)) measurableSet_Icc
      have h4 : IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) :=
        integrableOn_Icc_iff_integrableOn_Ioc
      exact h1.trans h2 |>.trans h3 |>.trans h4
    have lkey : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, f (a - t / (1 - t)) / (1 - t) ^ 2
      = ∫ x in Set.Icc (a - T / (1 - T)) a, f x := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          f (a - t / (1 - t)) / (1 - t) ^ 2 = -((-1 / (1 - t) ^ 2) • f (a - t / (1 - t))) :=
        fun t _ => neg_smul_key (f (a - t / (1 - t))) ((1 - t) ^ 2)
      have hL : ∫ t in Set.Icc 0 T, f (a - t / (1 - t)) / (1 - t) ^ 2
          = ∫ t in Set.Icc 0 T, -((-1 / (1 - t) ^ 2) • f (a - t / (1 - t))) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (-1 / (1 - t) ^ 2) • f (a - t / (1 - t))
          = -∫ x in Set.Icc (a - T / (1 - T)) (a - 0 / (1 - 0)), f x :=
        integral_Icc_deriv_smul_of_deriv_nonpos (f := fun u : ℝ => a - u / (1 - u))
          (f' := fun t : ℝ => -1 / (1 - t) ^ 2) (g := f)
          (continuousOn_psi a T hT1) (fun x hx => hasDerivAt_psi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonpos_neg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, sub_zero] at hR
      rw [hL, MeasureTheory.integral_neg, hR, neg_neg]
    have lkey_norm : ∀ {f : ℝ → ℝ} {a T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1), ∫ t in Set.Icc 0 T, ‖f (a - t / (1 - t)) / (1 - t) ^ 2‖
      = ∫ x in Set.Icc (a - T / (1 - T)) a, ‖f x‖ := by
      intro f
      intro a T
      intro hT0
      intro hT1
      have hpoint : ∀ t ∈ Set.Icc 0 T,
          ‖f (a - t / (1 - t)) / (1 - t) ^ 2‖
            = -((-1 / (1 - t) ^ 2) • ‖f (a - t / (1 - t))‖) := by
        intro t ht
        have hpos : 0 < (1 - t) ^ 2 := sq_pos_of_ne_zero (by linarith [ht.2, hT1])
        rw [norm_eq_div hpos]
        exact neg_smul_key _ _
      have hL : ∫ t in Set.Icc 0 T, ‖f (a - t / (1 - t)) / (1 - t) ^ 2‖
          = ∫ t in Set.Icc 0 T, -((-1 / (1 - t) ^ 2) • ‖f (a - t / (1 - t))‖) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpoint
      have hR : ∫ t in Set.Icc 0 T, (-1 / (1 - t) ^ 2) • ‖f (a - t / (1 - t))‖
          = -∫ x in Set.Icc (a - T / (1 - T)) (a - 0 / (1 - 0)), ‖f x‖ :=
        integral_Icc_deriv_smul_of_deriv_nonpos (f := fun u : ℝ => a - u / (1 - u))
          (f' := fun t : ℝ => -1 / (1 - t) ^ 2) (g := fun x => ‖f x‖)
          (continuousOn_psi a T hT1) (fun x hx => hasDerivAt_psi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonpos_neg_inv_sq (by linarith [hx.2, hT1])) hT0
      simp only [zero_div, sub_zero] at hR
      rw [hL, MeasureTheory.integral_neg, hR, neg_neg]
    have lkey_integrable : ∀ {f : ℝ → ℝ} {a : ℝ} {i : ℕ}, IntegrableOn f (Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a)
      ↔ IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) := by
      intro f
      intro a
      intro i
      have hsig : σ i / (1 - σ i) = ((i + 1 : ℕ) : ℝ) := σ_frac i
      have hT1 : σ i < 1 := σ_lt_one i
      have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
      have hiff :
          IntegrableOn (fun t : ℝ => (-1 / (1 - t) ^ 2) • f (a - t / (1 - t))) (Set.Icc 0 (σ i))
            ↔ IntegrableOn f (Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a) := by
        have h0 := integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos
          (f := fun u : ℝ => a - u / (1 - u)) (f' := fun t : ℝ => -1 / (1 - t) ^ 2) (g := f)
          (continuousOn_psi a (σ i) hT1) (fun x hx => hasDerivAt_psi a x (by linarith [hx.2, hT1]))
          (fun x hx => nonpos_neg_inv_sq (by linarith [hx.2, hT1])) hT0
        simpa only [zero_div, sub_zero, hsig] using h0
      have h1 : IntegrableOn f (Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a)
          ↔ IntegrableOn f (Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a) :=
        (integrableOn_Icc_iff_integrableOn_Ioc (f := f)
          (a := a - ((i + 1 : ℕ) : ℝ)) (b := a)).symm
      have h2 : IntegrableOn f (Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a)
          ↔ IntegrableOn (fun t : ℝ => (-1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
              (Set.Icc 0 (σ i)) :=
        hiff.symm
      have h3 : IntegrableOn (fun t : ℝ => (-1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => -((1 / (1 - t) ^ 2) • f (a - t / (1 - t))))
              (Set.Icc 0 (σ i)) :=
        integrableOn_congr_fun (fun t _ => by rw [neg_div, neg_smul]) measurableSet_Icc
      have h3b : IntegrableOn (fun t : ℝ => -((1 / (1 - t) ^ 2) • f (a - t / (1 - t))))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
              (Set.Icc 0 (σ i)) :=
        integrableOn_neg_iff
      have h3c : IntegrableOn (fun t : ℝ => (1 / (1 - t) ^ 2) • f (a - t / (1 - t)))
            (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i)) :=
        integrableOn_congr_fun
          (fun t _ => smul_eq_div (f (a - t / (1 - t))) ((1 - t) ^ 2)) measurableSet_Icc
      have h4 : IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Icc 0 (σ i))
          ↔ IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) :=
        integrableOn_Icc_iff_integrableOn_Ioc
      exact h1.trans h2 |>.trans h3 |>.trans h3b |>.trans h3c |>.trans h4
    have tendsto_sigma_integral : ∀ (g : ℝ → ℝ) (hint : IntervalIntegrable g volume 0 1), Tendsto (fun i : ℕ => ∫ t in (0:ℝ)..σ i, g t) atTop (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
      intro g
      intro hint
      have hmono : Monotone (fun i : ℕ => Set.Ioo 0 (σ i)) := by
        intro i j hij x hx
        exact Set.mem_Ioo.2 ⟨hx.1, lt_of_lt_of_le hx.2 (σ_monotone hij)⟩
      have hunion : (⋃ n : ℕ, Set.Ioo 0 (σ n)) = Set.Ioo 0 1 := by
        apply Set.Subset.antisymm
        · refine Set.iUnion_subset fun n x hx => ?_
          exact Set.mem_Ioo.2 ⟨hx.1, (hx.2).trans (σ_lt_one n)⟩
        · intro x hx
          obtain ⟨N, hN⟩ : ∃ N : ℕ, x < σ N := by
            have h1x : 0 < 1 - x := by linarith [hx.2]
            obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - x))
            have hne : ((N + 2 : ℕ) : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.succ_ne_zero (N + 1))
            refine ⟨N, ?_⟩
            have h1 : (1:ℝ) / (1 - x) < ((N + 2 : ℕ) : ℝ) :=
              lt_of_lt_of_le hN (by exact_mod_cast Nat.le_add_right N 2)
            have h2 : (1:ℝ) < ((N + 2 : ℕ) : ℝ) * (1 - x) := (div_lt_iff₀ h1x).mp h1
            rw [mul_comm] at h2
            have h3 : (1:ℝ) / ((N + 2 : ℕ) : ℝ) < 1 - x :=
              (div_lt_iff₀ (by positivity)).mpr (by linarith)
            simp only [σ]
            linarith
          exact Set.mem_iUnion.2 ⟨N, Set.mem_Ioo.2 ⟨hx.1, hN⟩⟩
      have hfiU : IntegrableOn g (⋃ n, Set.Ioo 0 (σ n)) := by
        rw [hunion]
        have h1 : IntegrableOn g (Set.Ioc 0 1) :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp hint
        exact h1.mono_set Set.Ioo_subset_Ioc_self
      have h := MeasureTheory.tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioo) hmono hfiU
      rw [hunion] at h
      have heq : ∫ x in Set.Ioo 0 1, g x = ∫ t in (0:ℝ)..1, g t :=
        MeasureTheory.integral_Ioc_eq_integral_Ioo.symm.trans
          (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm
      rw [heq] at h
      have hpt : ∀ i : ℕ, ∫ t in (0:ℝ)..σ i, g t = ∫ x in Set.Ioo 0 (σ i), g x := fun i =>
        (intervalIntegral.integral_of_le (σ_nonneg i)).trans
          MeasureTheory.integral_Ioc_eq_integral_Ioo
      exact Tendsto.congr (fun i => (hpt i).symm) h
    have r_iff_fwd : ∀ {f : ℝ → ℝ} {a : ℝ} (hi : IntegrableOn f (Set.Ioi a)), IntervalIntegrable (fun t => f (a+t/(1-t))/(1-t)^2) volume 0 1 := by
      intro f
      intro a
      intro hi
      have hsub : ∀ i : ℕ, Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)) ⊆ Set.Ioi a :=
        fun i _ hx => hx.1
      have hfi : ∀ i : ℕ,
          IntegrableOn (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) := by
        intro i
        exact (rkey_integrable (f := f) (a := a) (i := i)).mp (hi.mono_set (hsub i))
      have hbound : ∀ i : ℕ,
          ∫ x in Set.Ioc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖
            ≤ ∫ x in Set.Ioi a, ‖f x‖ := by
        intro i
        have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
        have hT1 : σ i < 1 := σ_lt_one i
        have hn : IntegrableOn (fun x : ℝ => ‖f x‖) (Set.Ioi a) :=
          (show Integrable f (volume.restrict _) from hi).norm
        calc ∫ x in Set.Ioc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖
            = ∫ x in Set.Icc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc.symm
          _ = ∫ x in Set.Icc a (a + σ i / (1 - σ i)), ‖f x‖ := rkey_norm hT0 hT1
          _ = ∫ x in Set.Icc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ := by rw [σ_frac i]
          _ = ∫ x in Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc
          _ ≤ ∫ x in Set.Ioi a, ‖f x‖ :=
                MeasureTheory.setIntegral_mono_set hn (ae_of_all _ (fun _ => norm_nonneg _))
                  ((hsub i).eventuallySubset)
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr ?_
      exact MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
        (I := ∫ x in Set.Ioi a, ‖f x‖) (b := σ) hfi σ_tendsto
        (Filter.Eventually.of_forall hbound)
    have r_iff_rev : ∀ {f : ℝ → ℝ} {a : ℝ} (hi : IntervalIntegrable (fun t => f (a+t/(1-t))/(1-t)^2) volume 0 1), IntegrableOn f (Set.Ioi a) := by
      intro f
      intro a
      intro hi
      have hfi0 : IntegrableOn
          (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 1) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp hi
      have hsub : ∀ i : ℕ, Set.Ioc 0 (σ i) ⊆ Set.Ioc 0 1 :=
        fun i => Set.Ioc_subset_Ioc le_rfl (le_of_lt (σ_lt_one i))
      have hfi : ∀ i : ℕ, IntegrableOn f (Set.Ioc a (a + ((i + 1 : ℕ) : ℝ))) := by
        intro i
        exact (rkey_integrable (f := f) (a := a) (i := i)).mpr (hfi0.mono_set (hsub i))
      have hbound : ∀ i : ℕ,
          ∫ x in a..(a + ((i + 1 : ℕ) : ℝ)), ‖f x‖
            ≤ ∫ x in Set.Ioc 0 1, ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ := by
        intro i
        have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
        have hT1 : σ i < 1 := σ_lt_one i
        have hn : IntegrableOn
            (fun x : ℝ => ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖) (Set.Ioc 0 1) :=
          (show Integrable (fun t : ℝ => f (a + t / (1 - t)) / (1 - t) ^ 2)
            (volume.restrict _) from hfi0).norm
        have hge : (0:ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
        calc ∫ x in a..(a + ((i + 1 : ℕ) : ℝ)), ‖f x‖
            = ∫ x in Set.Ioc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ :=
                intervalIntegral.integral_of_le (by linarith)
          _ = ∫ x in Set.Icc a (a + ((i + 1 : ℕ) : ℝ)), ‖f x‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc.symm
          _ = ∫ x in Set.Icc a (a + σ i / (1 - σ i)), ‖f x‖ := by rw [← σ_frac i]
          _ = ∫ t in Set.Icc 0 (σ i), ‖f (a + t / (1 - t)) / (1 - t) ^ 2‖ :=
                (rkey_norm hT0 hT1).symm
          _ = ∫ x in Set.Ioc 0 (σ i), ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc
          _ ≤ ∫ x in Set.Ioc 0 1, ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.setIntegral_mono_set hn (ae_of_all _ (fun _ => norm_nonneg _))
                  ((hsub i).eventuallySubset)
      exact MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded
        (I := ∫ x in Set.Ioc 0 1, ‖f (a + x / (1 - x)) / (1 - x) ^ 2‖) (a := a) hfi
        (tendsto_add_nat_atTop a) (Filter.Eventually.of_forall hbound)
    have l_iff_fwd : ∀ {f : ℝ → ℝ} {a : ℝ} (hi : IntegrableOn f (Set.Iio a)), IntervalIntegrable (fun t => f (a-t/(1-t))/(1-t)^2) volume 0 1 := by
      intro f
      intro a
      intro hi
      have hsub : ∀ i : ℕ, Set.Ioo (a - ((i + 1 : ℕ) : ℝ)) a ⊆ Set.Iio a :=
        fun i => Set.Ioo_subset_Iio_self
      have hfi : ∀ i : ℕ,
          IntegrableOn (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 (σ i)) := by
        intro i
        exact (lkey_integrable (f := f) (a := a) (i := i)).mp
          ((integrableOn_Ioc_iff_integrableOn_Ioo).mpr (hi.mono_set (hsub i)))
      have hbound : ∀ i : ℕ,
          ∫ x in Set.Ioc 0 (σ i), ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖
            ≤ ∫ x in Set.Iio a, ‖f x‖ := by
        intro i
        have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
        have hT1 : σ i < 1 := σ_lt_one i
        have hn : IntegrableOn (fun x : ℝ => ‖f x‖) (Set.Iio a) :=
          (show Integrable f (volume.restrict _) from hi).norm
        have hsub2 : ∀ i : ℕ, Set.Ico (a - ((i + 1 : ℕ) : ℝ)) a ⊆ Set.Iio a :=
          fun i => Set.Ico_subset_Iio_self
        calc ∫ x in Set.Ioc 0 (σ i), ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖
            = ∫ x in Set.Icc 0 (σ i), ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc.symm
          _ = ∫ x in Set.Icc (a - σ i / (1 - σ i)) a, ‖f x‖ := lkey_norm hT0 hT1
          _ = ∫ x in Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a, ‖f x‖ := by rw [← σ_frac i]
          _ = ∫ x in Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a, ‖f x‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc
          _ = ∫ x in Set.Ico (a - ((i + 1 : ℕ) : ℝ)) a, ‖f x‖ := by
                rw [MeasureTheory.integral_Ico_eq_integral_Ioo,
                  MeasureTheory.integral_Ioc_eq_integral_Ioo]
          _ ≤ ∫ x in Set.Iio a, ‖f x‖ :=
                MeasureTheory.setIntegral_mono_set hn (ae_of_all _ (fun _ => norm_nonneg _))
                  ((hsub2 i).eventuallySubset)
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr ?_
      exact MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
        (I := ∫ x in Set.Iio a, ‖f x‖) (b := σ) hfi σ_tendsto
        (Filter.Eventually.of_forall hbound)
    have l_iff_rev : ∀ {f : ℝ → ℝ} {a : ℝ} (hi : IntervalIntegrable (fun t => f (a-t/(1-t))/(1-t)^2) volume 0 1), IntegrableOn f (Set.Iio a) := by
      intro f
      intro a
      intro hi
      have hfi0 : IntegrableOn
          (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2) (Set.Ioc 0 1) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp hi
      have hsub : ∀ i : ℕ, Set.Ioc 0 (σ i) ⊆ Set.Ioc 0 1 :=
        fun i => Set.Ioc_subset_Ioc le_rfl (le_of_lt (σ_lt_one i))
      have hfi : ∀ i : ℕ, IntegrableOn f (Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a) := by
        intro i
        exact (lkey_integrable (f := f) (a := a) (i := i)).mpr (hfi0.mono_set (hsub i))
      have hbound : ∀ i : ℕ,
          ∫ x in (a - ((i + 1 : ℕ) : ℝ))..a, ‖f x‖
            ≤ ∫ x in Set.Ioc 0 1, ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖ := by
        intro i
        have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
        have hT1 : σ i < 1 := σ_lt_one i
        have hn : IntegrableOn
            (fun x : ℝ => ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖) (Set.Ioc 0 1) :=
          (show Integrable (fun t : ℝ => f (a - t / (1 - t)) / (1 - t) ^ 2)
            (volume.restrict _) from hfi0).norm
        have hge : (0:ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
        calc ∫ x in (a - ((i + 1 : ℕ) : ℝ))..a, ‖f x‖
            = ∫ x in Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a, ‖f x‖ :=
                intervalIntegral.integral_of_le (by linarith)
          _ = ∫ x in Set.Ico (a - ((i + 1 : ℕ) : ℝ)) a, ‖f x‖ := by
                rw [MeasureTheory.integral_Ico_eq_integral_Ioo,
                  MeasureTheory.integral_Ioc_eq_integral_Ioo]
          _ = ∫ x in Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a, ‖f x‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ico.symm
          _ = ∫ x in Set.Icc (a - σ i / (1 - σ i)) a, ‖f x‖ := by rw [← σ_frac i]
          _ = ∫ t in Set.Icc 0 (σ i), ‖f (a - t / (1 - t)) / (1 - t) ^ 2‖ :=
                (lkey_norm hT0 hT1).symm
          _ = ∫ x in Set.Ioc 0 (σ i), ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.integral_Icc_eq_integral_Ioc
          _ ≤ ∫ x in Set.Ioc 0 1, ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖ :=
                MeasureTheory.setIntegral_mono_set hn (ae_of_all _ (fun _ => norm_nonneg _))
                  ((hsub i).eventuallySubset)
      have hIic : IntegrableOn f (Set.Iic a) :=
        MeasureTheory.integrableOn_Iic_of_intervalIntegral_norm_bounded
          (I := ∫ x in Set.Ioc 0 1, ‖f (a - x / (1 - x)) / (1 - x) ^ 2‖)
          (a := fun i : ℕ => a - ((i + 1 : ℕ) : ℝ)) (b := a) hfi (tendsto_sub_nat_atBot a)
          (Filter.Eventually.of_forall hbound)
      have hAE : Set.Iio a =ᵐ[volume] Set.Iic a := Iio_ae_eq_Iic
      exact hIic.congr_set_ae hAE
    have hpieces : ∀ i : ℕ,
        ∫ x in (a - ((i + 1 : ℕ) : ℝ))..a, f x
          = ∫ t in (0:ℝ)..σ i, f (a - t / (1 - t)) / (1 - t) ^ 2 := by
      intro i
      have hT0 : (0:ℝ) ≤ σ i := σ_nonneg i
      have hT1 : σ i < 1 := σ_lt_one i
      have hge : (0:ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
      have hend : Set.Icc (a - σ i / (1 - σ i)) a
          = Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a := by
        rw [σ_frac i]
      calc ∫ x in (a - ((i + 1 : ℕ) : ℝ))..a, f x
          = ∫ x in Set.Ioc (a - ((i + 1 : ℕ) : ℝ)) a, f x :=
              intervalIntegral.integral_of_le (by linarith)
        _ = ∫ x in Set.Icc (a - ((i + 1 : ℕ) : ℝ)) a, f x :=
              MeasureTheory.integral_Icc_eq_integral_Ioc.symm
        _ = ∫ x in Set.Icc (a - σ i / (1 - σ i)) a, f x := by rw [← hend]
        _ = ∫ t in Set.Icc 0 (σ i), f (a - t / (1 - t)) / (1 - t) ^ 2 := (lkey hT0 hT1).symm
        _ = ∫ t in Set.Ioc 0 (σ i), f (a - t / (1 - t)) / (1 - t) ^ 2 :=
              MeasureTheory.integral_Icc_eq_integral_Ioc
        _ = ∫ t in (0:ℝ)..σ i, f (a - t / (1 - t)) / (1 - t) ^ 2 :=
              (intervalIntegral.integral_of_le hT0).symm
    have hchain : ∀ i : ℕ,
        ∫ x in (a - ((i + 1 : ℕ) : ℝ))..a, f x
          = ∫ x in Set.Ico (a - ((i + 1 : ℕ) : ℝ)) a, f x := fun i =>
      (intervalIntegral.integral_of_le (by
        have hge : (0:ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
        linarith :
        a - ((i + 1 : ℕ) : ℝ) ≤ a)).trans
        (MeasureTheory.integral_Ioc_eq_integral_Ioo.trans
          MeasureTheory.integral_Ico_eq_integral_Ioo.symm)
    have hL : Tendsto (fun i : ℕ => ∫ x in (a - ((i + 1 : ℕ) : ℝ))..a, f x) atTop
        (𝓝 (∫ x in Set.Iio a, f x)) :=
      Tendsto.congr (fun i => (hchain i).symm)
        (MeasureTheory.tendsto_integral_Ico_integral_Iio a hi (tendsto_sub_nat_atBot a))
    have hR : Tendsto (fun i : ℕ => ∫ t in (0:ℝ)..σ i, f (a - t / (1 - t)) / (1 - t) ^ 2) atTop
        (𝓝 (∫ t in (0:ℝ)..1, f (a - t / (1 - t)) / (1 - t) ^ 2)) :=
      tendsto_sigma_integral _ (l_iff_fwd hi)
    refine tendsto_nhds_unique hL ?_
    exact Tendsto.congr' (Filter.Eventually.of_forall fun i => (hpieces i).symm) hR

theorem exp_decay_power {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Real.exp (-s) ≤ (n.factorial : ℝ)/s^n := by
  have hl : (s:ℝ)^n / (n.factorial:ℝ) ≤ Real.exp s :=
    Real.pow_div_factorial_le_exp s hs.le n
  have h2 : (Real.exp s)⁻¹ ≤ ((s:ℝ)^n / (n.factorial:ℝ))⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr hl
  have hid : ((s:ℝ)^n / (n.factorial:ℝ))⁻¹ = (n.factorial:ℝ)/s^n := inv_div _ _
  rw [Real.exp_neg s, ← hid]
  exact h2

/-- Exact power/log moment used for endpoint truncation. -/
theorem power_log_moment {p δ : ℝ} (hp : -1 < p) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (m : ℕ) :
    IntegrableOn (fun t : ℝ => t^p*(1-Real.log t)^m) (Set.Ioc 0 δ) ∧
    (∫ t in (0 : ℝ)..δ, t^p*(1-Real.log t)^m) =
      δ^(p+1) * ∑ j ∈ Finset.range (m+1),
        ((m.factorial : ℝ)/j.factorial/(p+1)^(m-j+1))*(1-Real.log δ)^j := by
  let momentCoeff (m : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
    (m.factorial : ℝ) / j.factorial / (p + 1) ^ (m - j + 1)
  let momentAnti (m : ℕ) (p : ℝ) (t : ℝ) : ℝ :=
    ∑ j ∈ Finset.range (m + 1), momentCoeff m p j * (t ^ (p + 1) * (1 - Real.log t) ^ j)
  let momentIntegrand (m : ℕ) (p : ℝ) (t : ℝ) : ℝ :=
    t ^ p * (1 - Real.log t) ^ m
  have momentCoeff_id (m j : ℕ) (p : ℝ) (hp : -1 < p) (hjm : j < m) :
    (p + 1) * momentCoeff m p j = ((j + 1 : ℕ) : ℝ) * momentCoeff m p (j + 1)  := by
    have hex : m - (j + 1) + 1 = m - j := by omega
    have hp1 : p + 1 ≠ 0 := by linarith
    have hfac : (j + 1).factorial = (j + 1) * j.factorial := by
      rw [Nat.factorial_succ]
    simp only [momentCoeff]
    rw [hex, hfac]
    push_cast
    rw [pow_succ]
    have hpow : (p + 1) ^ (m - j) ≠ 0 := pow_ne_zero _ hp1
    field_simp [hpow]
  have momentAnti_hasDeriv (m : ℕ) (p : ℝ) (hp : -1 < p) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (momentAnti m p) (momentIntegrand m p t) t  := by
    have hterm : ∀ j ∈ Finset.range (m + 1),
        HasDerivAt (fun x : ℝ => momentCoeff m p j * (x ^ (p + 1) * (1 - Real.log x) ^ j))
          (momentCoeff m p j * ((p + 1) * t ^ p * (1 - Real.log t) ^ j
            - t ^ p * ((j : ℕ) : ℝ) * (1 - Real.log t) ^ (j - 1))) t := by
      intro j hj
      have hpow : HasDerivAt (fun x : ℝ => x ^ (p + 1)) ((p + 1) * t ^ p) t := by
        have h := Real.hasDerivAt_rpow_const (x := t) (p := p + 1) (Or.inl ht.ne')
        have he : p + 1 - 1 = p := by ring
        rwa [he] at h
      have hlog : HasDerivAt (fun x : ℝ => (1 - Real.log x) ^ j)
          (-((j : ℕ) : ℝ) * (1 - Real.log t) ^ (j - 1) / t) t := by
        have h0 : HasDerivAt (fun x : ℝ => 1 - Real.log x) (-t⁻¹) t :=
          (Real.hasDerivAt_log ht.ne').const_sub 1
        have h1 := h0.pow j
        have hv : (j : ℝ) * (1 - Real.log t) ^ (j - 1) * -t⁻¹
            = -((j : ℕ) : ℝ) * (1 - Real.log t) ^ (j - 1) / t := by
          rw [div_eq_mul_inv]
          ring
        exact h1.congr_deriv hv
      have hmul := hpow.mul hlog
      have hcmul := hmul.const_mul (momentCoeff m p j)
      have hpow2 : t ^ (p + 1) * t⁻¹ = t ^ p := by
        rw [← Real.rpow_neg_one t, ← Real.rpow_add ht]
        congr 1
        ring
      have hv2 : momentCoeff m p j * ((p + 1) * t ^ p * (1 - Real.log t) ^ j
            + t ^ (p + 1) * (-((j : ℕ) : ℝ) * (1 - Real.log t) ^ (j - 1) / t))
          = momentCoeff m p j * ((p + 1) * t ^ p * (1 - Real.log t) ^ j
            - t ^ p * ((j : ℕ) : ℝ) * (1 - Real.log t) ^ (j - 1)) := by
        have hstep : t ^ (p + 1) * (-((j : ℕ) : ℝ) * (1 - Real.log t) ^ (j - 1) / t)
            = -(t ^ p * ((j : ℕ) : ℝ) * (1 - Real.log t) ^ (j - 1)) := by
          rw [div_eq_mul_inv]
          have hrewrite :
              t ^ (p + 1) * (-((j : ℕ) : ℝ) * (1 - Real.log t) ^ (j - 1) * t⁻¹)
              = -(t ^ (p + 1) * t⁻¹) * (((j : ℕ) : ℝ) * (1 - Real.log t) ^ (j - 1)) := by
            ring
          rw [hrewrite, ← hpow2]
          ring
        rw [hstep]
        ring
      exact hcmul.congr_deriv hv2
    have hsum := HasDerivAt.sum (fun j hj => hterm j hj)
    have hkey : ∑ j ∈ Finset.range (m + 1),
          momentCoeff m p j * ((p + 1) * t ^ p * (1 - Real.log t) ^ j
            - t ^ p * ((j : ℕ) : ℝ) * (1 - Real.log t) ^ (j - 1))
        = t ^ p * (1 - Real.log t) ^ m := by
      have hsplit : ∀ j ∈ Finset.range (m + 1),
          momentCoeff m p j * ((p + 1) * t ^ p * (1 - Real.log t) ^ j
            - t ^ p * ((j : ℕ) : ℝ) * (1 - Real.log t) ^ (j - 1))
          = (p + 1) * t ^ p * (momentCoeff m p j * (1 - Real.log t) ^ j)
            - t ^ p * (momentCoeff m p j * ((j : ℕ) : ℝ) * (1 - Real.log t) ^ (j - 1)) := by
        intro j _
        ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
      have hS2 : ∑ j ∈ Finset.range (m + 1),
          t ^ p * (momentCoeff m p j * ((j : ℕ) : ℝ) * (1 - Real.log t) ^ (j - 1))
          = t ^ p * ∑ j ∈ Finset.range m,
              (momentCoeff m p (j + 1) * (((j + 1 : ℕ)) : ℝ) * (1 - Real.log t) ^ j) := by
        rw [Finset.mul_sum, Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
      have hS1 : ∑ j ∈ Finset.range (m + 1),
            (p + 1) * t ^ p * (momentCoeff m p j * (1 - Real.log t) ^ j)
          = (p + 1) * t ^ p * ∑ j ∈ Finset.range (m + 1),
              (momentCoeff m p j * (1 - Real.log t) ^ j) := by
        rw [Finset.mul_sum]
      rw [hS1, hS2]
      have hcoef : ∀ j ∈ Finset.range m,
          momentCoeff m p (j + 1) * (((j + 1 : ℕ)) : ℝ) = (p + 1) * momentCoeff m p j := by
        intro j hj
        exact (mul_comm (momentCoeff m p (j + 1)) (((j + 1 : ℕ)) : ℝ)).trans
          (momentCoeff_id m j p hp (Finset.mem_range.mp hj)).symm
      have hB : ∑ j ∈ Finset.range m,
            (momentCoeff m p (j + 1) * (((j + 1 : ℕ)) : ℝ) * (1 - Real.log t) ^ j)
          = (p + 1) * ∑ j ∈ Finset.range m, (momentCoeff m p j * (1 - Real.log t) ^ j) := by
        have hpoint : ∀ j ∈ Finset.range m,
            momentCoeff m p (j + 1) * (((j + 1 : ℕ)) : ℝ) * (1 - Real.log t) ^ j
              = (p + 1) * (momentCoeff m p j * (1 - Real.log t) ^ j) := by
          intro j hj
          rw [hcoef j hj, mul_assoc]
        rw [Finset.sum_congr rfl hpoint, ← Finset.mul_sum]
      rw [hB, Finset.sum_range_succ]
      have hm : momentCoeff m p m = (p + 1)⁻¹ := by
        simp only [momentCoeff]
        rw [Nat.sub_self, pow_one]
        have hfacne : (m.factorial : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.factorial_ne_zero m)
        have hp1 : p + 1 ≠ 0 := by linarith
        field_simp [hfacne, hp1]
      have hp1 : p + 1 ≠ 0 := by linarith
      rw [hm]
      field_simp [hp1]
      ring
    have hfun : momentAnti m p = ∑ i ∈ Finset.range (m + 1),
        fun x : ℝ => momentCoeff m p i * (x ^ (p + 1) * (1 - Real.log x) ^ i) := by
      funext x
      simp only [momentAnti, Finset.sum_apply]
    rw [hfun]
    exact hsum.congr_deriv hkey
  have tendsto_one_sub_log :
    Tendsto (fun ε : ℝ => 1 - Real.log ε) (𝓝[>] (0:ℝ)) atTop  := by
    have h1 : Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] (0:ℝ)) atTop :=
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    have h2 : Tendsto (fun ε : ℝ => 1 - Real.log ε) (𝓝[>] (0:ℝ)) atTop := by
      rw [tendsto_atTop]
      intro x
      have hge : ∀ᶠ ε in 𝓝[>] (0:ℝ), x - 1 ≤ -Real.log ε :=
        tendsto_atTop.mp h1 (x - 1)
      filter_upwards [hge] with ε hε
      show x ≤ 1 - Real.log ε
      linarith
    exact h2
  have momentTerm_tendsto_zero (p : ℝ) (hp : -1 < p) (j : ℕ) :
    Tendsto (fun ε : ℝ => ε ^ (p + 1) * (1 - Real.log ε) ^ j) (𝓝[>] (0:ℝ)) (𝓝 0)  := by
    set b : ℝ := (p + 1) / 2 with hbdef
    have hbpos : 0 < b := by linarith
    have hne : b ≠ 0 := hbpos.ne'
    have hat : Tendsto (fun x : ℝ => x ^ j * Real.exp (-b * x)) atTop (𝓝 0) := by
      refine Tendsto.congr' ?_ (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero j b hbpos)
      filter_upwards [Eventually.of_forall fun x => Real.rpow_natCast x j] with x hx
      rw [hx]
    have hcomp : Tendsto
        (fun ε : ℝ => (1 - Real.log ε) ^ j * Real.exp (-b * (1 - Real.log ε)))
        (𝓝[>] (0:ℝ)) (𝓝 0) := hat.comp tendsto_one_sub_log
    have hB : Tendsto
        (fun ε : ℝ => Real.exp b * ((1 - Real.log ε) ^ j
          * Real.exp (-b * (1 - Real.log ε)))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hcomp)
    have hA : Tendsto (fun ε : ℝ => ε ^ b) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hlog : Tendsto (fun ε : ℝ => b * Real.log ε) (𝓝[>] (0:ℝ)) atBot :=
        Tendsto.const_mul_atBot hbpos Real.tendsto_log_nhdsGT_zero
      have hexp : Tendsto (fun ε : ℝ => Real.exp (b * Real.log ε)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hlog
      refine Tendsto.congr' ?_ hexp
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hpos : 0 < ε := hε
      rw [mul_comm b (Real.log ε), Real.exp_mul, Real.exp_log hpos]
    have hstep : Tendsto (fun ε : ℝ => ε ^ b * (Real.exp b * ((1 - Real.log ε) ^ j
          * Real.exp (-b * (1 - Real.log ε))))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa using hA.mul hB
    refine Tendsto.congr' ?_ hstep
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hpos : 0 < ε := hε
    have hident : ε ^ b = Real.exp b * Real.exp (-b * (1 - Real.log ε)) := by
      have hrewrite : -b * (1 - Real.log ε) = -b + b * Real.log ε := by ring
      have h2 : Real.exp (b * Real.log ε) = ε ^ b := by
        rw [mul_comm b (Real.log ε), Real.exp_mul, Real.exp_log hpos]
      rw [hrewrite, ← Real.exp_add]
      have hsum : b + (-b + b * Real.log ε) = b * Real.log ε := by ring
      rw [hsum, h2]
    have hp2 : p + 1 = b + b := by rw [hbdef]; ring
    rw [hp2, Real.rpow_add hpos, hident]
    ring
  have momentAnti_tendsto_zero (m : ℕ) (p : ℝ) (hp : -1 < p) :
    Tendsto (momentAnti m p) (𝓝[>] (0:ℝ)) (𝓝 0)  := by
    have hterm : ∀ j ≤ m,
        Tendsto (fun ε : ℝ => momentCoeff m p j * (ε ^ (p + 1) * (1 - Real.log ε) ^ j))
          (𝓝[>] (0:ℝ)) (𝓝 0) := by
      intro j _
      simpa using (momentTerm_tendsto_zero p hp j).const_mul (momentCoeff m p j)
    have hsum : Tendsto
        (fun ε : ℝ => ∑ j ∈ Finset.range (m + 1),
          momentCoeff m p j * (ε ^ (p + 1) * (1 - Real.log ε) ^ j))
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hbound : ∀ j ∈ Finset.range (m + 1),
          Tendsto (fun ε : ℝ => momentCoeff m p j * (ε ^ (p + 1) * (1 - Real.log ε) ^ j))
            (𝓝[>] (0:ℝ)) (𝓝 0) := by
        intro j hj
        exact hterm j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      have h1 : Tendsto
          (fun ε : ℝ => ∑ j ∈ Finset.range (m + 1),
            momentCoeff m p j * (ε ^ (p + 1) * (1 - Real.log ε) ^ j))
          (𝓝[>] (0:ℝ)) (𝓝 (∑ _j ∈ Finset.range (m + 1), (0:ℝ))) :=
        tendsto_finsetSum _ hbound
      simpa [Finset.sum_const_zero] using h1
    have hfun : momentAnti m p = fun ε : ℝ => ∑ j ∈ Finset.range (m + 1),
        momentCoeff m p j * (ε ^ (p + 1) * (1 - Real.log ε) ^ j) := by
      funext ε
      simp only [momentAnti]
    rw [hfun]
    exact hsum

  have h01 : (0:ℝ) ≤ δ := hδ.le
  have hempty : Set.Ioc δ (0:ℝ) = ∅ := Set.Ioc_eq_empty_of_le h01
  have hcont : ContinuousOn (fun t : ℝ => t^p * (1 - Real.log t)^m) (Set.Ioi 0) := by
    intro t ht
    have hne : t ≠ 0 := ne_of_gt (Set.mem_Ioi.1 ht)
    have h1 : HasDerivAt (fun x : ℝ => x ^ p) _ t :=
      Real.hasDerivAt_rpow_const (x := t) (p := p) (Or.inl hne)
    have h2 : HasDerivAt (fun x : ℝ => (1 - Real.log x) ^ m) _ t :=
      ((Real.hasDerivAt_log hne).const_sub 1).pow m
    exact (h1.mul h2).continuousAt.continuousWithinAt
  have hI : IntegrableOn (fun t : ℝ => t^p*(1-Real.log t)^m) (Set.Ioc 0 δ) := by
    have hfi : ∀ i : ℝ, IntegrableOn (fun t : ℝ => t^p*(1-Real.log t)^m)
        (Set.Ioc (Real.exp i) δ) := by
      intro i
      by_cases hle : Real.exp i ≤ δ
      · have hcu : ContinuousOn (fun t : ℝ => t^p * (1 - Real.log t)^m)
            (Set.uIcc (Real.exp i) δ) := by
          rw [Set.uIcc_of_le hle]
          refine hcont.mono ?_
          intro x hx
          exact lt_of_lt_of_le (Real.exp_pos i) (Set.mem_Icc.1 hx).1
        exact (ContinuousOn.intervalIntegrable hcu).1
      · have hI0 : Set.Ioc (Real.exp i) δ = ∅ :=
          Set.Ioc_eq_empty_iff.mpr (not_lt.mpr (le_of_lt (not_le.mp hle)))
        rw [hI0]
        exact MeasureTheory.integrableOn_empty
    have hexp : Tendsto Real.exp atBot (𝓝[>] (0:ℝ)) := by
      show Tendsto Real.exp atBot (𝓝 (0:ℝ) ⊓ 𝓟 (Set.Ioi 0))
      exact tendsto_inf.2 ⟨Real.tendsto_exp_atBot,
        tendsto_principal.2 (Eventually.of_forall fun x => Real.exp_pos x)⟩
    have hcongr : ∀ i : ℝ, (∫ x in Set.Ioc (Real.exp i) δ,
        ‖(fun t : ℝ => t^p*(1-Real.log t)^m) x‖)
        = ∫ x in Set.Ioc (Real.exp i) δ, (fun t : ℝ => t^p*(1-Real.log t)^m) x := by
      intro i
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioc ?_
      apply ae_of_all
      intro x hx
      rcases Set.mem_Ioc.1 hx with ⟨h0, hle⟩
      have hx0 : 0 < x := lt_trans (Real.exp_pos i) h0
      have hlm : 0 ≤ 1 - Real.log x := by
        have hlx : Real.log x ≤ 0 := Real.log_nonpos hx0.le (le_trans hle hδ1)
        linarith
      have hprod : 0 ≤ x^p * (1 - Real.log x)^m :=
        mul_nonneg (Real.rpow_pos_of_pos hx0 p).le (pow_nonneg hlm m)
      show ‖x^p * (1 - Real.log x)^m‖ = x^p * (1 - Real.log x)^m
      rw [Real.norm_of_nonneg hprod]
    have hvalI : ∀ i : ℝ, Real.exp i ≤ δ →
        (∫ x in Set.Ioc (Real.exp i) δ, momentIntegrand m p x)
          = momentAnti m p δ - momentAnti m p (Real.exp i) := by
      intro i hle
      have hcu : ContinuousOn (fun t : ℝ => t^p * (1 - Real.log t)^m)
          (Set.uIcc (Real.exp i) δ) := by
        rw [Set.uIcc_of_le hle]
        refine hcont.mono ?_
        intro x hx
        exact lt_of_lt_of_le (Real.exp_pos i) (Set.mem_Icc.1 hx).1
      have hinti : IntervalIntegrable (momentIntegrand m p) volume (Real.exp i) δ :=
        ContinuousOn.intervalIntegrable hcu
      have hsub : ContinuousOn (momentAnti m p) (Set.Icc (Real.exp i) δ) := by
        intro t ht
        have htx : 0 < t := lt_of_lt_of_le (Real.exp_pos i) (Set.mem_Icc.1 ht).1
        exact (momentAnti_hasDeriv m p hp htx).continuousAt.continuousWithinAt
      have hder : ∀ x ∈ Set.Ioo (Real.exp i) δ,
          HasDerivAt (momentAnti m p) (momentIntegrand m p x) x :=
        fun x hx => momentAnti_hasDeriv m p hp (lt_trans (Real.exp_pos i) hx.1)
      rw [← intervalIntegral.integral_of_le hle,
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hsub hder hinti]
    have hcomp : Tendsto (fun i => momentAnti m p (Real.exp i)) atBot (𝓝 (0:ℝ)) :=
      (momentAnti_tendsto_zero m p hp).comp hexp
    have hsub2 : Tendsto (fun i => momentAnti m p δ - momentAnti m p (Real.exp i)) atBot
        (𝓝 (momentAnti m p δ - (0:ℝ))) := tendsto_const_nhds.sub hcomp
    have hsub3 : Tendsto (fun i => momentAnti m p δ - momentAnti m p (Real.exp i)) atBot
        (𝓝 (momentAnti m p δ)) := by simpa using hsub2
    have htend : Tendsto
        (fun i => ∫ x in Set.Ioc (Real.exp i) δ, (fun t : ℝ => t^p*(1-Real.log t)^m) x)
        atBot (𝓝 (momentAnti m p δ)) := by
      refine Tendsto.congr' ?_ hsub3
      refine eventually_atBot.2 ⟨Real.log δ, fun i hi => ?_⟩
      have hle : Real.exp i ≤ δ := by
        have h2 : Real.exp i ≤ Real.exp (Real.log δ) := (Real.exp_le_exp).mpr hi
        rwa [Real.exp_log hδ] at h2
      exact (hvalI i hle).symm
    obtain ⟨I', hI'⟩ := htend.isBoundedUnder_le
    have hbnd : ∀ᶠ i in atBot,
        (∫ x in Set.Ioc (Real.exp i) δ, ‖(fun t : ℝ => t^p*(1-Real.log t)^m) x‖) ≤ I' := by
      filter_upwards [hI'] with i hi
      rw [hcongr i]
      exact hi
    exact MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_left
      hfi Real.tendsto_exp_atBot hbnd
  refine ⟨hI, ?_⟩
  have hintG : IntervalIntegrable (fun t : ℝ => t^p*(1-Real.log t)^m) volume 0 δ :=
    ⟨hI, by rw [hempty]; exact MeasureTheory.integrableOn_empty⟩
  have hder : ∀ x ∈ Set.Ioo (0:ℝ) δ, HasDerivAt (momentAnti m p) (momentIntegrand m p x) x :=
    fun x hx => momentAnti_hasDeriv m p hp hx.1
  have ha0 : Tendsto (momentAnti m p) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    momentAnti_tendsto_zero m p hp
  have hb0 : Tendsto (momentAnti m p) (𝓝[<] δ) (𝓝 (momentAnti m p δ)) := by
    have h := (momentAnti_hasDeriv m p hp hδ).continuousAt
    exact Tendsto.mono_left h nhdsWithin_le_nhds
  show (∫ t in (0:ℝ)..δ, momentIntegrand m p t)
      = δ^(p+1) * ∑ j ∈ Finset.range (m+1),
        ((m.factorial : ℝ)/j.factorial/(p+1)^(m-j+1))*(1-Real.log δ)^j
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hδ hder hintG ha0 hb0,
    sub_zero]
  have hvalδ : momentAnti m p δ = δ^(p+1) * ∑ j ∈ Finset.range (m+1),
      ((m.factorial : ℝ)/j.factorial/(p+1)^(m-j+1))*(1-Real.log δ)^j := by
    simp only [momentAnti, momentCoeff]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ac_rfl)
  exact hvalδ
theorem endpoint_remainder {F : ℝ → ℂ} {p δ C : ℝ} {m : ℕ}
    (hp : -1 < p) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C)
    (hm : Measurable F)
    (hb : ∀ t ∈ Set.Ioo (0 : ℝ) δ, ‖F t‖ ≤ C*t^p*(1-Real.log t)^m) :
    IntegrableOn F (Set.Ioc 0 δ) ∧
    ‖∫ t in (0 : ℝ)..δ, F t‖ ≤ C*δ^(p+1) * ∑ j ∈ Finset.range (m+1),
      ((m.factorial : ℝ)/j.factorial/(p+1)^(m-j+1))*(1-Real.log δ)^j := by
  have h01 : (0:ℝ) ≤ δ := hδ.le
  have hempty : Set.Ioc δ (0:ℝ) = ∅ := Set.Ioc_eq_empty_of_le h01
  obtain ⟨hintG0, hvalG⟩ := power_log_moment hp hδ hδ1 m
  have hIF : IntegrableOn F (Set.Ioc 0 δ) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun t : ℝ => C * (t^p * (1 - Real.log t)^m)) ?_ ?_ ?_
    · exact hintG0.const_mul C
    · exact hm.aestronglyMeasurable
    · have hp1 : ∀ᵐ x ∂volume, x ∈ Set.Ioo (0:ℝ) δ →
          ‖F x‖ ≤ C*x^p*(1-Real.log x)^m := by
        apply ae_of_all
        intro x hx
        exact hb x hx
      have hne : ∀ᵐ x ∂volume, x ≠ δ := by
        rw [MeasureTheory.ae_iff]
        simp
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
      filter_upwards [hp1, hne] with x hx hδx
      intro hxi
      rcases Set.mem_Ioc.1 hxi with ⟨h0, hle⟩
      have hmem : x ∈ Set.Ioo 0 δ := ⟨h0, lt_of_le_of_ne hle hδx⟩
      have hbb := hb x hmem
      have hassoc : C*x^p*(1-Real.log x)^m = C * (x^p * (1 - Real.log x)^m) := by
        ac_rfl
      exact hbb.trans (le_of_eq hassoc)
  have hintF : IntervalIntegrable F volume 0 δ :=
    ⟨hIF, by rw [hempty]; exact MeasureTheory.integrableOn_empty⟩
  refine ⟨hIF, ?_⟩
  have hbound : ∀ x ∈ Set.Ioo (0:ℝ) δ, ‖F x‖ ≤ C * (x^p * (1 - Real.log x)^m) := by
    intro x hx
    have hbb := hb x hx
    have hassoc : C*x^p*(1-Real.log x)^m = C * (x^p * (1 - Real.log x)^m) := by
      ac_rfl
    exact hbb.trans (le_of_eq hassoc)
  have hintCg : IntervalIntegrable (fun t : ℝ => C * (t^p * (1 - Real.log t)^m)) volume 0 δ :=
    ⟨hintG0.const_mul C, by rw [hempty]; exact MeasureTheory.integrableOn_empty⟩
  have hnorm : ‖∫ t in (0:ℝ)..δ, F t‖ ≤ ∫ t in (0:ℝ)..δ, ‖F t‖ :=
    intervalIntegral.norm_integral_le_integral_norm h01
  have hmono : (∫ t in (0:ℝ)..δ, ‖F t‖) ≤ ∫ t in (0:ℝ)..δ, C * (t^p * (1 - Real.log t)^m) :=
    intervalIntegral.integral_mono_on_of_le_Ioo h01 hintF.norm hintCg hbound
  calc
    ‖∫ t in (0:ℝ)..δ, F t‖ ≤ ∫ t in (0:ℝ)..δ, ‖F t‖ := hnorm
    _ ≤ ∫ t in (0:ℝ)..δ, C * (t^p * (1 - Real.log t)^m) := hmono
    _ = C * ∫ t in (0:ℝ)..δ, t^p * (1 - Real.log t)^m :=
      intervalIntegral.integral_const_mul C (fun t : ℝ => t^p * (1 - Real.log t)^m)
    _ = C * (δ^(p+1) * ∑ j ∈ Finset.range (m+1),
        ((m.factorial : ℝ)/j.factorial/(p+1)^(m-j+1))*(1-Real.log δ)^j) := by
      rw [hvalG]
    _ = C*δ^(p+1) * ∑ j ∈ Finset.range (m+1),
          ((m.factorial : ℝ)/j.factorial/(p+1)^(m-j+1))*(1-Real.log δ)^j := by
      ac_rfl
theorem finite_power_value {a b p : ℝ} (hab : a ≤ b) (hp : -1 < p) :
    IntervalIntegrable (fun x : ℝ => (x-a)^p) volume a b ∧
      (∫ x in a..b, (x-a)^p) = (b-a)^(p+1)/(p+1) := by
  have h1 : IntervalIntegrable (fun y : ℝ => y^p) volume 0 (b - a) :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hint : IntervalIntegrable (fun x : ℝ => (x - a)^p) volume a b := by
    simpa using h1.comp_sub_right a
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_comp_sub_right (f := fun y : ℝ => y ^ p) a,
    integral_rpow (Or.inl hp), sub_self,
    Real.zero_rpow (show (p:ℝ) + 1 ≠ 0 by linarith)]
  ring

theorem finite_log_value {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable Real.log volume 0 b ∧
      (∫ x in (0 : ℝ)..b, Real.log x) = b*(Real.log b-1) := by
  have hI : IntervalIntegrable Real.log volume (0:ℝ) b :=
    intervalIntegral.intervalIntegrable_log'
  refine ⟨hI, ?_⟩
  simp [integral_log]
  ring

theorem right_exp_value (a c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (c-x)) (Set.Ioi a) ∧
      (∫ x in Set.Ioi a, Real.exp (c-x)) = Real.exp (c-a) := by
  have hder : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -Real.exp (c - y)) (Real.exp (c - x)) x := by
    intro x
    have h2 : HasDerivAt (fun y : ℝ => c - y) (-1) x := (hasDerivAt_id x).const_sub c
    have hcomp : HasDerivAt (fun y : ℝ => Real.exp (c - y)) ((-1:ℝ) • Real.exp (c - x)) x :=
      HasDerivAt.scomp x (Real.hasDerivAt_exp (c - x)) h2
    exact hcomp.neg.congr_deriv (by simp)
  have hfunext : (fun y : ℝ => Real.exp (c - y)) = fun y : ℝ => Real.exp c / Real.exp y := by
    funext y
    rw [Real.exp_sub c y]
  have hzT : Tendsto (fun y : ℝ => Real.exp (c - y)) atTop (𝓝 (0:ℝ)) := by
    rw [hfunext]
    exact Filter.Tendsto.const_div_atTop Real.tendsto_exp_atTop (Real.exp c)
  have hgTneg : Tendsto (fun y : ℝ => -Real.exp (c - y)) atTop (𝓝 (-(0:ℝ))) := hzT.neg
  refine ⟨?_, ?_⟩
  · exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
      (g := fun y : ℝ => -Real.exp (c - y)) (g' := fun y : ℝ => Real.exp (c - y)) (l := -(0:ℝ))
      (fun x _ => hder x) (fun x _ => by positivity) hgTneg
  · have hw : (∫ x in Set.Ioi a, Real.exp (c - x))
        = (-(0:ℝ)) - (-(Real.exp (c - a))) := by
      exact MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
        (g := fun y : ℝ => -Real.exp (c - y)) (g' := fun y : ℝ => Real.exp (c - y)) (l := -(0:ℝ))
        (fun x _ => hder x) (fun x _ => by positivity) hgTneg
    rw [hw]
    simp

theorem finite_power_substitution {f : ℝ → ℝ} (hm : Measurable f) {n : ℕ}
    (hn : 0 < n) :
    IntervalIntegrable f volume 0 1 ↔
      IntervalIntegrable (fun t : ℝ => (n:ℝ)*t^(n-1)*f (t^n)) volume 0 1 := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have hder : ∀ x ∈ Set.Ioo (0:ℝ) 1, HasDerivAt (fun t : ℝ => t ^ n) ((n:ℝ) * x ^ (n-1)) x := by
    intro x hx
    have h : HasDerivAt (fun t : ℝ => t ^ n) ((n:ℝ) * x ^ (n-1) * 1) x :=
      (hasDerivAt_id x).pow n
    simpa [mul_one] using h
  have hnn : ∀ x ∈ Set.Ioo (0:ℝ) 1, 0 ≤ (n:ℝ) * x ^ (n-1) := by
    intro x hx
    exact mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (le_of_lt hx.1) _)
  have hpow0 : ((0:ℝ)) ^ n = 0 := zero_pow hn.ne'
  have hpow1 : ((1:ℝ)) ^ n = 1 := one_pow n
  have hiff : IntegrableOn (fun x : ℝ => ((n:ℝ) * x^(n-1)) • f (x^n)) (Set.Icc (0:ℝ) 1)
      ↔ IntegrableOn f (Set.Icc ((0:ℝ)^n) ((1:ℝ)^n)) :=
    integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg (f := fun t : ℝ => t ^ n)
      (f' := fun t : ℝ => (n:ℝ) * t ^ (n-1)) (g := f) (continuousOn_pow n) hder hnn h01
  rw [hpow0, hpow1] at hiff
  have hleft : (fun x : ℝ => ((n:ℝ) * x^(n-1)) • f (x^n))
      =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)] (fun x : ℝ => (n:ℝ) * x^(n-1) * f (x^n)) :=
    ae_of_all _ (fun x => rfl)
  rw [MeasureTheory.integrableOn_congr_fun_ae hleft] at hiff
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h01,
    intervalIntegrable_iff_integrableOn_Ioc_of_le h01,
    integrableOn_Ioc_iff_integrableOn_Ioo, integrableOn_Ioc_iff_integrableOn_Ioo,
    ← integrableOn_Icc_iff_integrableOn_Ioo, ← integrableOn_Icc_iff_integrableOn_Ioo,
    hiff]

theorem finite_power_substitution_value {f : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hi : IntervalIntegrable f volume 0 1) :
    (∫ t in (0 : ℝ)..1, f t) = ∫ t in (0 : ℝ)..1, (n:ℝ)*t^(n-1)*f (t^n) := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have hder : ∀ x ∈ Set.Ioo (0:ℝ) 1, HasDerivAt (fun t : ℝ => t ^ n) ((n:ℝ) * x ^ (n-1)) x := by
    intro x hx
    have h : HasDerivAt (fun t : ℝ => t ^ n) ((n:ℝ) * x ^ (n-1) * 1) x :=
      (hasDerivAt_id x).pow n
    simpa [mul_one] using h
  have hnn : ∀ x ∈ Set.Ioo (0:ℝ) 1, 0 ≤ (n:ℝ) * x ^ (n-1) := by
    intro x hx
    exact mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (le_of_lt hx.1) _)
  have hpow0 : ((0:ℝ)) ^ n = 0 := zero_pow hn.ne'
  have hpow1 : ((1:ℝ)) ^ n = 1 := one_pow n
  have hmain : ∫ x in Set.Icc (0:ℝ) 1, ((n:ℝ) * x^(n-1)) • f (x^n)
      = ∫ u in Set.Icc ((0:ℝ)^n) ((1:ℝ)^n), f u :=
    integral_Icc_deriv_smul_of_deriv_nonneg (f := fun t : ℝ => t ^ n)
      (f' := fun t : ℝ => (n:ℝ) * t ^ (n-1)) (g := f) (continuousOn_pow n) hder hnn h01
  rw [hpow0, hpow1] at hmain
  have hconv : ∀ (g : ℝ → ℝ), ∫ x in Set.Icc (0:ℝ) 1, g x = ∫ t in (0:ℝ)..1, g t := by
    intro g
    rw [integral_Icc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le h01]
  have hL : ∫ x in Set.Icc (0:ℝ) 1, ((n:ℝ) * x^(n-1)) • f (x^n)
      = ∫ x in Set.Icc (0:ℝ) 1, (n:ℝ) * x^(n-1) * f (x^n) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun x _ => ?_)
    rfl
  calc
    ∫ t in (0:ℝ)..1, f t = ∫ u in Set.Icc (0:ℝ) 1, f u := (hconv f).symm
    _ = ∫ x in Set.Icc (0:ℝ) 1, ((n:ℝ) * x^(n-1)) • f (x^n) := hmain.symm
    _ = ∫ x in Set.Icc (0:ℝ) 1, (n:ℝ) * x^(n-1) * f (x^n) := hL
    _ = ∫ t in (0:ℝ)..1, (n:ℝ) * t^(n-1) * f (t^n) := hconv _

theorem sqrt_power_factor {t a p : ℝ} (ht : 0 < t) :
    Real.sqrt (t^p*a) = t^(p/2)*Real.sqrt a := by
  rcases lt_or_ge 0 a with hlt | hle
  · rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      Real.mul_rpow (Real.rpow_pos_of_pos ht p).le (le_of_lt hlt),
      ← Real.rpow_mul ht.le p ((1:ℝ)/2)]
    congr 1
    ring
  · have hprod : t^p * a ≤ t^p * 0 :=
      mul_le_mul_of_nonneg_left hle (Real.rpow_pos_of_pos ht p).le
    rw [mul_zero] at hprod
    rw [Real.sqrt_eq_zero_of_nonpos hprod, Real.sqrt_eq_zero_of_nonpos hle, mul_zero]

theorem whole_split {f : ℝ → ℝ}
    (hr : IntegrableOn f (Set.Ioi 0)) (hl : IntegrableOn f (Set.Iio 0)) :
    Integrable f ∧ (∫ x, f x) = (∫ x in Set.Ioi (0:ℝ), f x)+(∫ x in Set.Iio (0:ℝ), f x) := by
  have hcomb : Set.Ioi (0:ℝ) ∪ Set.Iio (0:ℝ) = ({(0:ℝ)} : Set ℝ)ᶜ := by
    rw [Set.union_comm, Set.Iio_union_Ioi]
  have hae : Set.univ =ᵐ[volume] (Set.Ioi (0:ℝ) ∪ Set.Iio (0:ℝ)) := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [hcomb, Set.diff_compl, Set.univ_inter, Real.volume_singleton]
    · simp
  have hun : IntegrableOn f (Set.Ioi (0:ℝ) ∪ Set.Iio (0:ℝ)) := hr.union hl
  have hun' : IntegrableOn f Set.univ volume :=
    (MeasureTheory.integrableOn_congr_set_ae hae.symm).mp hun
  refine ⟨MeasureTheory.integrableOn_univ.mp hun', ?_⟩
  have hstep : (∫ x, f x) = ∫ x in (Set.Ioi (0:ℝ) ∪ Set.Iio (0:ℝ)), f x := by
    rw [← MeasureTheory.setIntegral_univ, ← MeasureTheory.setIntegral_congr_set hae]
  rw [hstep, MeasureTheory.setIntegral_union Set.Ioi_disjoint_Iio_same
    (isOpen_Iio).measurableSet hr hl]

theorem exp_negative_nat (k : ℕ) : Real.exp (-(k:ℝ)) ≤ (2:ℝ)^(-(k:ℤ)) := by
  have hlog2 : Real.log 2 ≤ 1 :=
    (Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 2)).mpr Real.exp_one_gt_two.le
  have hkey : (2:ℝ)^k ≤ Real.exp (k:ℝ) := by
    have hexp2 : Real.exp (Real.log 2 * (k:ℝ)) = (2:ℝ)^k := by
      rw [Real.exp_mul, Real.exp_log (by norm_num : (0:ℝ) < 2), Real.rpow_natCast]
    have hmax : Real.log 2 * ↑k ≤ 1 * ↑k :=
      mul_le_mul_of_nonneg_right hlog2 (Nat.cast_nonneg' k)
    rw [one_mul] at hmax
    rw [← hexp2]
    exact Real.exp_le_exp.mpr hmax
  rw [zpow_neg, zpow_natCast, Real.exp_neg]
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hkey

theorem whole_split_at {f : ℝ → ℝ} {a : ℝ}
    (hr : IntegrableOn f (Set.Ioi a)) (hl : IntegrableOn f (Set.Iio a)) :
    Integrable f ∧ (∫ x, f x) = (∫ x in Set.Ioi a, f x)+(∫ x in Set.Iio a, f x) := by
  have hcomb : Set.Ioi a ∪ Set.Iio a = {a}ᶜ := by
    rw [Set.union_comm, Set.Iio_union_Ioi]
  have hae : Set.univ =ᵐ[volume] (Set.Ioi a ∪ Set.Iio a) := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [hcomb, Set.diff_compl, Set.univ_inter, Real.volume_singleton]
    · simp
  have hun : IntegrableOn f (Set.Ioi a ∪ Set.Iio a) := hr.union hl
  have hun' : IntegrableOn f Set.univ volume :=
    (MeasureTheory.integrableOn_congr_set_ae hae.symm).mp hun
  refine ⟨MeasureTheory.integrableOn_univ.mp hun', ?_⟩
  have hstep : (∫ x, f x) = ∫ x in (Set.Ioi a ∪ Set.Iio a), f x := by
    rw [← MeasureTheory.setIntegral_univ, ← MeasureTheory.setIntegral_congr_set hae]
  rw [hstep, MeasureTheory.setIntegral_union Set.Ioi_disjoint_Iio_same
    (isOpen_Iio).measurableSet hr hl]

theorem left_exp_value (a c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (c+x)) (Set.Iio a) ∧
      (∫ x in Set.Iio a, Real.exp (c+x)) = Real.exp (c+a) := by
  have hderiv : ∀ x ∈ Set.Iic a, HasDerivAt (fun y : ℝ => Real.exp (c + y)) (Real.exp (c + x)) x := by
    intro x _
    have h2 : HasDerivAt (fun y : ℝ => c + y) ((0:ℝ) + 1) x :=
      (hasDerivAt_const x c).add (hasDerivAt_id x)
    have hcomp : HasDerivAt (fun y : ℝ => Real.exp (c + y)) (((0:ℝ) + 1) • Real.exp (c + x)) x :=
      HasDerivAt.scomp x (Real.hasDerivAt_exp (c + x)) h2
    exact hcomp.congr_deriv (by simp)
  have hIic : IntegrableOn (fun x : ℝ => Real.exp (c + x)) (Set.Iic a) := by
    have hbase : Integrable (fun x : ℝ => Real.exp x) (volume.restrict (Set.Iic a)) :=
      integrableOn_exp_Iic a
    have hmul : Integrable (fun x : ℝ => Real.exp c * Real.exp x) (volume.restrict (Set.Iic a)) :=
      hbase.const_mul (Real.exp c)
    have hfun : (fun x : ℝ => Real.exp (c + x)) = fun x => Real.exp c * Real.exp x := by
      funext x
      exact Real.exp_add c x
    rw [hfun]
    exact hmul
  have htend : Tendsto (fun y : ℝ => Real.exp (c + y)) atBot (𝓝 (0:ℝ)) := by
    have hflip : Tendsto (fun y : ℝ => Real.exp (c - y)) atTop (𝓝 (0:ℝ)) := by
      have hfunext : (fun y : ℝ => Real.exp (c - y)) = fun y : ℝ => Real.exp c / Real.exp y := by
        funext y
        rw [Real.exp_sub c y]
      rw [hfunext]
      exact Filter.Tendsto.const_div_atTop Real.tendsto_exp_atTop (Real.exp c)
    refine (hflip.comp tendsto_neg_atBot_atTop).congr' (Eventually.of_forall fun y => ?_)
    simp [Function.comp]
  have hvalIic : (∫ x in Set.Iic a, Real.exp (c + x)) = Real.exp (c + a) - (0:ℝ) :=
    MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto' hderiv hIic htend
  have hae : (Set.Iio a : Set ℝ) =ᵐ[volume] Set.Iic a := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · have hempty : Set.Iio a \ Set.Iic a = ∅ :=
        (Set.diff_eq_empty).2 (fun x hx => (Set.mem_Iio.1 hx).le)
      rw [hempty]
      simp
    · rw [Set.Iic_sdiff_Iio_same, Real.volume_singleton]
  have hval : (∫ x in Set.Iio a, Real.exp (c + x)) = Real.exp (c + a) := by
    rw [MeasureTheory.setIntegral_congr_set hae, hvalIic, sub_zero]
  exact ⟨(integrableOn_Iic_iff_integrableOn_Iio).mp hIic, hval⟩

end Intgrl
