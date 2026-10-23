module

import Mathlib

/-! Mathematical lemmas for endpoint envelopes and parameter integrals.
This file imports only Mathlib and is copied verbatim to `/tmp/intgrl`.
There are no interval representations, expression evaluators or certificates
in these statements. -/
noncomputable section
open MeasureTheory
open scoped Topology

namespace Intgrl

/-- Absorb logarithmic growth into half of a positive endpoint power. -/
theorem power_log_absorb {t p : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hp : 0 < p) (m : ℕ) :
    t^p * (1 - Real.log t)^m ≤
      (2:ℝ)^m * (1 + (m.factorial:ℝ) / (p/2)^m) * t^(p/2) := by
  set L := -Real.log t with hL
  have hL0 : 0 ≤ L := by rw [hL]; linarith [Real.log_nonpos ht.le ht1]
  have h1 : 1 - Real.log t = 1 + L := by rw [hL]; ring
  have htp2 : t^(p/2) = Real.exp (-(p/2) * L) := by
    rw [Real.rpow_def_of_pos ht, hL]; ring_nf
  have htp : t^p = t^(p/2) * t^(p/2) := by
    rw [← Real.rpow_add ht]; ring_nf
  have hpow : (1 + L)^m ≤ 2^m * (1 + L^m) := by
    rcases le_total L 1 with h | h
    · calc (1+L)^m ≤ 2^m := pow_le_pow_left₀ (by linarith) (by linarith) m
        _ ≤ 2^m * (1 + L^m) := by
          have : 0 ≤ L^m := pow_nonneg hL0 m
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) m]
    · calc (1+L)^m ≤ (2*L)^m := pow_le_pow_left₀ (by linarith) (by linarith) m
        _ = 2^m * L^m := mul_pow _ _ _
        _ ≤ 2^m * (1 + L^m) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) m]
  have hexp : t^(p/2) * L^m ≤ m.factorial / (p/2)^m := by
    have hq : 0 < p/2 := by linarith
    have := Real.pow_div_factorial_le_exp ((p/2) * L) (by positivity) m
    rw [div_le_iff₀ (by positivity)] at this
    rw [le_div_iff₀ (by positivity), htp2]
    have e : Real.exp (-(p/2) * L) * Real.exp ((p/2) * L) = 1 := by
      rw [← Real.exp_add]; simp
    have hE := Real.exp_pos ((p/2) * L)
    have hE2 := Real.exp_pos (-(p/2) * L)
    calc Real.exp (-(p / 2) * L) * L ^ m * (p / 2) ^ m
        = Real.exp (-(p / 2) * L) * ((p/2) * L)^m := by rw [mul_pow]; ring
      _ ≤ Real.exp (-(p / 2) * L) * (Real.exp ((p/2) * L) * m.factorial) := by gcongr
      _ = m.factorial := by rw [← mul_assoc, e, one_mul]
  have ht2pos : 0 < t^(p/2) := Real.rpow_pos_of_pos ht _
  have ht2le : t^(p/2) ≤ 1 := Real.rpow_le_one ht.le ht1 (by linarith)
  rw [h1, htp]
  calc t^(p/2) * t^(p/2) * (1+L)^m ≤ t^(p/2) * t^(p/2) * (2^m * (1 + L^m)) := by gcongr
    _ = 2^m * t^(p/2) * (t^(p/2) + t^(p/2) * L^m) := by ring
    _ ≤ 2^m * t^(p/2) * (1 + m.factorial / (p/2)^m) := by gcongr
    _ = _ := by ring

/-- The real logarithm uses the same branch on either side of zero. -/
theorem real_log_scaled_bound {t p a : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |Real.log (t^p * a)| ≤ (|p| + |Real.log a|) * (1 - Real.log t) := by
  have hlt : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  rcases eq_or_ne a 0 with rfl | ha
  · simp; nlinarith [abs_nonneg p]
  rw [Real.log_mul (Real.rpow_pos_of_pos ht p).ne' ha, Real.log_rpow ht]
  calc |p * Real.log t + Real.log a| ≤ |p| * |Real.log t| + |Real.log a| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ (|p| + |Real.log a|) * (1 - Real.log t) := by
        rw [abs_of_nonpos hlt]; nlinarith [abs_nonneg p, abs_nonneg (Real.log a)]

/-- Uniform exponential decay, including complex coefficients. -/
theorem complex_exp_scaled_bound {t p C : ℝ} {z : ℂ}
    (ht : 0 < t) (hC : 0 < C) (hz : z.re ≤ -C) (n : ℕ) :
    ‖Complex.exp (((t^p:ℝ):ℂ) * z)‖ ≤
      ((n.factorial:ℝ) / C^n) * t^((-p)*(n:ℝ)) := by
  have htp : 0 < t^p := Real.rpow_pos_of_pos ht p
  rw [Complex.norm_exp]
  have hre : (((t^p:ℝ):ℂ) * z).re = t^p * z.re := by simp
  rw [hre]
  set u := C * t^p with hu
  have hu0 : 0 < u := mul_pos hC htp
  have h1 : Real.exp (t^p * z.re) ≤ Real.exp (-u) := by
    apply Real.exp_le_exp.2; nlinarith
  have h2 : u^n * Real.exp (-u) ≤ n.factorial := by
    have := Real.pow_div_factorial_le_exp u hu0.le n
    rw [Real.exp_neg]
    rw [div_le_iff₀ (by positivity)] at this
    rw [mul_inv_le_iff₀ (Real.exp_pos u)]
    linarith
  have h3 : t^((-p)*(n:ℝ)) = ((t^p)^n)⁻¹ := by
    rw [neg_mul, Real.rpow_neg ht.le, Real.rpow_mul ht.le, Real.rpow_natCast]
  rw [h3]
  calc Real.exp (t^p * z.re) ≤ Real.exp (-u) := h1
    _ ≤ (n.factorial:ℝ) / u^n := by rw [le_div_iff₀ (by positivity)]; linarith
    _ = _ := by rw [hu, mul_pow]; field_simp

theorem real_rpow_scaled {t p a q : ℝ} (ht : 0 < t) (ha : 0 < a) :
    (t^p * a)^q = t^(p*q) * a^q := by
  rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) ha.le, ← Real.rpow_mul ht.le]

/-- Positive real scaling does not cross the principal logarithm cut. -/
theorem complex_log_scaled_bound {t p : ℝ} {z : ℂ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hz : z ≠ 0) :
    ‖Complex.log (((t^p:ℝ):ℂ) * z)‖ ≤
      (|p| + ‖Complex.log z‖) * (1 - Real.log t) := by
  have htp : 0 < t^p := Real.rpow_pos_of_pos ht p
  have hlt : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  have hl : Complex.log (((t^p:ℝ):ℂ) * z) = ((p * Real.log t : ℝ) : ℂ) + Complex.log z := by
    rw [Complex.log_ofReal_mul htp hz, Real.log_rpow ht]
  rw [hl]
  calc ‖((p * Real.log t : ℝ) : ℂ) + Complex.log z‖
        ≤ |p| * |Real.log t| + ‖Complex.log z‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    _ ≤ _ := by
        rw [abs_of_nonpos hlt]; nlinarith [abs_nonneg p, norm_nonneg (Complex.log z)]

/-- A bounded complex integral has a mean in the same closed rectangle. -/
theorem complex_integral_rectangle_mean {F : ℝ → ℂ} {a b l u v w : ℝ}
    (hab : a ≤ b) (hlu : l ≤ u) (hvw : v ≤ w) (hm : Measurable F)
    (hF : ∀ x ∈ Set.Ioo a b, (F x).re ∈ Set.Icc l u ∧ (F x).im ∈ Set.Icc v w) :
    IntervalIntegrable F volume a b ∧ ∃ z : ℂ,
      z.re ∈ Set.Icc l u ∧ z.im ∈ Set.Icc v w ∧
      (∫ x in a..b, F x) = ((b-a:ℝ):ℂ) * z := by
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      (F t).re ∈ Set.Icc l u ∧ (F t).im ∈ Set.Icc v w := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have h1 : ∀ᵐ t ∂volume, t ≠ b := by simp [ae_iff, measure_singleton]
    have h2 : ∀ᵐ t ∂volume, t ≠ a := by simp [ae_iff, measure_singleton]
    filter_upwards [h1, h2] with t ht ht' htm
    exact hF t ⟨lt_of_le_of_ne htm.1 (Ne.symm ht'), lt_of_le_of_ne htm.2 ht⟩
  have hint : IntegrableOn F (Set.Icc a b) volume := by
    refine Measure.integrableOn_of_bounded (M := (max |l| |u|) + max |v| |w|) ?_
      hm.aestronglyMeasurable ?_
    · simp [Real.volume_Icc]
    · filter_upwards [hae] with t ht
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      gcongr
      · rw [abs_le]; constructor
        · linarith [le_max_left |l| |u|, neg_abs_le l, ht.1.1]
        · linarith [le_max_right |l| |u|, le_abs_self u, ht.1.2]
      · rw [abs_le]; constructor
        · linarith [le_max_left |v| |w|, neg_abs_le v, ht.2.1]
        · linarith [le_max_right |v| |w|, le_abs_self w, ht.2.2]
  have hii : IntervalIntegrable F volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hint
  refine ⟨hii, ?_⟩
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact ⟨⟨l, v⟩, ⟨le_rfl, hlu⟩, ⟨le_rfl, hvw⟩, by simp⟩
  have hre : ∀ g : ℂ →L[ℝ] ℝ, (∫ x in a..b, g (F x)) = g (∫ x in a..b, F x) := fun g =>
    g.intervalIntegral_comp_comm hii
  set I := ∫ x in a..b, F x
  have hba : 0 < b - a := by linarith
  refine ⟨I / ((b-a:ℝ):ℂ), ?_, ?_, ?_⟩
  · have hreI : I.re = ∫ x in a..b, (F x).re := (hre Complex.reCLM).symm
    have hrii : IntervalIntegrable (fun x => (F x).re) volume a b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hint.re
    have hlo := intervalIntegral.integral_mono_ae_restrict hab intervalIntegrable_const hrii
      (f := fun _ => l) (g := fun x => (F x).re) (by filter_upwards [hae] with t ht; exact ht.1.1)
    have hhi := intervalIntegral.integral_mono_ae_restrict hab hrii intervalIntegrable_const
      (f := fun x => (F x).re) (g := fun _ => u) (by filter_upwards [hae] with t ht; exact ht.1.2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hlo hhi
    rw [Complex.div_ofReal_re, hreI]
    constructor
    · rw [le_div_iff₀ hba]; linarith
    · rw [div_le_iff₀ hba]; linarith
  · have hreI : I.im = ∫ x in a..b, (F x).im := (hre Complex.imCLM).symm
    have hrii : IntervalIntegrable (fun x => (F x).im) volume a b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hint.im
    have hlo := intervalIntegral.integral_mono_ae_restrict hab intervalIntegrable_const hrii
      (f := fun _ => v) (g := fun x => (F x).im) (by filter_upwards [hae] with t ht; exact ht.2.1)
    have hhi := intervalIntegral.integral_mono_ae_restrict hab hrii intervalIntegrable_const
      (f := fun x => (F x).im) (g := fun _ => w) (by filter_upwards [hae] with t ht; exact ht.2.2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hlo hhi
    rw [Complex.div_ofReal_im, hreI]
    constructor
    · rw [le_div_iff₀ hba]; linarith
    · rw [div_le_iff₀ hba]; linarith
  · have : ((b-a:ℝ):ℂ) ≠ 0 := by exact_mod_cast hba.ne'
    field_simp

/-- Oriented affine substitution also covers reversed and zero-width intervals. -/
theorem finite_affine_integrable {F : ℝ → ℝ} {a b : ℝ} (hm : Measurable F) :
    IntervalIntegrable F volume a b ↔
      IntervalIntegrable (fun t : ℝ => (b-a) * F (a+(b-a)*t)) volume 0 1 := by
  rcases eq_or_ne (b - a) 0 with h | h
  · have : b = a := by linarith
    subst this; simp
  have e1 : IntervalIntegrable (fun t : ℝ => (b-a) * F (a+(b-a)*t)) volume 0 1 ↔
      IntervalIntegrable (fun t : ℝ => F (a+(b-a)*t)) volume 0 1 := by
    constructor
    · intro hi
      have := hi.const_mul (b-a)⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ h] using this
    · intro hi; exact hi.const_mul _
  rw [e1]
  have e2 := IntervalIntegrable.comp_mul_left_iff (f := fun x => F (a + x)) (a := 0)
    (b := b - a) h
  simp only [zero_div, div_self h] at e2
  rw [e2]
  have e3 := IntervalIntegrable.comp_add_left_iff (f := F) (a := a) (b := b) (c := a)
  simp only [sub_self] at e3
  exact e3.symm

theorem finite_affine_value {F : ℝ → ℝ} {a b : ℝ}
    (hi : IntervalIntegrable F volume a b) :
    (∫ x in a..b, F x) = ∫ t in (0:ℝ)..1, (b-a) * F (a+(b-a)*t) := by
  rcases eq_or_ne (b - a) 0 with h | h
  · have : b = a := by linarith
    subst this; simp
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_mul _ h]
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel, smul_eq_mul]
  field_simp

/-- The constant in a bounded-interval remainder estimate need not be sharp. -/
theorem interval_remainder_bound {F : ℝ → ℝ} {a b M : ℝ}
    (hm : Measurable F) (hM : 0 ≤ M)
    (hF : ∀ x ∈ Set.uIoo a b, |F x| ≤ M) :
    IntervalIntegrable F volume a b ∧ |∫ x in a..b, F x| ≤ |b-a| * M := by
  have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → ‖F t‖ ≤ M := by
    have h1 : ∀ᵐ t ∂volume, t ≠ max a b := by simp [ae_iff, measure_singleton]
    filter_upwards [h1] with t ht htm
    rw [Real.norm_eq_abs]
    apply hF
    rw [Set.uIoc] at htm
    exact ⟨htm.1, lt_of_le_of_ne htm.2 ht⟩
  have hii : IntervalIntegrable F volume a b := by
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := M) ?_ hm.aestronglyMeasurable ?_
    · rw [Set.uIoc]; simp [Real.volume_Ioc]
    · rw [ae_restrict_iff' measurableSet_uIoc]; exact hae
  refine ⟨hii, ?_⟩
  have := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := a) (b := b) (f := F)
    (C := M) hae
  rw [Real.norm_eq_abs] at this
  linarith [mul_comm |b-a| M]

/-- Assemble a truncated integral with two integrable endpoint remainders. -/
theorem endpoint_truncation {F : ℝ → ℂ} {a b L R : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (hl : IntervalIntegrable F volume 0 a) (hm : IntervalIntegrable F volume a b)
    (hr : IntervalIntegrable F volume b 1)
    (hL : ‖∫ t in (0:ℝ)..a, F t‖ ≤ L) (hR : ‖∫ t in b..(1:ℝ), F t‖ ≤ R) :
    IntervalIntegrable F volume 0 1 ∧
      ‖(∫ t in (0:ℝ)..1, F t) - (∫ t in a..b, F t)‖ ≤ L+R := by
  refine ⟨(hl.trans hm).trans hr, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (hl.trans hm) hr,
    ← intervalIntegral.integral_add_adjacent_intervals hl hm]
  calc ‖(∫ t in (0:ℝ)..a, F t) + (∫ t in a..b, F t) + (∫ t in b..(1:ℝ), F t)
        - ∫ t in a..b, F t‖
      = ‖(∫ t in (0:ℝ)..a, F t) + (∫ t in b..(1:ℝ), F t)‖ := by ring_nf
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hL hR)

section ParamAnalytic
open Metric
open scoped Nat
theorem iteratedFDeriv_comp_affine_of_analytic {A E B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℂ A] [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup B]
    [NormedSpace ℂ B] [CompleteSpace B]
    {f : E → B} {Ω : Set E} (hΩ : IsOpen Ω) (hf : AnalyticOnNhd ℂ f Ω) (c : E) (L : A →L[ℂ] E)
    (n : ℕ) : ∀ a : A, c + L a ∈ Ω →
    iteratedFDeriv ℂ n (fun a => f (c + L a)) a =
      (iteratedFDeriv ℂ n f (c + L a)).compContinuousLinearMap (fun _ => L) := by
  induction n with
  | zero =>
    intro a _
    ext m; simp
  | succ n ih =>
    intro a ha
    have hopen : IsOpen {a : A | c + L a ∈ Ω} :=
      hΩ.preimage (continuous_const.add L.continuous)
    have heq : iteratedFDeriv ℂ n (fun a => f (c + L a)) =ᶠ[𝓝 a]
        fun a => ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin n => L)
          (iteratedFDeriv ℂ n f (c + L a)) := by
      filter_upwards [hopen.mem_nhds ha] with b hb
      rw [ih b hb]; rfl
    have hd : HasFDerivAt (fun a => ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin n => L) (iteratedFDeriv ℂ n f (c + L a)))
        ((ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin n => L)).comp
          ((fderiv ℂ (iteratedFDeriv ℂ n f) (c + L a)).comp L)) a := by
      have h1 : HasFDerivAt (iteratedFDeriv ℂ n f)
          (fderiv ℂ (iteratedFDeriv ℂ n f) (c + L a)) (c + L a) :=
        ((hf.iteratedFDeriv n) _ ha).differentiableAt.hasFDerivAt
      have h2 : HasFDerivAt (fun a => c + L a) L a := by
        simpa using (L.hasFDerivAt).const_add c
      exact (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin n => L)).hasFDerivAt.comp a (h1.comp a h2)
    ext m
    rw [iteratedFDeriv_succ_apply_left, heq.fderiv_eq, hd.fderiv]
    simp [iteratedFDeriv_succ_apply_left]
    rfl

theorem norm_fderiv_le_of_closedBall {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup B] [NormedSpace ℂ B] {g : E → B} {Ω : Set E} {z : E} {ρ K : ℝ}
    (hρ : 0 < ρ) (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (hsub : closedBall z ρ ⊆ Ω)
    (hK : ∀ w ∈ closedBall z ρ, ‖g w‖ ≤ K) : ‖fderiv ℂ g z‖ ≤ K / ρ := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK z (mem_closedBall_self hρ.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have hhn : 0 < ‖h‖ := norm_pos_iff.2 hh
  have hr : 0 < ρ / ‖h‖ := by positivity
  set gl : ℂ → B := fun l => g (z + l • h) with hgl
  have hmem : ∀ l ∈ closedBall (0:ℂ) (ρ / ‖h‖), z + l • h ∈ closedBall z ρ := by
    intro l hl
    rw [mem_closedBall, dist_eq_norm] at hl ⊢
    rw [add_sub_cancel_left, norm_smul]
    rw [sub_zero, le_div_iff₀ hhn] at hl
    exact hl
  have hdiff : ∀ l ∈ closedBall (0:ℂ) (ρ / ‖h‖), DifferentiableAt ℂ gl l := by
    intro l hl
    have h1 : DifferentiableAt ℂ g (z + l • h) :=
      (hg _ (hsub (hmem l hl))).differentiableAt (hΩ.mem_nhds (hsub (hmem l hl)))
    have h2 : DifferentiableAt ℂ (fun l : ℂ => z + l • h) l :=
      (differentiableAt_id.smul_const h).const_add z
    exact h1.comp l h2
  have hdc : DiffContOnCl ℂ gl (ball (0:ℂ) (ρ / ‖h‖)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    exact fun l hl => (hdiff l hl).differentiableWithinAt
  have hderiv : deriv gl 0 = fderiv ℂ g z h := by
    have h1 : HasFDerivAt g (fderiv ℂ g z) (z + (0:ℂ) • h) := by
      rw [zero_smul, add_zero]
      exact ((hg z (hsub (mem_closedBall_self hρ.le))).differentiableAt
        (hΩ.mem_nhds (hsub (mem_closedBall_self hρ.le)))).hasFDerivAt
    have h2 : HasDerivAt (fun l : ℂ => z + l • h) h 0 := by
      simpa using ((hasDerivAt_id (0:ℂ)).smul_const h).const_add z
    exact (h1.comp_hasDerivAt (0:ℂ) h2).deriv
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc
    (C := K) (fun l hl => hK _ (hmem l (sphere_subset_closedBall hl)))
  rw [hderiv] at hC
  calc ‖fderiv ℂ g z h‖ ≤ K / (ρ / ‖h‖) := hC
    _ = K / ρ * ‖h‖ := by field_simp

theorem norm_iteratedFDeriv_le_of_closedBall {E B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {f : E → B} {Ω : Set E}
    (hΩ : IsOpen Ω) (hf : AnalyticOnNhd ℂ f Ω) {M : ℝ} (hM : ∀ w ∈ Ω, ‖f w‖ ≤ M) (n : ℕ) :
    ∀ z ρ, 0 < ρ → closedBall z (n * ρ) ⊆ Ω → ‖iteratedFDeriv ℂ n f z‖ ≤ M / ρ ^ n := by
  induction n with
  | zero =>
    intro z ρ _ hsub
    simp only [norm_iteratedFDeriv_zero, pow_zero, div_one]
    exact hM z (hsub (by simp))
  | succ n ih =>
    intro z ρ hρ hsub
    rw [← norm_fderiv_iteratedFDeriv]
    have hsub1 : closedBall z ρ ⊆ Ω := (closedBall_subset_closedBall (by
      push_cast; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])).trans hsub
    have := norm_fderiv_le_of_closedBall hρ hΩ ((hf.iteratedFDeriv n).differentiableOn) hsub1
      (K := M / ρ ^ n) (fun w hw => ih w ρ hρ (by
        refine (closedBall_subset_closedBall' ?_).trans hsub
        rw [mem_closedBall] at hw
        push_cast; linarith))
    rw [pow_succ, ← div_div]; exact this

theorem hasSum_iteratedFDeriv_of_ball {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {f : E → B} {z0 : E} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball z0 R)) {y : E} (hy : ‖y‖ < R) :
    HasSum (fun n => (n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f z0 (fun _ => y)) (f (z0 + y)) := by
  have hR : 0 < R := (norm_nonneg y).trans_lt hy
  set L : ℂ →L[ℂ] E := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) y with hL
  have hLa : ∀ l : ℂ, L l = l • y := fun l => by simp [hL]
  set r : ℝ := 2 * R / (‖y‖ + R) with hr
  have hden : 0 < ‖y‖ + R := by positivity
  have h1r : (1:ℂ) ∈ ball (0:ℂ) r := by
    rw [mem_ball, dist_zero_right, norm_one, hr, lt_div_iff₀ hden]; linarith
  have hball : ∀ l ∈ ball (0:ℂ) r, z0 + L l ∈ ball z0 R := by
    intro l hl
    rw [mem_ball, dist_zero_right] at hl
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hLa, norm_smul]
    calc ‖l‖ * ‖y‖ ≤ r * ‖y‖ := by gcongr
      _ < R := by
        rw [hr, div_mul_eq_mul_div, div_lt_iff₀ hden]; nlinarith
  have hg : DifferentiableOn ℂ (fun l : ℂ => f (z0 + L l)) (ball (0:ℂ) r) := by
    intro l hl
    have h1 := (hf _ (hball l hl)).differentiableAt
    exact (h1.comp l ((L.differentiableAt).const_add z0)).differentiableWithinAt
  have hs := Complex.hasSum_taylorSeries_on_ball hg h1r
  have e1 : ∀ n, iteratedDeriv n (fun l : ℂ => f (z0 + L l)) 0 =
      iteratedFDeriv ℂ n f z0 (fun _ => y) := by
    intro n
    rw [iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_comp_affine_of_analytic isOpen_ball hf z0
      L n 0 (by rw [map_zero, add_zero]; exact mem_ball_self hR)]
    simp [hLa]
  simp only [e1, sub_zero, one_pow, one_smul] at hs
  rw [hLa, one_smul] at hs
  exact hs



theorem norm_taylorCoeff_le {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {f : E → B} {z0 : E}
    {R M s : ℝ} (hf : AnalyticOnNhd ℂ f (ball z0 R)) (hM : ∀ w ∈ ball z0 R, ‖f w‖ ≤ M)
    (hs : 0 < s) (hsR : s < R) (n : ℕ) :
    ‖(n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f z0‖ ≤ M * Real.exp 1 * (Real.exp 1 / s) ^ n := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z0 (mem_ball_self (hs.trans hsR)))
  have hn1 : (0:ℝ) < n + 1 := by positivity
  have hρ : 0 < s / (n + 1) := by positivity
  have hsub : closedBall z0 (n * (s / (n + 1))) ⊆ ball z0 R := by
    apply closedBall_subset_ball
    calc (n:ℝ) * (s / (n + 1)) ≤ s := by
          rw [mul_div_assoc', div_le_iff₀ hn1]; nlinarith
      _ < R := hsR
  have hD := norm_iteratedFDeriv_le_of_closedBall isOpen_ball hf hM n z0 _ hρ hsub
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hfac : ((n + 1 : ℝ)) ^ n / (n ! : ℝ) ≤ Real.exp 1 ^ (n + 1) := by
    have := Real.pow_div_factorial_le_exp ((n:ℝ) + 1) hn1.le (n + 1)
    rw [← Real.exp_nat_mul]
    push_cast at this ⊢
    calc ((n:ℝ) + 1) ^ n / (n ! : ℝ) = ((n:ℝ) + 1) ^ (n + 1) / ((n + 1) ! : ℝ) := by
          rw [Nat.factorial_succ]; push_cast
          field_simp
          ring
      _ ≤ Real.exp ((n:ℝ) + 1) := this
      _ = _ := by ring_nf
  have hfpos : (0:ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  calc (n ! : ℝ)⁻¹ * ‖iteratedFDeriv ℂ n f z0‖ ≤ (n ! : ℝ)⁻¹ * (M / (s / (n + 1)) ^ n) := by
        gcongr
    _ = M * (((n + 1 : ℝ)) ^ n / (n ! : ℝ)) / s ^ n := by
        rw [div_pow]; field_simp
    _ ≤ M * Real.exp 1 ^ (n + 1) / s ^ n := by gcongr
    _ = M * Real.exp 1 * (Real.exp 1 / s) ^ n := by rw [div_pow, pow_succ]; ring


theorem analyticAt_setIntegral_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℝ → ℂ} {z0 : E} {R : ℝ} {S : Set ℝ} (hS : MeasurableSet S) {M : ℝ → ℝ}
    (hM : IntegrableOn M S) (hR : 0 < R)
    (hf : ∀ t ∈ S, AnalyticOnNhd ℂ (fun z => f z t) (ball z0 R))
    (hb : ∀ t ∈ S, ∀ z ∈ ball z0 R, ‖f z t‖ ≤ M t)
    (hmeas : ∀ n, AEStronglyMeasurable (fun t => iteratedFDeriv ℂ n (fun z => f z t) z0)
      (volume.restrict S)) :
    AnalyticAt ℂ (fun z => ∫ t in S, f z t) z0 := by
  set e := Real.exp 1 with he
  have he0 : 0 < e := Real.exp_pos 1
  set s := R / 2 with hs
  have hs0 : 0 < s := by positivity
  have hsR : s < R := by rw [hs]; linarith
  set q : ℝ → (n : ℕ) → ContinuousMultilinearMap ℂ (fun _ : Fin n => E) ℂ :=
    fun t n => (n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n (fun z => f z t) z0 with hqdef
  have hq : ∀ n, ∀ᵐ t ∂(volume.restrict S), ‖q t n‖ ≤ M t * e * (e / s) ^ n := by
    intro n
    rw [ae_restrict_iff' hS]
    exact Filter.Eventually.of_forall fun t ht =>
      norm_taylorCoeff_le (hf t ht) (hb t ht) hs0 hsR n
  have hqint : ∀ n, Integrable (fun t => q t n) (volume.restrict S) := fun n =>
    Integrable.mono' (hM.mul_const (e * (e / s) ^ n)) ((hmeas n).const_smul ((n ! : ℂ)⁻¹))
      (by filter_upwards [hq n] with t ht; rwa [mul_assoc] at ht)
  set Q : FormalMultilinearSeries ℂ E ℂ := fun n => ∫ t in S, q t n with hQdef
  set IM := ∫ t in S, M t with hIM
  have hIM0 : 0 ≤ IM := setIntegral_nonneg_of_ae_restrict (by
    rw [Filter.EventuallyLE, ae_restrict_iff' hS]
    exact Filter.Eventually.of_forall fun t ht =>
      (norm_nonneg _).trans (hb t ht z0 (mem_ball_self hR)))
  have hQ : ∀ n, ‖Q n‖ ≤ IM * e * (e / s) ^ n := by
    intro n
    have := norm_integral_le_of_norm_le (hM.mul_const (e * (e / s) ^ n))
      (by filter_upwards [hq n] with t ht; rw [mul_assoc] at ht; exact ht)
    rw [integral_mul_const] at this
    rw [mul_assoc]; exact this
  set r : NNReal := Real.toNNReal (s / (2 * e)) with hr
  have hrr : (r:ℝ) = s / (2 * e) := Real.coe_toNNReal _ (by positivity)
  have hrpos : (0:ℝ) < r := by rw [hrr]; positivity
  refine ⟨Q, r, ?_⟩
  refine
    { r_le := ?_
      r_pos := by simpa using hrpos
      hasSum := ?_ }
  · refine Q.le_radius_of_bound (IM * e) fun n => ?_
    calc ‖Q n‖ * (r:ℝ) ^ n ≤ IM * e * (e / s) ^ n * (r:ℝ) ^ n := by gcongr; exact hQ n
      _ = IM * e * (1/2) ^ n := by
          rw [mul_assoc, ← mul_pow, hrr]; congr 2; field_simp
      _ ≤ IM * e * 1 := by
          gcongr; exact pow_le_one₀ (by norm_num) (by norm_num)
      _ = IM * e := mul_one _
  · intro y hy
    rw [Metric.eball_coe, mem_ball, dist_zero_right] at hy
    have hyr : ‖y‖ < s / (2 * e) := by rw [← hrr]; exact hy
    have hyR : ‖y‖ < R := by
      have : s / (2 * e) ≤ s := by
        rw [div_le_iff₀ (by positivity)]
        have : (1:ℝ) ≤ e := by rw [he]; exact Real.one_le_exp (by norm_num)
        nlinarith
      linarith
    set ρ := e * ‖y‖ / s with hρ
    have hρ0 : 0 ≤ ρ := by positivity
    have hρ1 : ρ < 1 := by
      rw [hρ, div_lt_one hs0]
      rw [lt_div_iff₀ (by positivity)] at hyr
      nlinarith
    have hQy : ∀ n, Q n (fun _ => y) = ∫ t in S, q t n (fun _ => y) := fun n =>
      ContinuousMultilinearMap.integral_apply (hqint n) _
    simp only [hQy]
    refine hasSum_integral_of_dominated_convergence (fun n t => M t * e * ρ ^ n) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) ℂ (fun _ => y)).continuous
        |>.comp_aestronglyMeasurable (hqint n).aestronglyMeasurable
    · intro n
      filter_upwards [hq n] with t ht
      calc ‖q t n (fun _ => y)‖ ≤ ‖q t n‖ * ∏ _i : Fin n, ‖y‖ := (q t n).le_opNorm _
        _ = ‖q t n‖ * ‖y‖ ^ n := by simp
        _ ≤ M t * e * (e / s) ^ n * ‖y‖ ^ n := by gcongr
        _ = M t * e * ρ ^ n := by rw [hρ, mul_assoc, ← mul_pow]; ring_nf
    · exact Filter.Eventually.of_forall fun t =>
        (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
    · have : (fun t => ∑' n, M t * e * ρ ^ n) = fun t => M t * e * (1 - ρ)⁻¹ := by
        funext t; rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
      rw [this]
      exact (hM.mul_const _).mul_const _
    · rw [ae_restrict_iff' hS]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have := hasSum_iteratedFDeriv_of_ball (hf t ht) hyR
      simpa [hqdef] using this


theorem exists_ball_bound_of_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {G : E × ℂ → ℂ} {z1 : E} {a b : ℝ}
    (h : ∀ t ∈ Set.Icc a b, AnalyticAt ℂ G (z1, (t:ℂ))) :
    ∃ r0 > 0, ∃ M0, 0 ≤ M0 ∧ ∀ z ∈ ball z1 r0, ∀ t ∈ Set.Icc a b,
      AnalyticAt ℂ G (z, (t:ℂ)) ∧ ‖G (z, (t:ℂ))‖ ≤ M0 := by
  set Ω := {x : E × ℂ | AnalyticAt ℂ G x} with hΩ
  have hΩo : IsOpen Ω := isOpen_analyticAt ℂ G
  have hGc : ContinuousOn G Ω := fun x hx => (hx : AnalyticAt ℂ G x).continuousAt.continuousWithinAt
  set K := (fun t : ℝ => (z1, (t:ℂ))) '' Set.Icc a b with hK
  have hKc : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hKΩ : K ⊆ Ω := by
    rintro _ ⟨t, ht, rfl⟩; exact h t ht
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hGc.mono hKΩ)
  set W := Ω ∩ G ⁻¹' (ball (0:ℂ) (|C| + 1)) with hW
  have hWo : IsOpen W := hGc.isOpen_inter_preimage hΩo isOpen_ball
  have hKW : K ⊆ W := by
    intro x hx
    refine ⟨hKΩ hx, ?_⟩
    simp only [Set.mem_preimage, mem_ball, dist_zero_right]
    linarith [hC x hx, le_abs_self C]
  obtain ⟨r0, hr0, hth⟩ := hKc.exists_thickening_subset_open hWo hKW
  refine ⟨r0, hr0, |C| + 1, by positivity, fun z hz t ht => ?_⟩
  have hmem : (z, (t:ℂ)) ∈ W := by
    apply hth
    rw [mem_thickening_iff]
    refine ⟨(z1, (t:ℂ)), ⟨t, ht, rfl⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact hz
  refine ⟨hmem.1, ?_⟩
  have := hmem.2
  simp only [Set.mem_preimage, mem_ball, dist_zero_right] at this
  exact this.le

theorem continuousOn_iteratedFDeriv_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {G : E × ℂ → ℂ} {z0 : E} {T : Set ℝ} (h : ∀ t ∈ T, AnalyticAt ℂ G (z0, (t:ℂ))) (n : ℕ) :
    ContinuousOn (fun t : ℝ => iteratedFDeriv ℂ n (fun z => G (z, (t:ℂ))) z0) T := by
  set Ω := {x : E × ℂ | AnalyticAt ℂ G x} with hΩ
  have hΩo : IsOpen Ω := isOpen_analyticAt ℂ G
  have hGa : AnalyticOnNhd ℂ G Ω := fun x hx => hx
  have e : ∀ t ∈ T, iteratedFDeriv ℂ n (fun z => G (z, (t:ℂ))) z0 =
      ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin n => ContinuousLinearMap.inl ℂ E ℂ)
        (iteratedFDeriv ℂ n G (z0, (t:ℂ))) := by
    intro t ht
    have := iteratedFDeriv_comp_affine_of_analytic hΩo hGa ((0:E), (t:ℂ))
      (ContinuousLinearMap.inl ℂ E ℂ) n z0 (by
        show AnalyticAt ℂ G _
        simpa using h t ht)
    have e2 : (fun a => G (((0:E), (t:ℂ)) + ContinuousLinearMap.inl ℂ E ℂ a)) =
        fun z => G (z, (t:ℂ)) := by
      funext a; simp
    rw [e2] at this
    rw [this]
    simp
  refine ContinuousOn.congr ?_ e
  refine (ContinuousMultilinearMap.compContinuousLinearMapL _).continuous.comp_continuousOn ?_
  intro t ht
  have hc : ContinuousAt (iteratedFDeriv ℂ n G) (z0, (t:ℂ)) :=
    ((hGa.iteratedFDeriv n) _ (h t ht)).continuousAt
  have hc2 : ContinuousAt (fun t : ℝ => (z0, (t:ℂ))) t := by fun_prop
  exact (ContinuousAt.comp (g := iteratedFDeriv ℂ n G) (f := fun t : ℝ => (z0, (t:ℂ))) (x := t) hc hc2).continuousWithinAt


theorem integrableOn_rpow_mul_one_sub_log_pow {p : ℝ} (hp : -1 < p) (m : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ p * (1 - Real.log t) ^ m) (Set.Ioo 0 1) := by
  have hp' : 0 < p + 1 := by linarith
  set K := (2:ℝ) ^ m * (1 + (m ! : ℝ) / ((p + 1) / 2) ^ m) with hK
  have hint : IntegrableOn (fun t : ℝ => K * t ^ ((p - 1) / 2)) (Set.Ioo 0 1) := by
    have h1 := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := (p - 1) / 2)
      (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h1
    exact h1.const_mul K
  refine hint.mono' ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact (measurable_id.pow_const p).mul ((measurable_const.sub Real.measurable_log).pow_const m)
  · rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht0 := ht.1
    have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht.2.le
    have hnn : 0 ≤ t ^ p * (1 - Real.log t) ^ m :=
      mul_nonneg (Real.rpow_nonneg ht0.le _) (pow_nonneg (by linarith) _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hab := power_log_absorb ht0 ht.2.le hp' m
    have e1 : t ^ (p + 1) = t ^ p * t := by rw [Real.rpow_add ht0, Real.rpow_one]
    have e2 : t ^ ((p + 1) / 2) = t ^ ((p - 1) / 2) * t := by
      rw [← Real.rpow_add_one ht0.ne']; ring_nf
    rw [e1, e2] at hab
    have : t * (t ^ p * (1 - Real.log t) ^ m) ≤ t * (K * t ^ ((p - 1) / 2)) := by
      rw [hK]; nlinarith
    exact le_of_mul_le_mul_left this ht0

theorem integrableOn_one_sub_rpow_mul_log_pow {q : ℝ} (hq : -1 < q) (n : ℕ) :
    IntegrableOn (fun t : ℝ => (1 - t) ^ q * (1 - Real.log (1 - t)) ^ n) (Set.Ioo 0 1) := by
  have h := integrableOn_rpow_mul_one_sub_log_pow hq n
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h ⊢
  have := h.comp_sub_left 1
  simpa using this.symm


/-- Common core of the two parametric analyticity results (same statement as
`parametric_endpoint_analytic_nd`). -/
theorem parametric_endpoint_analytic_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} (hU : IsOpen U) {F : E → ℂ → ℂ}
    {δ p q C D : ℝ} {m n : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hp : -1 < p) (hq : -1 < q) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : AnalyticOnNhd ℂ (fun s : E × ℂ => F s.1 s.2)
      (U ×ˢ (Complex.ofReal '' Set.Ioo (0:ℝ) 1)))
    (hleft : ∀ z ∈ U, ∀ t ∈ Set.Ioo (0:ℝ) δ,
      ‖F z t‖ ≤ C*t^p*(1-Real.log t)^m)
    (hright : ∀ z ∈ U, ∀ t ∈ Set.Ioo (0:ℝ) δ,
      ‖F z (1-t)‖ ≤ D*t^q*(1-Real.log t)^n) :
    AnalyticOnNhd ℂ (fun z => ∫ t in (0:ℝ)..1, F z t) U ∧
      ∀ z ∈ U, IntervalIntegrable (fun t : ℝ => F z t) volume 0 1 := by
  set G : E × ℂ → ℂ := fun s => F s.1 s.2 with hG
  have hA : ∀ z ∈ U, ∀ t ∈ Set.Ioo (0:ℝ) 1, AnalyticAt ℂ G (z, (t:ℂ)) :=
    fun z hz t ht => hF (z, (t:ℂ)) ⟨hz, t, ht, rfl⟩
  have key : ∀ z1 ∈ U, ∃ r0 > 0, ball z1 r0 ⊆ U ∧ ∃ Mf : ℝ → ℝ,
      IntegrableOn Mf (Set.Ioo 0 1) ∧
      ∀ t ∈ Set.Ioo (0:ℝ) 1, ∀ z ∈ ball z1 r0, ‖F z t‖ ≤ Mf t := by
    intro z1 hz1
    obtain ⟨R1, hR1, hR1U⟩ := Metric.isOpen_iff.1 hU z1 hz1
    obtain ⟨r1, hr1, M0, hM0, hb0⟩ := exists_ball_bound_of_analyticAt (G := G) (z1 := z1)
      (a := δ) (b := 1 - δ) (fun t ht => hA z1 hz1 t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    refine ⟨min R1 r1, lt_min hR1 hr1, (ball_subset_ball (min_le_left _ _)).trans hR1U,
      fun t => C * (t ^ p * (1 - Real.log t) ^ m) +
        D * ((1 - t) ^ q * (1 - Real.log (1 - t)) ^ n) + M0, ?_, ?_⟩
    · refine (((integrableOn_rpow_mul_one_sub_log_pow hp m).const_mul C).add
        ((integrableOn_one_sub_rpow_mul_log_pow hq n).const_mul D)).add ?_
      exact integrableOn_const (by simp)
    · intro t ht z hz
      have hzU : z ∈ U := hR1U (ball_subset_ball (min_le_left _ _) hz)
      have hz1 : z ∈ ball z1 r1 := ball_subset_ball (min_le_right _ _) hz
      have h1 : 0 ≤ C * (t ^ p * (1 - Real.log t) ^ m) := by
        have := Real.log_nonpos ht.1.le ht.2.le
        exact mul_nonneg hC (mul_nonneg (Real.rpow_nonneg ht.1.le _) (pow_nonneg (by linarith) _))
      have h2 : 0 ≤ D * ((1 - t) ^ q * (1 - Real.log (1 - t)) ^ n) := by
        have := Real.log_nonpos (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) (by linarith [ht.1])
        exact mul_nonneg hD (mul_nonneg (Real.rpow_nonneg (by linarith [ht.2]) _)
          (pow_nonneg (by linarith) _))
      rcases lt_or_ge t δ with hlt | hge
      · have := hleft z hzU t ⟨ht.1, hlt⟩
        rw [mul_assoc] at this
        linarith
      rcases lt_or_ge (1 - δ) t with hlt2 | hge2
      · have := hright z hzU (1 - t) ⟨by linarith [ht.2], by linarith⟩
        have e : (1:ℂ) - ((1 - t : ℝ) : ℂ) = (t:ℂ) := by push_cast; ring
        rw [e, mul_assoc] at this
        linarith
      · have := (hb0 z hz1 t ⟨hge, hge2⟩).2
        simp only [hG] at this
        linarith
  constructor
  · intro z0 hz0
    obtain ⟨r0, hr0, hsub, Mf, hMf, hb⟩ := key z0 hz0
    have hcore := analyticAt_setIntegral_of_bound (f := fun z (t:ℝ) => F z t) (z0 := z0)
      (R := r0) measurableSet_Ioo hMf hr0
      (fun t ht z hz => AnalyticAt.comp (g := G) (f := fun z : E => (z, (t:ℂ))) (x := z)
        (hA z (hsub hz) t ht) (AnalyticAt.prod analyticAt_id analyticAt_const)) hb
      (fun n => (continuousOn_iteratedFDeriv_slice (G := G) (fun t ht => hA z0 hz0 t ht)
        n).aestronglyMeasurable measurableSet_Ioo)
    have e : (fun z => ∫ t in (0:ℝ)..1, F z t) = fun z => ∫ t in Set.Ioo (0:ℝ) 1, F z t := by
      funext z
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    rw [e]; exact hcore
  · intro z hz
    obtain ⟨r0, hr0, hsub, Mf, hMf, hb⟩ := key z hz
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    refine hMf.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioo
      have hc2 : ContinuousAt (fun t : ℝ => (z, (t:ℂ))) t := by fun_prop
      exact (ContinuousAt.comp (g := G) (f := fun t : ℝ => (z, (t:ℂ))) (x := t)
        (hA z hz t ht).continuousAt hc2).continuousWithinAt
    · rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun t ht => hb t ht z (mem_ball_self hr0)


end ParamAnalytic

/-- General parameter spaces are necessary for genuinely nested integrals. -/
theorem parametric_finite_analytic_nd {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {S : Set E} {F : E → ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : E × ℂ => F p.1 p.2)
      (S ×ˢ (Complex.ofReal '' Set.Icc (0:ℝ) 1))) :
    AnalyticOnNhd ℂ (fun z => ∫ t in (0:ℝ)..1, F z t) S := by
  intro z0 hz0
  obtain ⟨r0, hr0, M0, hM0, hball⟩ := exists_ball_bound_of_analyticAt
    (G := fun s : E × ℂ => F s.1 s.2) (z1 := z0) (a := 0) (b := 1)
    (fun t ht => hF _ ⟨hz0, t, ht, rfl⟩)
  refine (parametric_endpoint_analytic_aux (U := Metric.ball z0 r0) Metric.isOpen_ball (F := F)
    (δ := 1/2) (p := 0) (q := 0) (C := M0) (D := M0) (m := 0) (n := 0) (by norm_num) le_rfl
    (by norm_num) (by norm_num) hM0 hM0 ?_ ?_ ?_).1 z0 (Metric.mem_ball_self hr0)
  · rintro ⟨z, w⟩ ⟨hz, t, ht, rfl⟩
    exact (hball z hz t ⟨ht.1.le, ht.2.le⟩).1
  · intro z hz t ht
    simp only [Real.rpow_zero, pow_zero, mul_one]
    exact (hball z hz t ⟨ht.1.le, by linarith [ht.2]⟩).2
  · intro z hz t ht
    have := (hball z hz (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).2
    simp only [Real.rpow_zero, pow_zero, mul_one]
    push_cast at this
    exact this

/-- Uniform power/log majorants justify holomorphic dependence through an
improper inner integral; pointwise convergence is not a sufficient hypothesis. -/
theorem parametric_endpoint_analytic_nd {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} (hU : IsOpen U) {F : E → ℂ → ℂ}
    {δ p q C D : ℝ} {m n : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hp : -1 < p) (hq : -1 < q) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : AnalyticOnNhd ℂ (fun s : E × ℂ => F s.1 s.2)
      (U ×ˢ (Complex.ofReal '' Set.Ioo (0:ℝ) 1)))
    (hleft : ∀ z ∈ U, ∀ t ∈ Set.Ioo (0:ℝ) δ,
      ‖F z t‖ ≤ C*t^p*(1-Real.log t)^m)
    (hright : ∀ z ∈ U, ∀ t ∈ Set.Ioo (0:ℝ) δ,
      ‖F z (1-t)‖ ≤ D*t^q*(1-Real.log t)^n) :
    AnalyticOnNhd ℂ (fun z => ∫ t in (0:ℝ)..1, F z t) U ∧
      ∀ z ∈ U, IntervalIntegrable (fun t : ℝ => F z t) volume 0 1 := by
  exact parametric_endpoint_analytic_aux hU hδ hδ1 hp hq hC hD hF hleft hright

end Intgrl
