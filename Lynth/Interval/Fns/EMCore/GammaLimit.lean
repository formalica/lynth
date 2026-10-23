module

import all Lynth.Interval.Fns.EMCore.Gamma

/-!
# Complex Stirling formula (exponential form) with explicit remainder
-/

open Real Complex intervalIntegral Nat Filter Topology

namespace EMCore

lemma log_factorial_eq {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) = Real.log (Stirling.stirlingSeq n) + (1/2) * Real.log 2
      + (1/2) * Real.log n + n * Real.log n - n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hf : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hsq : 0 < Real.sqrt (2 * n) := Real.sqrt_pos.2 (by positivity)
  have hp : 0 < ((n:ℝ) / Real.exp 1) ^ n := by positivity
  unfold Stirling.stirlingSeq
  rw [Real.log_div hf.ne' (by positivity), Real.log_mul hsq.ne' hp.ne', Real.log_pow,
    Real.log_div hn0.ne' (Real.exp_pos 1).ne', Real.log_exp, Real.log_sqrt (by positivity),
    Real.log_mul (by norm_num) hn0.ne']
  ring

lemma tendsto_log_stirlingSeq :
    Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) :=
  (Real.continuousAt_log (Real.sqrt_pos.2 Real.pi_pos).ne').tendsto.comp
    Stirling.tendsto_stirlingSeq_sqrt_pi

lemma tendsto_aux (w : ℂ) :
    Tendsto (fun n : ℕ => ((n : ℂ) + 1/2 + w) * Complex.log (1 + (1 + w) / n)) atTop
      (𝓝 (1 + w)) := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℂ) / n) atTop (𝓝 0) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat).ofReal
    simpa using this
  have hu : Tendsto (fun n : ℕ => (1 + w) / (n : ℂ)) atTop (𝓝 0) := by
    have := hinv.const_mul (1 + w)
    rw [mul_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have hmain : Tendsto (fun n : ℕ => ((n : ℂ) + 1/2 + w) * ((1 + w) / n)) atTop
      (𝓝 (1 + w)) := by
    have h1 : Tendsto (fun n : ℕ => (1 + w) * (1 + (1/2 + w) * (1 / (n : ℂ)))) atTop
        (𝓝 ((1 + w) * (1 + (1/2 + w) * 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv))
    simp only [mul_zero, add_zero, mul_one] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp
    ring
  have herr : Tendsto (fun n : ℕ => ((n : ℂ) + 1/2 + w) *
      (Complex.log (1 + (1 + w) / n) - (1 + w) / n)) atTop (𝓝 0) := by
    have hnu : Tendsto (fun n : ℕ => ‖(1 + w) / (n : ℂ)‖) atTop (𝓝 0) := by
      simpa using hu.norm
    have hbound : Tendsto (fun n : ℕ => ‖((n : ℂ) + 1/2 + w) * ((1 + w) / n)‖ *
        ‖(1 + w) / (n : ℂ)‖ * (1 - ‖(1 + w) / (n : ℂ)‖)⁻¹ / 2) atTop
        (𝓝 (‖1 + w‖ * 0 * (1 - 0)⁻¹ / 2)) :=
      ((hmain.norm.mul hnu).mul ((tendsto_const_nhds.sub hnu).inv₀ (by norm_num))).div_const 2
    simp only [mul_zero, zero_mul, zero_div] at hbound
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hnu.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with n hn
    rw [norm_mul]
    have hl := Complex.norm_log_one_add_sub_self_le (z := (1 + w) / n) (by linarith)
    calc ‖(n : ℂ) + 1/2 + w‖ * ‖Complex.log (1 + (1 + w) / n) - (1 + w) / n‖
        ≤ ‖(n : ℂ) + 1/2 + w‖ * (‖(1 + w) / (n : ℂ)‖ ^ 2 * (1 - ‖(1 + w) / (n : ℂ)‖)⁻¹ / 2) :=
          mul_le_mul_of_nonneg_left hl (norm_nonneg _)
      _ = _ := by rw [norm_mul]; ring
  have := hmain.add herr
  simp only [add_zero] at this
  refine this.congr (fun n => ?_)
  ring

lemma tendsto_A {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun n : ℕ => w * Complex.log n + Complex.log (n.factorial : ℂ)
      - ((n:ℂ) + 1 + w) * Complex.log ((n:ℂ) + 1 + w) + ((n:ℂ) + 1)
      + Complex.log ((n:ℂ) + 1 + w) / 2) atTop
      (𝓝 ((Real.log (Real.sqrt (2 * Real.pi)) : ℂ) - w)) := by
  have hlim : Tendsto (fun n : ℕ => ((Real.log (Stirling.stirlingSeq n) : ℝ) : ℂ)
      + (1/2) * (Real.log 2 : ℂ) + 1 - ((n : ℂ) + 1/2 + w) * Complex.log (1 + (1 + w) / n))
      atTop (𝓝 (((Real.log (Real.sqrt Real.pi)) : ℂ) + (1/2) * (Real.log 2 : ℂ) + 1 - (1 + w))) :=
    ((tendsto_log_stirlingSeq.ofReal.add tendsto_const_nhds).add tendsto_const_nhds).sub
      (tendsto_aux w)
  have hc : ((Real.log (Real.sqrt Real.pi)) : ℂ) + (1/2) * (Real.log 2 : ℂ) + 1 - (1 + w)
      = (Real.log (Real.sqrt (2 * Real.pi)) : ℂ) - w := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.log_mul (by positivity)
      (Real.sqrt_pos.2 Real.pi_pos).ne', Real.log_sqrt (x := 2) (by norm_num)]
    push_cast; ring
  rw [hc] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hfac : Complex.log (n.factorial : ℂ) = ((Real.log (n.factorial : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; simp
  have hlogn : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hn0.le]; simp
  have hx : (1 + (1 + w) / n) ≠ 0 := by
    intro h
    have h2 : (n : ℂ) + 1 + w = 0 := by
      have := congrArg (· * (n : ℂ)) h
      simp only [zero_mul, add_mul, one_mul, div_mul_cancel₀ _ hnc] at this
      linear_combination this
    have := congrArg Complex.re h2
    simp at this
    linarith
  have hsplit : Complex.log ((n:ℂ) + 1 + w)
      = ((Real.log n : ℝ) : ℂ) + Complex.log (1 + (1 + w) / n) := by
    rw [← Complex.log_mul_ofReal n hn0 _ hx]
    congr 1
    rw [Complex.ofReal_natCast]
    field_simp
    ring
  rw [hfac, hlogn, hsplit, log_factorial_eq hn]
  push_cast
  ring

lemma integral_log_add {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    ∫ x in (0:ℝ)..n, Complex.log ((x : ℂ) + w)
      = ((n : ℂ) + w) * Complex.log ((n : ℂ) + w) - n - w * Complex.log w := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) n,
      HasDerivAt (fun y : ℝ => ((y : ℂ) + w) * Complex.log ((y : ℂ) + w) - y)
      (Complex.log ((x : ℂ) + w)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by positivity)] at hx
    have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) + w) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp.add_const w
    have hl := hlin.clog_real (slit_of_re hw hx.1)
    have hne : (x : ℂ) + w ≠ 0 := slitPlane_ne_zero (slit_of_re hw hx.1)
    have hsub := (hlin.mul hl).sub (hasDerivAt_id x).ofReal_comp
    have hfun : (fun y : ℝ => ((y : ℂ) + w) * Complex.log ((y : ℂ) + w) - y)
        = (((fun y : ℝ => (y : ℂ) + w) * fun (t : ℝ) => Complex.log ((t : ℂ) + w))
          - fun (y : ℝ) => ((id y : ℝ) : ℂ)) := by
      funext y
      simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
    rw [hfun]
    convert hsub using 1
    field_simp
    simp
  rw [integral_eq_sub_of_hasDerivAt hd]
  · simp
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by positivity)] at hx
    have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) + w) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp.add_const w
    exact (hlin.clog_real (slit_of_re hw hx.1)).continuousAt.continuousWithinAt

lemma gammaSeq_eq_exp {w : ℂ} (hw : 0 < w.re) {n : ℕ} (hn : 1 ≤ n) :
    Complex.GammaSeq w n = Complex.exp (w * Complex.log n + Complex.log (n.factorial : ℂ)
      - ∑ j ∈ Finset.range (n + 1), Complex.log (w + j)) := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hfc : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [Complex.exp_sub, Complex.exp_add, Complex.exp_sum, Complex.exp_log hfc]
  rw [Complex.GammaSeq, Complex.cpow_def_of_ne_zero hnc, mul_comm (Complex.log n) w]
  congr 1
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Complex.exp_log]
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]

lemma gF_odd_tendsto {w : ℂ} (hw : 0 < w.re) (j : ℕ) :
    Tendsto (fun n : ℕ => gF w (2 * j + 1) ((0:ℝ) + ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => ((2 * j) ! : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul ((2 * j) ! : ℝ)
    rw [mul_zero] at this
    refine this.congr (fun n => ?_)
    push_cast; ring
  refine squeeze_zero_norm (fun n => ?_) hb
  have hx : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hge : ((n + 1 : ℕ) : ℝ) ≤ ‖(((n + 1 : ℕ) : ℝ) : ℂ) + w‖ := by
    have := Complex.re_le_norm ((((n + 1 : ℕ) : ℝ) : ℂ) + w)
    simp at this ⊢
    linarith
  have hge1 : (1:ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have : (1:ℝ) ≤ (n:ℝ) + 1 := by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    simp only [Nat.cast_add, Nat.cast_one]; exact this
  simp only [zero_add, gF, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]
  apply div_le_div_of_nonneg_left (by positivity) hx
  calc ((n + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) ^ 1 := (pow_one _).symm
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ (2 * j + 1) := pow_le_pow_right₀ hge1 (by omega)
    _ ≤ _ := pow_le_pow_left₀ hx.le hge _

/-- The Stirling exponent with explicit Euler–Maclaurin remainder. -/
noncomputable def stirlingPhi (w : ℂ) (N : ℕ) : ℂ :=
  (w - 1 / 2) * Complex.log w - w + Complex.log (Real.sqrt (2 * Real.pi))
    + (∑ k ∈ Finset.range (N - 1),
        ((bernoulli (2 * (k + 1)) : ℚ) : ℂ)
          / ((2 * ((k + 1) : ℂ)) * (2 * ((k + 1) : ℂ) - 1) * w ^ (2 * (k + 1) - 1)))
    + gammaR w N

lemma corr_term_eq {w : ℂ} (hw : 0 < w.re) (j : ℕ) :
    (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ) * gF w (2 * j + 1) 0
      = ((bernoulli (2 * (j + 1)) : ℚ) : ℂ)
          / ((2 * ((j + 1) : ℂ)) * (2 * ((j + 1) : ℂ) - 1) * w ^ (2 * (j + 1) - 1)) := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have e : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have hf : ((2 * (j + 1)) ! : ℂ) = (2 * ((j:ℂ) + 1)) * (2 * ((j:ℂ) + 1) - 1) * ((2 * j) ! : ℂ) := by
    have : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
    rw [this, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  simp only [gF, e, Complex.ofReal_zero, zero_add]
  push_cast
  rw [hf, pow_mul, neg_one_sq, one_pow, one_mul]
  have : ((2 * j) ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2 : (2 * ((j:ℂ) + 1)) ≠ 0 := by
    have : (2 * ((j:ℂ) + 1)) = ((2 * (j + 1) : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast (by omega : 2 * (j + 1) ≠ 0)
  have h3 : (2 * ((j:ℂ) + 1) - 1) ≠ 0 := by
    have : (2 * ((j:ℂ) + 1) - 1) = ((2 * j + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast (by omega : 2 * j + 1 ≠ 0)
  field_simp

/-- **Complex Stirling formula** (exponential form) with Euler–Maclaurin remainder,
valid for `0 < Re w`. -/
theorem gamma_eq_exp_stirlingPhi {w : ℂ} (hw : 0 < w.re) {N : ℕ} (hN : 1 ≤ N) :
    Complex.Gamma w = Complex.exp (stirlingPhi w N) := by
  obtain ⟨hs, -⟩ := gammaR_summable_bound hw hN
  -- the exponent of `GammaSeq`
  set E : ℕ → ℂ := fun n => w * Complex.log n + Complex.log (n.factorial : ℂ)
      - ∑ j ∈ Finset.range (n + 1), Complex.log (w + j) with hE
  have hEM : ∀ n : ℕ, E n =
      (w * Complex.log n + Complex.log (n.factorial : ℂ)
        - ((n:ℂ) + 1 + w) * Complex.log ((n:ℂ) + 1 + w) + ((n:ℂ) + 1)
        + Complex.log ((n:ℂ) + 1 + w) / 2)
      + (w * Complex.log w - Complex.log w / 2)
      - ∑ j ∈ Finset.range (N - 1),
          (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
            * gF w (2 * j + 1) ((0:ℝ) + ((n + 1 : ℕ) : ℝ))
      + ∑ j ∈ Finset.range (N - 1),
          (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ) * gF w (2 * j + 1) 0
      + ∑ k ∈ Finset.range (n + 1), emR (gF w) (2 * N) k := by
    intro n
    have hsum := em_sum (gF_gchain hw) N hN (n + 1)
    have hl : ∑ k ∈ Finset.range (n + 1), gF w 0 ((0:ℝ) + k)
        = ∑ j ∈ Finset.range (n + 1), Complex.log (w + j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [gF, add_comm]
    rw [hl] at hsum
    have hint : ∫ x in (0:ℝ)..((n + 1 : ℕ) : ℝ), gF w 0 x
        = (((n + 1 : ℕ) : ℂ) + w) * Complex.log (((n + 1 : ℕ) : ℂ) + w) - ((n + 1 : ℕ) : ℂ)
          - w * Complex.log w := integral_log_add hw (n + 1)
    simp only [zero_add] at hsum
    rw [hint] at hsum
    simp only [hE]
    rw [hsum]
    have hsplit : ∑ x ∈ Finset.range (N - 1),
          (((bernoulli (2 * (x + 1)) : ℝ) / ((2 * (x + 1)) ! : ℝ) : ℝ) : ℂ)
            * (gF w (2 * x + 1) ((n + 1 : ℕ) : ℝ) - gF w (2 * x + 1) 0)
        = ∑ x ∈ Finset.range (N - 1),
          (((bernoulli (2 * (x + 1)) : ℝ) / ((2 * (x + 1)) ! : ℝ) : ℝ) : ℂ)
            * gF w (2 * x + 1) ((n + 1 : ℕ) : ℝ)
          - ∑ x ∈ Finset.range (N - 1),
          (((bernoulli (2 * (x + 1)) : ℝ) / ((2 * (x + 1)) ! : ℝ) : ℝ) : ℂ)
            * gF w (2 * x + 1) 0 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [hsplit]
    have g0 : ∀ x : ℝ, gF w 0 x = Complex.log ((x : ℂ) + w) := fun _ => rfl
    simp only [g0, zero_add, Complex.ofReal_zero]
    push_cast
    ring
  have hlim : Tendsto E atTop (𝓝 (stirlingPhi w N)) := by
    have h1 := tendsto_A hw
    have h2 : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (N - 1),
          (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
            * gF w (2 * j + 1) ((0:ℝ) + ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.range (N - 1)) (fun j _ =>
        (gF_odd_tendsto hw j).const_mul
          (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ))
      simp only [mul_zero, Finset.sum_const_zero] at this
      exact this
    have h3 : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), emR (gF w) (2 * N) k) atTop
        (𝓝 (gammaR w N)) :=
      hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have := (((h1.add (tendsto_const_nhds (x := w * Complex.log w - Complex.log w / 2))).sub
      h2).add (tendsto_const_nhds (x := ∑ j ∈ Finset.range (N - 1),
          (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
            * gF w (2 * j + 1) 0))).add h3
    convert this using 1
    · funext n; exact hEM n
    · unfold stirlingPhi
      rw [Finset.sum_congr rfl (fun j _ => (corr_term_eq hw j).symm)]
      rw [← Complex.ofReal_log (Real.sqrt_nonneg _)]
      ring_nf
  have hG := Complex.GammaSeq_tendsto_Gamma w
  have hG2 : Tendsto (Complex.GammaSeq w) atTop (𝓝 (Complex.exp (stirlingPhi w N))) := by
    refine ((Complex.continuous_exp.tendsto _).comp hlim).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp, hE]
    exact (gammaSeq_eq_exp hw hn).symm
  exact tendsto_nhds_unique hG hG2

end EMCore
