module

import all Lynth.Interval.Fns.EMCore.EulerMaclaurin

/-!
# Euler–Maclaurin for `x ↦ x^{-s}`: the zeta remainder
-/

open Real Complex intervalIntegral Nat Filter Topology

namespace EMCore

/-- Rising factorial `s (s+1) ⋯ (s+m-1)`. -/
noncomputable def pochC (s : ℂ) (m : ℕ) : ℂ := ∏ j ∈ Finset.range m, (s + (j : ℂ))

/-- The derivative chain of `x ↦ x^{-s}`. -/
noncomputable def zF (s : ℂ) (m : ℕ) (x : ℝ) : ℂ :=
  (-1) ^ m * pochC s m * (x : ℂ) ^ (-s - m)

lemma zF_chain (s : ℂ) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (zF s m) (zF s (m + 1) x) x := by
  have hslit : (x : ℂ) ∈ slitPlane := Or.inl (by simpa using hx)
  have h := ((Complex.hasStrictDerivAt_cpow_const (c := -s - m) hslit).hasDerivAt).comp_ofReal
  have h2 := h.const_mul ((-1) ^ m * pochC s m)
  unfold zF
  convert h2 using 1
  unfold pochC
  rw [Finset.prod_range_succ]
  push_cast
  have : -s - ((m : ℂ) + 1) = -s - m - 1 := by ring
  rw [this]
  ring

lemma zF_gchain (s : ℂ) {a : ℝ} (ha : 0 < a) : GChain (zF s) a :=
  fun m x hx => zF_chain s m (x := x) (lt_of_lt_of_le ha hx)

lemma norm_zF {s : ℂ} (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖zF s m x‖ = ‖pochC s m‖ * x ^ (-(s.re + m)) := by
  unfold zF
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 2
  simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
  ring

/-- `∫_b^{b+1} x^{-(q+1)} = h(b) - h(b+1)` with `h(y) = y^{-q} / q`, for real `q > 0`. -/
lemma integral_rpow_unit {q : ℝ} (hq : 0 < q) {b : ℝ} (hb : 0 < b) :
    ∫ x in b..b + 1, x ^ (-(q + 1)) = b ^ (-q) / q - (b + 1) ^ (-q) / q := by
  have hd : ∀ x ∈ Set.uIcc b (b + 1), HasDerivAt (fun y : ℝ => -(y ^ (-q) / q)) (x ^ (-(q + 1))) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    have := ((Real.hasDerivAt_rpow_const (p := -q) (Or.inl hx0.ne')).div_const q).neg
    convert this using 1
    have : -q - 1 = -(q + 1) := by ring
    rw [this]
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hd]
  · ring
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    exact (Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne')).continuousWithinAt

/-- Per-interval bound for the zeta remainder. -/
lemma norm_emR_zF_le {s : ℂ} {M : ℕ} {b : ℝ} (hb : 0 < b) (hσ : 0 < s.re + (2 * M + 1)) :
    ‖emR (zF s) (2 * (M + 1)) b‖
      ≤ (2 * |(bernoulli (2 * (M + 1)) : ℝ)| / ((2 * (M + 1)) ! : ℝ) * ‖pochC s (2 * (M + 1))‖)
        * (b ^ (-(s.re + (2 * M + 1))) / (s.re + (2 * M + 1))
          - (b + 1) ^ (-(s.re + (2 * M + 1))) / (s.re + (2 * M + 1))) := by
  refine (norm_emR_le ((zF_gchain s hb).derivChain le_rfl) (M + 1) (by omega)).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← integral_rpow_unit hσ hb, ← integral_const_mul]
  apply le_of_eq
  apply integral_congr
  intro x hx
  rw [Set.uIcc_of_le (by linarith)] at hx
  have hx0 : 0 < x := by linarith [hx.1]
  dsimp only
  rw [norm_zF _ hx0]
  congr 2
  push_cast
  ring

lemma zeta_tail_summable_bound {s : ℂ} (M : ℕ) {a : ℝ} (ha : 0 < a)
    (hσ : 0 < s.re + (2 * M + 1)) :
    Summable (fun k : ℕ => emR (zF s) (2 * (M + 1)) (a + k)) ∧
    ‖∑' k : ℕ, emR (zF s) (2 * (M + 1)) (a + k)‖
      ≤ (2 * |(bernoulli (2 * (M + 1)) : ℝ)| / ((2 * (M + 1)) ! : ℝ) * ‖pochC s (2 * (M + 1))‖)
        * (a ^ (-(s.re + (2 * M + 1))) / (s.re + (2 * M + 1))) := by
  set q : ℝ := s.re + (2 * M + 1) with hq
  set C : ℝ := 2 * |(bernoulli (2 * (M + 1)) : ℝ)| / ((2 * (M + 1)) ! : ℝ)
    * ‖pochC s (2 * (M + 1))‖ with hC
  have hC0 : 0 ≤ C := by positivity
  have he : ∀ k : ℕ, ‖emR (zF s) (2 * (M + 1)) (a + k)‖
      ≤ C * ((a + k) ^ (-q) / q - (a + ((k + 1 : ℕ) : ℝ)) ^ (-q) / q) := by
    intro k
    have hk : 0 < a + k := by positivity
    have := norm_emR_zF_le (s := s) (M := M) hk hσ
    have e : a + ((k + 1 : ℕ) : ℝ) = a + k + 1 := by push_cast; ring
    rw [e]
    exact this
  have h := summable_of_telescope (e := fun k : ℕ => emR (zF s) (2 * (M + 1)) (a + k))
    (h := fun k : ℕ => (a + k) ^ (-q) / q) hC0 (fun k => by
      have : 0 < a + k := by positivity
      positivity) he
  simpa using h

lemma zF_zero (s : ℂ) (x : ℝ) : zF s 0 x = (x : ℂ) ^ (-s) := by
  simp [zF, pochC]

lemma tendsto_zF_atTop {s : ℂ} (m : ℕ) (hσ : 0 < s.re + m) (a : ℝ) :
    Tendsto (fun n : ℕ => zF s m (a + n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => a + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have h2 := ((tendsto_rpow_neg_atTop hσ).comp h1).const_mul ‖pochC s m‖
  rw [mul_zero] at h2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h2.congr' ?_
  filter_upwards [h1.eventually (eventually_gt_atTop 0)] with n hn
  rw [norm_zF m hn]
  rfl

lemma integral_cpow_neg {s : ℂ} (hs : s ≠ 1) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, (x : ℂ) ^ (-s) = ((b : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) := by
  have hs1 : (1 - s) ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
  have hd : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => (y : ℂ) ^ (1 - s) / (1 - s))
      ((x : ℂ) ^ (-s)) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le ha hx.1).ne'
    have := (hasDerivAt_ofReal_cpow_const hx0 hs1).div_const (1 - s)
    convert this using 1
    rw [show (1 - s - 1) = -s by ring]
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hd]
  · ring
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (zF_chain s 0 (x := x) (lt_of_lt_of_le ha hx.1)).continuousAt.continuousWithinAt.congr
      (fun y _ => (zF_zero s y).symm) (zF_zero s x).symm |>.mono subset_rfl

/-- The zeta Euler–Maclaurin remainder. -/
noncomputable def zetaR (s : ℂ) (N M : ℕ) : ℂ :=
  -∑' k : ℕ, emR (zF s) (2 * (M + 1)) (((N + 1 : ℕ) : ℝ) + k)

/-- Euler–Maclaurin for `ζ` on `Re s > 1`. -/
theorem zeta_em_of_one_lt {s : ℂ} (hs : 1 < s.re) (N M : ℕ) :
    riemannZeta s = (∑ k ∈ Finset.range N, (((k + 1 : ℕ)) : ℂ) ^ (-s))
      + (((N + 1 : ℕ)) : ℂ) ^ (1 - s) / (s - 1) + (((N + 1 : ℕ)) : ℂ) ^ (-s) / 2
      - ∑ j ∈ Finset.range M, (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
          * zF s (2 * j + 1) (((N + 1 : ℕ)) : ℝ)
      + zetaR s N M := by
  set a : ℝ := ((N + 1 : ℕ) : ℝ) with ha_def
  have ha : 0 < a := by positivity
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hσ0 : 0 < s.re := by linarith
  have hσM : 0 < s.re + (2 * M + 1) := by positivity
  obtain ⟨hsumR, -⟩ := zeta_tail_summable_bound (s := s) M ha hσM
  -- the Dirichlet series tail
  have hf : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hs)
    simpa using this
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]; exact hf.hasSum
  have htail := (hasSum_nat_add_iff' N).2 hz
  have htail' : HasSum (fun k : ℕ => zF s 0 (a + k))
      (riemannZeta s - ∑ k ∈ Finset.range N, (((k + 1 : ℕ)) : ℂ) ^ (-s)) := by
    have e1 : ∑ i ∈ Finset.range N, 1 / ((i : ℂ) + 1) ^ s
        = ∑ k ∈ Finset.range N, (((k + 1 : ℕ)) : ℂ) ^ (-s) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Complex.cpow_neg]; push_cast; ring
    rw [← e1]
    refine htail.congr_fun (fun k => ?_)
    rw [zF_zero, ha_def, Complex.cpow_neg]
    push_cast
    ring_nf
  -- Euler–Maclaurin partial sums
  have hEM : ∀ n : ℕ, ∑ k ∈ Finset.range n, zF s 0 (a + k)
      = (((a + n : ℝ) : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s)
        - (zF s 0 (a + n) - zF s 0 a) / 2
        + ∑ j ∈ Finset.range M, (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
            * (zF s (2 * j + 1) (a + n) - zF s (2 * j + 1) a)
        - ∑ k ∈ Finset.range n, emR (zF s) (2 * (M + 1)) (a + k) := by
    intro n
    have h := em_sum (zF_gchain s ha) (M + 1) (by omega) n
    rw [show M + 1 - 1 = M by omega] at h
    rw [h]
    have hi : ∫ x in a..a + n, zF s 0 x = (((a + n : ℝ) : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) := by
      rw [← integral_cpow_neg hs1 ha (by have := n.cast_nonneg (α := ℝ); linarith)]
      exact integral_congr (fun x _ => zF_zero s x)
    rw [hi]
  -- limits
  have hL : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, zF s 0 (a + k)) atTop
      (𝓝 (riemannZeta s - ∑ k ∈ Finset.range N, (((k + 1 : ℕ)) : ℂ) ^ (-s))) :=
    htail'.tendsto_sum_nat
  have hpow : Tendsto (fun n : ℕ => ((a + n : ℝ) : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => a + (n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    have h2 := (tendsto_rpow_neg_atTop (y := s.re - 1) (by linarith)).comp h1
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine h2.congr' ?_
    filter_upwards [h1.eventually (eventually_gt_atTop 0)] with n hn
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp only [Function.comp, Complex.sub_re, Complex.one_re]
    ring_nf
  have hR : Tendsto (fun n : ℕ => (((a + n : ℝ) : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s)
        - (zF s 0 (a + n) - zF s 0 a) / 2
        + ∑ j ∈ Finset.range M, (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
            * (zF s (2 * j + 1) (a + n) - zF s (2 * j + 1) a)
        - ∑ k ∈ Finset.range n, emR (zF s) (2 * (M + 1)) (a + k)) atTop
      (𝓝 ((0 - (a : ℂ) ^ (1 - s)) / (1 - s) - (0 - zF s 0 a) / 2
        + ∑ j ∈ Finset.range M, (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
            * (0 - zF s (2 * j + 1) a)
        - ∑' k : ℕ, emR (zF s) (2 * (M + 1)) (a + k))) := by
    refine ((((hpow.sub tendsto_const_nhds).div_const _).sub
      (((tendsto_zF_atTop 0 (by simpa using hσ0) a).sub tendsto_const_nhds).div_const _)).add
      (tendsto_finsetSum _ (fun j _ => ((tendsto_zF_atTop (2 * j + 1) (by positivity) a).sub
        tendsto_const_nhds).const_mul _))).sub hsumR.hasSum.tendsto_sum_nat
  have hlim := tendsto_nhds_unique hL (hR.congr (fun n => (hEM n).symm))
  have hzF0 : zF s 0 a = (a : ℂ) ^ (-s) := zF_zero s a
  rw [hzF0] at hlim
  unfold zetaR
  rw [← ha_def]
  have hs1' : (s - 1) ≠ 0 := sub_ne_zero.2 hs1
  have hs2 : (1 - s) ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  have e : (((N + 1 : ℕ)) : ℂ) = ((a : ℝ) : ℂ) := by rw [ha_def]; push_cast; ring
  rw [e]
  rw [sub_eq_iff_eq_add] at hlim
  rw [hlim]
  simp only [zero_sub, mul_neg, Finset.sum_neg_distrib]
  field_simp
  ring

lemma norm_pochC_le (s : ℂ) (m : ℕ) {ρ : ℝ} (hs : ‖s‖ ≤ ρ) : ‖pochC s m‖ ≤ (ρ + m) ^ m := by
  unfold pochC
  refine (Finset.norm_prod_le _ _).trans ?_
  calc ∏ j ∈ Finset.range m, ‖s + (j : ℂ)‖ ≤ ∏ j ∈ Finset.range m, (ρ + m) := by
        apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
        intro j hj
        have hj' : (j : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.1 hj).le
        calc ‖s + (j : ℂ)‖ ≤ ‖s‖ + ‖(j : ℂ)‖ := norm_add_le _ _
          _ ≤ ρ + m := by simp only [Complex.norm_natCast]; linarith
    _ = (ρ + m) ^ m := by simp

lemma emR_zF_unif {s : ℂ} (M : ℕ) (hσ : 0 < s.re) {ρ : ℝ} (hρ : ‖s‖ ≤ ρ) {b : ℝ} (hb : 1 ≤ b) :
    ‖emR (zF s) (2 * (M + 1)) b‖
      ≤ 2 * |(bernoulli (2 * (M + 1)) : ℝ)| / ((2 * (M + 1)) ! : ℝ)
        * ((ρ + (2 * (M + 1) : ℕ)) ^ (2 * (M + 1)) / b ^ (2 * (M + 1))) := by
  have hb0 : 0 < b := by linarith
  refine (norm_emR_le ((zF_gchain s hb0).derivChain le_rfl) (M + 1) (by omega)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρ
  have hc : ∫ x in b..b + 1, ((ρ + (2 * (M + 1) : ℕ)) ^ (2 * (M + 1)) / b ^ (2 * (M + 1)))
      = (ρ + (2 * (M + 1) : ℕ)) ^ (2 * (M + 1)) / b ^ (2 * (M + 1)) := by simp
  rw [← hc]
  apply integral_mono_on (by linarith)
  · exact ((zF_gchain s hb0).derivChain le_rfl).continuousOn _ |>.norm |>.intervalIntegrable
  · exact _root_.intervalIntegrable_const
  · intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hx1 : 1 ≤ x := le_trans hb hx.1
    rw [norm_zF _ hx0]
    have hp := norm_pochC_le s (2 * (M + 1)) hρ
    have hr : x ^ (-(s.re + ((2 * (M + 1) : ℕ) : ℝ))) ≤ 1 / b ^ (2 * (M + 1)) := by
      calc x ^ (-(s.re + ((2 * (M + 1) : ℕ) : ℝ))) ≤ x ^ (-(((2 * (M + 1) : ℕ) : ℝ))) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
        _ = 1 / x ^ (2 * (M + 1)) := by
            rw [Real.rpow_neg hx0.le, Real.rpow_natCast, one_div]
        _ ≤ 1 / b ^ (2 * (M + 1)) := by
            apply one_div_le_one_div_of_le (by positivity)
            exact pow_le_pow_left₀ hb0.le hx.1 _
    calc ‖pochC s (2 * (M + 1))‖ * x ^ (-(s.re + ((2 * (M + 1) : ℕ) : ℝ)))
        ≤ (ρ + (2 * (M + 1) : ℕ)) ^ (2 * (M + 1)) * (1 / b ^ (2 * (M + 1))) :=
          mul_le_mul hp hr (by positivity) (by positivity)
      _ = _ := by ring

/-- Closed form of the zeta unit remainder (valid for `s ≠ 1`). -/
noncomputable def closedZ (s : ℂ) (M : ℕ) (b : ℝ) : ℂ :=
  (((b + 1 : ℝ) : ℂ) ^ (1 - s) - (b : ℂ) ^ (1 - s)) / (1 - s)
    - (zF s 0 b + zF s 0 (b + 1)) / 2
    + ∑ j ∈ Finset.range M, (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
        * (zF s (2 * j + 1) (b + 1) - zF s (2 * j + 1) b)

lemma emR_zF_eq_closedZ {s : ℂ} (hs1 : s ≠ 1) (M : ℕ) {b : ℝ} (hb : 0 < b) :
    emR (zF s) (2 * (M + 1)) b = closedZ s M b := by
  have h := em_unit ((zF_gchain s hb).derivChain le_rfl) (M + 1) (by omega)
  rw [show M + 1 - 1 = M by omega] at h
  have hi : ∫ x in b..b + 1, zF s 0 x
      = (((b + 1 : ℝ) : ℂ) ^ (1 - s) - (b : ℂ) ^ (1 - s)) / (1 - s) := by
    rw [← integral_cpow_neg hs1 hb (by linarith)]
    exact integral_congr (fun x _ => zF_zero s x)
  rw [hi] at h
  unfold closedZ
  rw [h]; ring

lemma differentiableAt_zF (m : ℕ) {x : ℝ} (hx : 0 < x) (s : ℂ) :
    DifferentiableAt ℂ (fun s => zF s m x) s := by
  unfold zF pochC
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have h1 : DifferentiableAt ℂ (fun s : ℂ => ∏ j ∈ Finset.range m, (s + (j : ℂ))) s := by
    fun_prop
  exact ((differentiableAt_const _).mul h1).mul
    (((differentiableAt_id.neg).sub_const _).const_cpow (Or.inl hx'))

lemma differentiableAt_closedZ (M : ℕ) {b : ℝ} (hb : 0 < b) {s : ℂ} (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun s => closedZ s M b) s := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hb1 : ((b + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : b + 1 ≠ 0)
  have hs2 : (1 - s) ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  unfold closedZ
  apply DifferentiableAt.add
  · apply DifferentiableAt.sub
    · apply DifferentiableAt.div _ (differentiableAt_const _ |>.sub differentiableAt_id) hs2
      exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hb1) |>.sub
        (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hb'))
    · exact ((differentiableAt_zF 0 hb s).add (differentiableAt_zF 0 (by linarith) s)).div_const 2
  · exact DifferentiableAt.fun_sum (fun j _ => (differentiableAt_const _).mul
      ((differentiableAt_zF _ (by linarith) s).sub (differentiableAt_zF _ hb s)))

/-- `zetaR` is holomorphic on `{Re s > 0, s ≠ 1}`. -/
lemma differentiableAt_zetaR {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) (N M : ℕ) :
    DifferentiableAt ℂ (fun s => zetaR s N M) s := by
  set ρ : ℝ := ‖s‖ + 1 with hρ
  set U : Set ℂ := {v | 0 < v.re} ∩ {v | ‖v‖ < ρ} ∩ {v | v ≠ 1} with hU
  have hUo : IsOpen U :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)).inter isOpen_ne
  have hsU : s ∈ U := ⟨⟨hσ, by simp [ρ]⟩, hs1⟩
  set u : ℕ → ℝ := fun k => 2 * |(bernoulli (2 * (M + 1)) : ℝ)| / ((2 * (M + 1)) ! : ℝ)
    * ((ρ + (2 * (M + 1) : ℕ)) ^ (2 * (M + 1)) / (((N + 1 : ℕ) : ℝ) + k) ^ (2 * (M + 1))) with hu
  have hus : Summable u := by
    have hs : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ (2 * (M + 1))) :=
      (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega))
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (hs.mul_left (2 * |(bernoulli (2 * (M + 1)) : ℝ)| / ((2 * (M + 1)) ! : ℝ)
        * (ρ + (2 * (M + 1) : ℕ)) ^ (2 * (M + 1))))
    simp only [hu]
    rw [mul_assoc, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    push_cast; linarith
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ
      (fun v => emR (zF v) (2 * (M + 1)) (((N + 1 : ℕ) : ℝ) + k)) U := by
    intro k v hv
    have hb : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) + k := by positivity
    have hev : (fun v => emR (zF v) (2 * (M + 1)) (((N + 1 : ℕ) : ℝ) + k))
        =ᶠ[𝓝 v] fun v => closedZ v M (((N + 1 : ℕ) : ℝ) + k) := by
      filter_upwards [isOpen_ne.mem_nhds hv.2] with x hx
      exact emR_zF_eq_closedZ hx M hb
    exact ((differentiableAt_closedZ M hb hv.2).congr_of_eventuallyEq hev).differentiableWithinAt
  have hle : ∀ (k : ℕ) (v : ℂ), v ∈ U →
      ‖emR (zF v) (2 * (M + 1)) (((N + 1 : ℕ) : ℝ) + k)‖ ≤ u k := by
    intro k v hv
    have hb : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) + k := by
      push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k), (N.cast_nonneg : (0:ℝ) ≤ N)]
    exact emR_zF_unif M hv.1.1 hv.1.2.le hb
  have hD := differentiableOn_tsum_of_summable_norm hus hdiff hUo hle
  exact ((hD s hsU).differentiableAt (hUo.mem_nhds hsU)).neg

/-- Right-hand side of the Euler–Maclaurin formula for `ζ`. -/
noncomputable def zetaRHS (s : ℂ) (N M : ℕ) : ℂ :=
  (∑ k ∈ Finset.range N, (((k + 1 : ℕ)) : ℂ) ^ (-s))
    + (((N + 1 : ℕ)) : ℂ) ^ (1 - s) / (s - 1) + (((N + 1 : ℕ)) : ℂ) ^ (-s) / 2
    - ∑ j ∈ Finset.range M, (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
        * zF s (2 * j + 1) (((N + 1 : ℕ)) : ℝ)
    + zetaR s N M

lemma differentiableAt_zetaRHS {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) (N M : ℕ) :
    DifferentiableAt ℂ (fun s => zetaRHS s N M) s := by
  have hs2 : (s - 1) ≠ 0 := sub_ne_zero.2 hs1
  have hN : (((N + 1 : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast (by omega : N + 1 ≠ 0)
  have ha : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  unfold zetaRHS
  apply DifferentiableAt.add _ (differentiableAt_zetaR hσ hs1 N M)
  apply DifferentiableAt.sub
  · apply DifferentiableAt.add
    · apply DifferentiableAt.add
      · exact DifferentiableAt.fun_sum (fun k _ => differentiableAt_id.neg.const_cpow
          (Or.inl (by exact_mod_cast (by omega : k + 1 ≠ 0))))
      · exact (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hN)).div
          (differentiableAt_id.sub_const _) hs2
    · exact (differentiableAt_id.neg.const_cpow (Or.inl hN)).div_const 2
  · exact DifferentiableAt.fun_sum (fun j _ => (differentiableAt_const _).mul
      (differentiableAt_zF _ ha s))

lemma convex_E1 : Convex ℝ {v : ℂ | 0 < v.re ∧ v.re - 1 < v.im} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul] at hx hy ⊢
  rcases ha.lt_or_eq with ha' | ha'
  · have h1 : a * (x.re - 1) < a * x.im := mul_lt_mul_of_pos_left hx.2 ha'
    have h2 : b * (y.re - 1) ≤ b * y.im := mul_le_mul_of_nonneg_left hy.2.le hb
    constructor
    · nlinarith [mul_pos ha' hx.1, mul_nonneg hb hy.1.le]
    · nlinarith
  · subst ha'; simp only [zero_add] at hab; subst hab; simpa using hy

lemma convex_E2 : Convex ℝ {v : ℂ | 0 < v.re ∧ v.im < 0} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul] at hx hy ⊢
  rcases ha.lt_or_eq with ha' | ha'
  · constructor
    · nlinarith [mul_pos ha' hx.1, mul_nonneg hb hy.1.le]
    · nlinarith [mul_neg_of_pos_of_neg ha' hx.2, mul_nonpos_of_nonneg_of_nonpos hb hy.2.le]
  · subst ha'; simp only [zero_add] at hab; subst hab; simpa using hy

/-- Euler–Maclaurin for `ζ` on `{Re s > 0, s ≠ 1}`, by analytic continuation. -/
theorem zeta_em {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) (N M : ℕ) :
    riemannZeta s = zetaRHS s N M := by
  rcases lt_or_ge 1 s.re with h1 | h1
  · exact zeta_em_of_one_lt h1 N M
  have key : ∀ (E : Set ℂ) (z0 : ℂ), IsOpen E → Convex ℝ E → (∀ v ∈ E, 0 < v.re ∧ v ≠ 1) →
      z0 ∈ E → 1 < z0.re → ∀ v ∈ E, riemannZeta v = zetaRHS v N M := by
    intro E z0 hEo hEc hE hz0 hz0re
    have hf : AnalyticOnNhd ℂ riemannZeta E := by
      apply DifferentiableOn.analyticOnNhd _ hEo
      intro v hv
      exact (differentiableAt_riemannZeta (hE v hv).2).differentiableWithinAt
    have hg : AnalyticOnNhd ℂ (fun v => zetaRHS v N M) E := by
      apply DifferentiableOn.analyticOnNhd _ hEo
      intro v hv
      exact (differentiableAt_zetaRHS (hE v hv).1 (hE v hv).2 N M).differentiableWithinAt
    have hev : riemannZeta =ᶠ[𝓝 z0] fun v => zetaRHS v N M := by
      have ho : IsOpen {v : ℂ | 1 < v.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [ho.mem_nhds hz0re] with v hv
      exact zeta_em_of_one_lt hv N M
    exact fun v hv => hf.eqOn_of_preconnected_of_eventuallyEq hg hEc.isPreconnected hz0 hev hv
  rcases lt_or_ge s.im 0 with him | him
  · refine key {v : ℂ | 0 < v.re ∧ v.im < 0} ⟨2, -1⟩
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_im continuous_const)) convex_E2 ?_ ?_ ?_ s ⟨hσ, him⟩
    · intro v hv
      refine ⟨hv.1, fun h => ?_⟩
      have := hv.2; rw [h] at this; simp at this
    · show (0:ℝ) < 2 ∧ (-1:ℝ) < 0; norm_num
    · show (1:ℝ) < 2; norm_num
  · have hlt : s.re - 1 < s.im := by
      rcases h1.lt_or_eq with h1' | h1'
      · linarith
      · rcases him.lt_or_eq with h2 | h2
        · linarith
        · exfalso; apply hs1; apply Complex.ext <;> simp [h1', ← h2]
    refine key {v : ℂ | 0 < v.re ∧ v.re - 1 < v.im} ⟨2, 2⟩
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt (Complex.continuous_re.sub continuous_const) Complex.continuous_im))
      convex_E1 ?_ ?_ ?_ s ⟨hσ, hlt⟩
    · intro v hv
      refine ⟨hv.1, fun h => ?_⟩
      have := hv.2; rw [h] at this; simp at this
    · show (0:ℝ) < 2 ∧ (2:ℝ) - 1 < 2; norm_num
    · show (1:ℝ) < 2; norm_num

lemma zetaR_bound {s : ℂ} (hσ : 0 < s.re) (N M : ℕ) :
    ‖zetaR s N M‖
      ≤ (2 * |(bernoulli (2 * (M + 1)) : ℝ)| / ((2 * (M + 1)) ! : ℝ) * ‖pochC s (2 * (M + 1))‖)
        * ((((N + 1 : ℕ) : ℝ)) ^ (-(s.re + (2 * M + 1))) / (s.re + (2 * M + 1))) := by
  unfold zetaR
  rw [norm_neg]
  exact (zeta_tail_summable_bound M (by positivity) (by positivity)).2

end EMCore
