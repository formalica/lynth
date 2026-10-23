module

import all Lynth.Interval.Fns.EMCore.GammaLimit

/-!
# Complex Stirling expansion for the digamma function
-/

open Real Complex intervalIntegral Nat Filter Topology

namespace EMCore

/-- The derivative chain of `x ↦ 1 / (x + w)` (a shift of `gF`). -/
noncomputable def dF (w : ℂ) : ℕ → ℝ → ℂ := fun m x => gF w (m + 1) x

lemma dF_gchain {w : ℂ} (hw : 0 < w.re) : GChain (dF w) 0 :=
  fun m x hx => gF_chain hw (m + 1) x hx

/-- `w ↦ gF w m x` has derivative `gF w (m+1) x` (the chain also runs in `w`). -/
lemma gF_hasDerivAt_w {w : ℂ} (hw : 0 < w.re) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun v => gF v m x) (gF w (m + 1) x) w := by
  have hne := ne_zero_of_re hw hx
  cases m with
  | zero =>
    have h1 : HasDerivAt (fun v : ℂ => (x : ℂ) + v) 1 w := (hasDerivAt_id w).const_add _
    have := h1.clog (slit_of_re hw hx)
    simp only [gF]
    convert this using 1
    simp
  | succ m =>
    have h := hasDerivAt_c_div_pow ((-1) ^ m * (m ! : ℂ)) (x : ℂ) w (m + 1) (by
      rw [add_comm]; exact hne)
    simp only [gF]
    have e : (fun v : ℂ => (-1) ^ m * (m ! : ℂ) / ((x : ℂ) + v) ^ (m + 1))
        = (fun v : ℂ => (-1) ^ m * (m ! : ℂ) / (v + (x : ℂ)) ^ (m + 1)) := by
      funext v; rw [add_comm]
    rw [e]
    convert h using 1
    rw [add_comm (x : ℂ) w]
    push_cast [Nat.factorial_succ]
    ring

/-- Antiderivative of `log (x + w)` in `x`. -/
noncomputable def logAnti (w : ℂ) (x : ℝ) : ℂ := ((x : ℂ) + w) * Complex.log ((x : ℂ) + w) - x

lemma logAnti_hasDerivAt_x {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (logAnti w) (gF w 0 x) x := by
  have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) + w) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp.add_const w
  have hl := hlin.clog_real (slit_of_re hw hx)
  have hne : (x : ℂ) + w ≠ 0 := slitPlane_ne_zero (slit_of_re hw hx)
  have := (hlin.mul hl).sub (hasDerivAt_id x).ofReal_comp
  unfold logAnti
  have hfun : (fun x : ℝ => ((x : ℂ) + w) * Complex.log ((x : ℂ) + w) - x)
      = (((fun y : ℝ => (y : ℂ) + w) * fun (t : ℝ) => Complex.log ((t : ℂ) + w))
        - fun (y : ℝ) => ((id y : ℝ) : ℂ)) := by
    funext y
    simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  rw [hfun]
  convert this using 1
  simp only [gF]
  field_simp
  simp

lemma logAnti_hasDerivAt_w {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun v => logAnti v x) (gF w 0 x + 1) w := by
  have h1 : HasDerivAt (fun v : ℂ => (x : ℂ) + v) 1 w := (hasDerivAt_id w).const_add _
  have hl := h1.clog (slit_of_re hw hx)
  have hne : (x : ℂ) + w ≠ 0 := slitPlane_ne_zero (slit_of_re hw hx)
  have := (h1.mul hl).sub_const (x : ℂ)
  unfold logAnti
  convert this using 1
  simp only [gF]
  field_simp

/-- Closed form of the unit remainder, from `em_unit`. -/
lemma emR_closed {F : ℕ → ℝ → ℂ} {a : ℝ} (h : DerivChain F a) (N : ℕ) (hN : 1 ≤ N) :
    emR F (2 * N) a = (∫ x in a..a + 1, F 0 x) - (F 0 a + F 0 (a + 1)) / 2
      + ∑ j ∈ Finset.range (N - 1), (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
          * (F (2 * j + 1) (a + 1) - F (2 * j + 1) a) := by
  rw [em_unit h N hN]; ring

/-- Differentiating the Stirling unit remainder in `w` gives the digamma unit remainder. -/
lemma emR_gF_hasDerivAt {w : ℂ} (hw : 0 < w.re) (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    HasDerivAt (fun v => emR (gF v) (2 * N) k) (emR (dF w) (2 * N) k) w := by
  have hk0 : (0:ℝ) ≤ k := k.cast_nonneg
  have hk1 : (0:ℝ) ≤ k + 1 := by linarith
  -- closed forms, valid in a neighbourhood of `w`
  have hU : ∀ᶠ v in 𝓝 w, emR (gF v) (2 * N) k
      = (logAnti v (k + 1) - logAnti v k) - (gF v 0 k + gF v 0 (k + 1)) / 2
        + ∑ j ∈ Finset.range (N - 1),
            (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
              * (gF v (2 * j + 1) (k + 1) - gF v (2 * j + 1) k) := by
    have hopen : IsOpen {v : ℂ | 0 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hw] with v hv
    rw [emR_closed ((gF_gchain hv).derivChain hk0) N hN]
    congr 2
    rw [integral_eq_sub_of_hasDerivAt]
    · intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact logAnti_hasDerivAt_x hv (hk0.trans hx.1)
    · exact (((gF_gchain hv).derivChain hk0).continuousOn 0).intervalIntegrable
  have hD : emR (dF w) (2 * N) k
      = (gF w 0 (k + 1) - gF w 0 k) - (gF w 1 k + gF w 1 (k + 1)) / 2
        + ∑ j ∈ Finset.range (N - 1),
            (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
              * (gF w (2 * j + 1 + 1) (k + 1) - gF w (2 * j + 1 + 1) k) := by
    rw [emR_closed ((dF_gchain hw).derivChain hk0) N hN]
    congr 2
    exact ((gF_gchain hw).derivChain hk0).integral_eq 0
  rw [hD]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hU
  have hsum := HasDerivAt.fun_sum (u := Finset.range (N - 1)) (fun j _ =>
    ((gF_hasDerivAt_w hw (2 * j + 1) hk1).sub (gF_hasDerivAt_w hw (2 * j + 1) hk0)).const_mul
      (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ))
  have hA := (logAnti_hasDerivAt_w hw hk1).sub (logAnti_hasDerivAt_w hw hk0)
  have hB := ((gF_hasDerivAt_w hw 0 hk0).add (gF_hasDerivAt_w hw 0 hk1)).div_const 2
  have := (hA.sub hB).add hsum
  convert this using 1
  ring

/-- Uniform bound for the unit remainders on a half-plane `δ ≤ Re v`. -/
lemma norm_emR_gF_unif {v : ℂ} {δ : ℝ} (hδ : 0 < δ) (hv : δ ≤ v.re) {N : ℕ} (hN : 1 ≤ N)
    (k : ℕ) :
    ‖emR (gF v) (2 * N) k‖
      ≤ 2 * |(bernoulli (2 * N) : ℝ)| / ((2 * N) ! : ℝ) * (((2 * N - 1) ! : ℝ) / ((k : ℝ) + δ) ^ (2 * N)) := by
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hv0 : 0 < v.re := lt_of_lt_of_le hδ hv
  refine (norm_emR_le ((gF_gchain hv0).derivChain hk0) N hN).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hc : ∫ x in (k:ℝ)..(k:ℝ) + 1, (((2 * N - 1) ! : ℝ) / ((k : ℝ) + δ) ^ (2 * N))
      = ((2 * N - 1) ! : ℝ) / ((k : ℝ) + δ) ^ (2 * N) := by simp
  rw [← hc]
  apply integral_mono_on (by linarith)
  · exact ((gF_gchain hv0).derivChain hk0).continuousOn _ |>.norm |>.intervalIntegrable
  · exact _root_.intervalIntegrable_const
  · intro x hx
    have hx0 : 0 ≤ x := hk0.trans hx.1
    obtain ⟨M, hM⟩ : ∃ M, 2 * N = M + 1 := ⟨2 * N - 1, by omega⟩
    have hM' : 2 * N - 1 = M := by omega
    rw [hM', hM]
    simp only [gF, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    have := Complex.re_le_norm ((x : ℂ) + v)
    simp at this
    linarith [hx.1]

lemma summable_inv_add_pow {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {q : ℕ} (hq : 2 ≤ q) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + δ) ^ q) := by
  have hs : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ q) :=
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega))
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hs.mul_left (1 / δ ^ q))
  have hk : δ * ((k + 1 : ℕ) : ℝ) ≤ (k : ℝ) + δ := by
    push_cast; nlinarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  rw [one_div_mul_one_div, ← mul_pow]
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by positivity) hk q

/-- `gammaR` is holomorphic in `w`, with derivative the digamma remainder. -/
lemma gammaR_hasDerivAt {w : ℂ} (hw : 0 < w.re) {N : ℕ} (hN : 1 ≤ N) :
    HasDerivAt (fun v => gammaR v N) (∑' k : ℕ, emR (dF w) (2 * N) k) w := by
  set δ : ℝ := min (w.re / 2) 1 with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδw : δ < w.re := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set U : Set ℂ := {v | δ < v.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hwU : w ∈ U := hδw
  set u : ℕ → ℝ := fun k => 2 * |(bernoulli (2 * N) : ℝ)| / ((2 * N) ! : ℝ)
    * (((2 * N - 1) ! : ℝ) / ((k : ℝ) + δ) ^ (2 * N)) with hu
  have hus : Summable u := by
    have := (summable_inv_add_pow hδ0 hδ1 (q := 2 * N) (by omega)).mul_left
      (2 * |(bernoulli (2 * N) : ℝ)| / ((2 * N) ! : ℝ) * ((2 * N - 1) ! : ℝ))
    refine this.congr (fun k => ?_)
    simp only [hu]; ring
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ (fun v => emR (gF v) (2 * N) k) U := by
    intro k v hv
    have hv0 : 0 < v.re := lt_trans hδ0 hv
    exact (emR_gF_hasDerivAt hv0 N hN k).differentiableAt.differentiableWithinAt
  have hle : ∀ (k : ℕ) (v : ℂ), v ∈ U → ‖emR (gF v) (2 * N) k‖ ≤ u k :=
    fun k v hv => norm_emR_gF_unif hδ0 (le_of_lt hv) hN k
  have hD := Complex.hasSum_deriv_of_summable_norm hus hdiff hUo hle hwU
  have hDiff := Complex.differentiableOn_tsum_of_summable_norm hus hdiff hUo hle
  have hda : DifferentiableAt ℂ (fun v => ∑' k : ℕ, emR (gF v) (2 * N) k) w :=
    (hDiff w hwU).differentiableAt (hUo.mem_nhds hwU)
  have he : (fun k : ℕ => deriv (fun v => emR (gF v) (2 * N) k) w)
      = fun k : ℕ => emR (dF w) (2 * N) (k : ℝ) := by
    funext k; exact (emR_gF_hasDerivAt hw N hN k).deriv
  rw [he] at hD
  have : HasDerivAt (fun v => ∑' k : ℕ, emR (gF v) (2 * N) k)
      (deriv (fun v => ∑' k : ℕ, emR (gF v) (2 * N) k) w) w := hda.hasDerivAt
  rw [← hD.tsum_eq] at this
  exact this

lemma norm_gF_odd {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    ‖gF w (2 * N + 1) x‖ ≤ ((2 * N) ! : ℝ) * secSq w ^ (N + 1) / (x + ‖w‖) ^ (2 * N + 1) := by
  simp only [gF, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]
  have := inv_norm_pow_odd_le hw hx N
  calc ((2 * N) ! : ℝ) / ‖(x : ℂ) + w‖ ^ (2 * N + 1)
      = ((2 * N) ! : ℝ) * (1 / ‖(x : ℂ) + w‖ ^ (2 * N + 1)) := by ring
    _ ≤ ((2 * N) ! : ℝ) * (secSq w ^ (N + 1) / (x + ‖w‖) ^ (2 * N + 1)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

lemma norm_emR_dF_le {w : ℂ} (hw : 0 < w.re) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    ‖emR (dF w) (2 * N) k‖
      ≤ (2 * |(bernoulli (2 * N) : ℝ)| / ((2 * N) ! : ℝ) * (((2 * N) ! : ℝ) * secSq w ^ (N + 1)))
        * (1 / (((2 * N : ℕ) : ℝ) * ((k : ℝ) + ‖w‖) ^ (2 * N))
          - 1 / (((2 * N : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + ‖w‖) ^ (2 * N))) := by
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le hw (Complex.re_le_norm w)
  refine (norm_emR_le ((dF_gchain hw).derivChain hk0) N hN).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hint := integral_inv_pow_unit hw0 hk0 (q := 2 * N) (by omega)
  push_cast at hint ⊢
  rw [← hint, ← integral_const_mul]
  apply integral_mono_on (by linarith)
  · exact ((dF_gchain hw).derivChain hk0).continuousOn _ |>.norm |>.intervalIntegrable
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      have : 0 < x + ‖w‖ := by linarith [hx.1]
      positivity
  · intro x hx
    have hx0 : 0 ≤ x := hk0.trans hx.1
    have := norm_gF_odd hw hx0 N
    calc ‖dF w (2 * N) x‖ ≤ ((2 * N) ! : ℝ) * secSq w ^ (N + 1) / (x + ‖w‖) ^ (2 * N + 1) := this
      _ = _ := by ring

/-- The digamma Euler–Maclaurin remainder. -/
noncomputable def digR (w : ℂ) (N : ℕ) : ℂ := ∑' k : ℕ, emR (dF w) (2 * N) k

lemma digR_bound {w : ℂ} (hw : 0 < w.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖digR w N‖ ≤ (2 * (|(bernoulli (2 * N) : ℝ)| / (2 * (N : ℝ)))) * secSq w ^ (N + 1)
      / ‖w‖ ^ (2 * N) := by
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le hw (Complex.re_le_norm w)
  have hS := one_le_secSq hw
  obtain ⟨-, hb⟩ := summable_of_telescope (e := fun k : ℕ => emR (dF w) (2 * N) k)
    (h := fun k : ℕ => 1 / (((2 * N : ℕ) : ℝ) * ((k : ℝ) + ‖w‖) ^ (2 * N)))
    (by positivity) (fun k => by positivity) (fun k => norm_emR_dF_le hw hN k)
  refine hb.trans (le_of_eq ?_)
  simp only [Nat.cast_zero, zero_add]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : (0:ℝ) < ((2 * N) ! : ℝ) := by positivity
  push_cast
  field_simp

lemma hasDerivAt_c_div_pow' (c w : ℂ) (m : ℕ) (hw : w ≠ 0) :
    HasDerivAt (fun v : ℂ => c / v ^ m) (c * (-(m : ℂ)) / w ^ (m + 1)) w := by
  have := hasDerivAt_c_div_pow c 0 w m (by simpa using hw)
  simpa using this

/-- Derivative of the Stirling exponent. -/
lemma stirlingPhi_hasDerivAt {w : ℂ} (hw : 0 < w.re) {N : ℕ} (hN : 1 ≤ N) :
    HasDerivAt (fun v => stirlingPhi v N)
      (Complex.log w + (w - 1 / 2) / w - 1
        + (∑ k ∈ Finset.range (N - 1),
            ((bernoulli (2 * (k + 1)) : ℚ) : ℂ) / ((2 * ((k + 1) : ℂ)) * (2 * ((k + 1) : ℂ) - 1))
              * (-((2 * (k + 1) - 1 : ℕ) : ℂ)) / w ^ (2 * (k + 1) - 1 + 1))
        + digR w N) w := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have hslit : w ∈ slitPlane := Or.inl hw
  have hlog := Complex.hasDerivAt_log hslit
  have h1 := (((hasDerivAt_id w).sub_const (1 / 2 : ℂ)).mul hlog).sub (hasDerivAt_id w)
  have h2 := h1.add_const (Complex.log (Real.sqrt (2 * Real.pi)))
  have hsum := HasDerivAt.fun_sum (u := Finset.range (N - 1)) (fun k _ =>
    hasDerivAt_c_div_pow' (((bernoulli (2 * (k + 1)) : ℚ) : ℂ)
      / ((2 * ((k + 1) : ℂ)) * (2 * ((k + 1) : ℂ) - 1))) w (2 * (k + 1) - 1) hw0)
  have h3 := (h2.add hsum).add (gammaR_hasDerivAt hw hN)
  unfold stirlingPhi
  convert h3 using 1
  · funext v
    congr 2
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [div_div]
  · unfold digR
    simp only [id]
    field_simp

/-- **Complex Stirling expansion for digamma** with Euler–Maclaurin remainder. -/
theorem digamma_eq_stirling {w : ℂ} (hw : 0 < w.re) {N : ℕ} (hN : 1 ≤ N) :
    Complex.digamma w = Complex.log w - 1 / (2 * w)
      + (∑ k ∈ Finset.range (N - 1),
          -(((bernoulli (2 * (k + 1)) : ℚ)) : ℂ) / ((2 * ((((k + 1) : ℕ)) : ℂ)) * w ^ (2 * (k + 1))))
      + digR w N := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have hopen : IsOpen {v : ℂ | 0 < v.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : Complex.Gamma =ᶠ[𝓝 w] fun v => Complex.exp (stirlingPhi v N) := by
    filter_upwards [hopen.mem_nhds hw] with v hv
    exact gamma_eq_exp_stirlingPhi hv hN
  have hd := (stirlingPhi_hasDerivAt hw hN).cexp
  rw [Complex.digamma_def, logDeriv_apply, hev.deriv_eq, hd.deriv, gamma_eq_exp_stirlingPhi hw hN,
    mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
  have hterm : ∀ k ∈ Finset.range (N - 1),
      ((bernoulli (2 * (k + 1)) : ℚ) : ℂ) / ((2 * ((k + 1) : ℂ)) * (2 * ((k + 1) : ℂ) - 1))
          * (-((2 * (k + 1) - 1 : ℕ) : ℂ)) / w ^ (2 * (k + 1) - 1 + 1)
        = -(((bernoulli (2 * (k + 1)) : ℚ)) : ℂ) / ((2 * ((((k + 1) : ℕ)) : ℂ)) * w ^ (2 * (k + 1))) := by
    intro k _
    have e1 : 2 * (k + 1) - 1 + 1 = 2 * (k + 1) := by omega
    have e2 : ((2 * (k + 1) - 1 : ℕ) : ℂ) = 2 * ((k : ℂ) + 1) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have h3 : (2 * ((k:ℂ) + 1) - 1) ≠ 0 := by
      rw [← e2]; exact_mod_cast (by omega : 2 * (k + 1) - 1 ≠ 0)
    have h4 : (2 * ((k:ℂ) + 1)) ≠ 0 := by
      have : (2 * ((k:ℂ) + 1)) = ((2 * (k + 1) : ℕ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast (by omega : 2 * (k + 1) ≠ 0)
    rw [e1, e2]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm]
  field_simp
  ring

end EMCore
