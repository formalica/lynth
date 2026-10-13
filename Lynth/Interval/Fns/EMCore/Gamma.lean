import Lynth.Interval.Fns.EMCore.EulerMaclaurin

/-!
# Euler–Maclaurin for `log (x + w)`: the complex Stirling remainder
-/

open Real Complex intervalIntegral Nat Filter Topology

namespace EMCore

lemma hasDerivAt_c_div_pow (c w z : ℂ) (k : ℕ) (hz : z + w ≠ 0) :
    HasDerivAt (fun z : ℂ => c / (z + w) ^ k) (c * (-(k : ℂ)) / (z + w) ^ (k + 1)) z := by
  have h1 : HasDerivAt (fun z : ℂ => z + w) 1 z := (hasDerivAt_id z).add_const w
  have h2 := ((h1.pow k).inv (pow_ne_zero _ hz)).const_mul c
  simp only [Pi.inv_apply, Pi.pow_apply] at h2
  have hfun : (fun z : ℂ => c / (z + w) ^ k)
      = (fun y => c * ((y + w) ^ k)⁻¹) := by
    ext y
    rw [div_eq_mul_inv]
  rw [hfun]
  convert h2 using 1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have : (z + w) ^ (k + 1) * (z + w) ^ (k - 1) = ((z + w) ^ k) ^ 2 := by
      rw [← pow_add, ← pow_mul]; congr 1; omega
    field_simp
    rw [mul_assoc (c * k), this]

/-- The derivative chain of `x ↦ log (x + w)`. -/
noncomputable def gF (w : ℂ) : ℕ → ℝ → ℂ
  | 0, x => Complex.log ((x : ℂ) + w)
  | (m + 1), x => (-1) ^ m * (m ! : ℂ) / ((x : ℂ) + w) ^ (m + 1)

lemma slit_of_re {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) + w ∈ slitPlane := by
  left; simp; linarith

lemma ne_zero_of_re {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) + w ≠ 0 :=
  slitPlane_ne_zero (slit_of_re hw hx)

lemma gF_chain {w : ℂ} (hw : 0 < w.re) (m : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (gF w m) (gF w (m + 1) x) x := by
  have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) + w) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp.add_const w
  have hne := ne_zero_of_re hw hx
  cases m with
  | zero =>
    have hlog := hlin.clog_real (slit_of_re hw hx)
    simp only [gF]
    have hfun : gF w 0 = (fun y : ℝ => Complex.log ((y : ℂ) + w)) := by
      ext y
      simp only [gF]
    rw [hfun]
    convert hlog using 1
    simp
  | succ m =>
    have h := (hasDerivAt_c_div_pow ((-1) ^ m * (m ! : ℂ)) w x (m + 1) hne).comp_ofReal
    simp only [gF]
    have hfun : gF w (m + 1)
        = (fun y : ℝ => (-1) ^ m * (m ! : ℂ) / ((y : ℂ) + w) ^ (m + 1)) := by
      ext y
      simp only [gF]
    rw [hfun]
    convert h using 1
    push_cast [Nat.factorial_succ]
    ring

lemma gF_gchain {w : ℂ} (hw : 0 < w.re) : GChain (gF w) 0 :=
  fun m x hx => gF_chain hw m x hx

/-- Key geometric inequality: `|x + w| ≥ cos(arg w / 2) (x + |w|)`, squared and cleared. -/
lemma norm_add_sq_ge {w : ℂ} (x : ℝ) :
    (‖w‖ + w.re) * (x + ‖w‖) ^ 2 ≤ 2 * ‖w‖ * ‖(x : ℂ) + w‖ ^ 2 := by
  have h1 : ‖(x : ℂ) + w‖ ^ 2 = (x + w.re) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h2 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h3 : w.re ≤ ‖w‖ := Complex.re_le_norm w
  have h4 : w.im ^ 2 = ‖w‖ ^ 2 - w.re ^ 2 := by linarith
  rw [h1, h4]
  nlinarith [mul_nonneg (sub_nonneg.2 h3) (sq_nonneg (x - ‖w‖))]

/-- The "sector factor" `S = sec²(arg w / 2) = 2|w| / (|w| + Re w) ≥ 1`. -/
noncomputable def secSq (w : ℂ) : ℝ := 2 * ‖w‖ / (‖w‖ + w.re)

lemma one_le_secSq {w : ℂ} (hw : 0 < w.re) : 1 ≤ secSq w := by
  have h3 : w.re ≤ ‖w‖ := Complex.re_le_norm w
  unfold secSq
  rw [le_div_iff₀ (by linarith)]; linarith

lemma inv_norm_pow_even_le {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    1 / ‖(x : ℂ) + w‖ ^ (2 * N) ≤ secSq w ^ N / (x + ‖w‖) ^ (2 * N) := by
  have hn : 0 < ‖(x : ℂ) + w‖ := norm_pos_iff.2 (ne_zero_of_re hw hx)
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le hw (Complex.re_le_norm w)
  have hxw : 0 < x + ‖w‖ := by linarith
  have key := norm_add_sq_ge (w := w) x
  have hS : (x + ‖w‖) ^ 2 ≤ secSq w * ‖(x : ℂ) + w‖ ^ 2 := by
    unfold secSq
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith [Complex.re_le_norm w])]
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, pow_mul, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hS N

lemma inv_norm_pow_odd_le {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    1 / ‖(x : ℂ) + w‖ ^ (2 * N + 1) ≤ secSq w ^ (N + 1) / (x + ‖w‖) ^ (2 * N + 1) := by
  have hn : 0 < ‖(x : ℂ) + w‖ := norm_pos_iff.2 (ne_zero_of_re hw hx)
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le hw (Complex.re_le_norm w)
  have hxw : 0 < x + ‖w‖ := by linarith
  have hS1 := one_le_secSq hw
  have key := norm_add_sq_ge (w := w) x
  have hS : (x + ‖w‖) ^ 2 ≤ secSq w * ‖(x : ℂ) + w‖ ^ 2 := by
    unfold secSq
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith [Complex.re_le_norm w])]
    linarith
  have hS' : x + ‖w‖ ≤ secSq w * ‖(x : ℂ) + w‖ := by
    have : (x + ‖w‖) ^ 2 ≤ (secSq w * ‖(x : ℂ) + w‖) ^ 2 := by
      rw [mul_pow]
      calc (x + ‖w‖) ^ 2 ≤ secSq w * ‖(x : ℂ) + w‖ ^ 2 := hS
        _ ≤ secSq w ^ 2 * ‖(x : ℂ) + w‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 this
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, pow_succ, pow_succ,
    pow_succ (‖(x : ℂ) + w‖), pow_mul, pow_mul]
  calc ((x + ‖w‖) ^ 2) ^ N * (x + ‖w‖)
      ≤ (secSq w * ‖(x : ℂ) + w‖ ^ 2) ^ N * (secSq w * ‖(x : ℂ) + w‖) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hS N) hS' (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; ring

lemma norm_gF_even {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : 1 ≤ N) :
    ‖gF w (2 * N) x‖ ≤ ((2 * N - 1) ! : ℝ) * secSq w ^ N / (x + ‖w‖) ^ (2 * N) := by
  obtain ⟨M, hM⟩ : ∃ M, 2 * N = M + 1 := ⟨2 * N - 1, by omega⟩
  have hM' : 2 * N - 1 = M := by omega
  rw [hM', hM]
  simp only [gF, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]
  have := inv_norm_pow_even_le hw hx N
  rw [hM] at this
  calc (M ! : ℝ) / ‖(x : ℂ) + w‖ ^ (M + 1) = (M ! : ℝ) * (1 / ‖(x : ℂ) + w‖ ^ (M + 1)) := by ring
    _ ≤ (M ! : ℝ) * (secSq w ^ N / (x + ‖w‖) ^ (M + 1)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

/-- Per-interval bound on the Stirling remainder. -/
lemma norm_emR_gF_le {w : ℂ} (hw : 0 < w.re) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    ‖emR (gF w) (2 * N) k‖
      ≤ (2 * |(bernoulli (2 * N) : ℝ)| / ((2 * N) ! : ℝ) * (((2 * N - 1) ! : ℝ) * secSq w ^ N))
        * (1 / (((2 * N - 1 : ℕ) : ℝ) * ((k : ℝ) + ‖w‖) ^ (2 * N - 1))
          - 1 / (((2 * N - 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + ‖w‖) ^ (2 * N - 1))) := by
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le hw (Complex.re_le_norm w)
  refine (norm_emR_le ((gF_gchain hw).derivChain hk0) N hN).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hint := integral_inv_pow_unit hw0 hk0 (q := 2 * N - 1) (by omega)
  have e : 2 * N - 1 + 1 = 2 * N := by omega
  rw [e] at hint
  push_cast
  rw [← hint, ← integral_const_mul]
  apply integral_mono_on (by linarith)
  · exact ((gF_gchain hw).derivChain hk0).continuousOn _ |>.norm |>.intervalIntegrable
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
    have := norm_gF_even hw hx0 hN
    calc ‖gF w (2 * N) x‖ ≤ ((2 * N - 1) ! : ℝ) * secSq w ^ N / (x + ‖w‖) ^ (2 * N) := this
      _ = _ := by ring

/-- The complex Stirling remainder (Euler–Maclaurin tail of order `2N`). -/
noncomputable def gammaR (w : ℂ) (N : ℕ) : ℂ := ∑' k : ℕ, emR (gF w) (2 * N) k

lemma gammaR_summable_bound {w : ℂ} (hw : 0 < w.re) {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun k : ℕ => emR (gF w) (2 * N) k) ∧
    ‖gammaR w N‖ ≤ 2 * |(bernoulli (2 * N) : ℝ) / ((2 * (N : ℝ)) * (2 * (N : ℝ) - 1))|
        * secSq w ^ N / ‖w‖ ^ (2 * N - 1) := by
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le hw (Complex.re_le_norm w)
  have hS := one_le_secSq hw
  obtain ⟨hs, hb⟩ := summable_of_telescope (e := fun k : ℕ => emR (gF w) (2 * N) k)
    (h := fun k : ℕ => 1 / (((2 * N - 1 : ℕ) : ℝ) * ((k : ℝ) + ‖w‖) ^ (2 * N - 1)))
    (by positivity) (fun k => by positivity) (fun k => norm_emR_gF_le hw hN k)
  refine ⟨hs, hb.trans (le_of_eq ?_)⟩
  simp only [Nat.cast_zero, zero_add]
  have hfac : ((2 * N) ! : ℝ) = (2 * N : ℝ) * ((2 * N - 1) ! : ℝ) := by
    obtain ⟨M, hM⟩ : ∃ M, 2 * N = M + 1 := ⟨2 * N - 1, by omega⟩
    have hM' : 2 * N - 1 = M := by omega
    rw [hM', hM, Nat.factorial_succ, Nat.cast_mul]
    have : ((M + 1 : ℕ) : ℝ) = 2 * (N : ℝ) := by rw [← hM]; push_cast; ring
    rw [this]
  have hc : ((2 * N - 1 : ℕ) : ℝ) = 2 * (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hpos : 0 < 2 * (N : ℝ) - 1 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hfac, hc, abs_div, abs_of_pos (by positivity : 0 < 2 * (N : ℝ) * (2 * (N : ℝ) - 1))]
  field_simp

end EMCore
