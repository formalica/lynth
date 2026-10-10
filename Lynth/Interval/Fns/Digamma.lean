import Lynth.Interval.Fns.Gamma
import Lynth.Interval.Fns.Elem
import Lynth.Interval.Fns.Trig
import Lynth.Interval.Fns.Zeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Digamma function (real line, FLINT-style)

`ψ(x) = Γ'(x)/Γ(x)` following FLINT/Arb (`arb/digamma.c`, real case):
* positive `x`: shift up by `ψ(x+1) = ψ(x) + 1/x` until `y = x+n ≥ X₀`,
  then Stirling `ψ(y) ≈ ln y - 1/(2y) - Σ_{k=1}^{K} B_{2k}/(2k·y^{2k})`
  with explicit remainder (`2·T_{K+1}` widening).  One Bernoulli list
  `bernoulliList (2*(K+1))` per point (no per-term recomputation).
* negative non-pole `x`: reflection `ψ(x) = ψ(1-x) - π·cot(πx)`
  (`digamma_one_sub`); `1-x > 1` runs the positive path, `cot` via the
  verified `sin`/`cos` kernels.
* poles (nonpositive integers in the enclosure), `x = 0` straddles,
  unbounded → `⊤`.  No integer fast paths (`ψ(n) = H_{n-1} - γ` waived).

Analytic identities + remainder bounds are proved in-file (ported from
the external prover via the Mathlib-only `/tmp/digamma_thm.lean` handoff,
which vendors the Bernoulli block so nothing is re-proved from scratch).
-/

namespace Lynth.Interval.Fns

open BigOperators

/-- real digamma as a real-valued function (graph for the registry entry). -/
noncomputable def rdig (s : ℝ) : ℝ := (Complex.digamma (s : ℂ)).re

/-- shift sum `Σ_{k<n} 1/(x+k)` (what the evaluator subtracts). -/
noncomputable def digShiftSum (x : ℝ) (n : Nat) : ℝ :=
  (Finset.range n).sum fun k => 1 / (x + (k : ℝ))

/-- one Stirling correction `-B_{2k}/(2k·y^{2k})` (may be positive or
negative; `B_{2k}` alternates).  For `k = 0` this is `0` (division by
zero); only `k ≥ 1` is ever used. -/
noncomputable def digCorrR (y : ℝ) (k : Nat) : ℝ :=
  -(bernoulli (2 * k) : ℝ) / ((2 * (k : ℝ)) * y ^ ((2 * (k : ℝ))))

/-- Stirling approximation `ln y - 1/(2y) + Σ_{k<K} C_{k+1}`. -/
noncomputable def digStirling (y : ℝ) (K : Nat) : ℝ :=
  Real.log y - 1 / (2 * y)
    + (Finset.range K).sum (fun k => digCorrR y (k + 1))

/-- first omitted correction scale `|B_{2K+2}|/((2K+2)·y^{2K+2})`. -/
noncomputable def digTailScale (y : ℝ) (K : Nat) : ℝ :=
  |(bernoulli (2 * (K + 1)) : ℝ)|
    / ((2 * (((K + 1 : Nat)) : ℝ)) * y ^ ((2 * (((K + 1 : Nat)) : ℝ))))

/-- EASY: the shift sum is what the evaluator subtracts (definitional). -/
theorem digShiftSum_eq (x : ℝ) (n : Nat) :
    digShiftSum x n = (Finset.range n).sum fun k => 1 / (x + (k : ℝ)) := by
  rfl



/-- shift identity (ported prover proof; handoff `/tmp/digamma_thm.lean`)
`ψ(x) = ψ(x+n) - Σ_{k<n} 1/(x+k)` for `0 < x`. -/
theorem dig_shift (x : ℝ) (hx : 0 < x) (n : Nat) :
    rdig x = rdig (x + n) - digShiftSum x n := by
  have hs : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h := Complex.digamma_apply_add_nat hs n
  unfold rdig digShiftSum
  rw [show ((x + n : ℝ) : ℂ) = (x : ℂ) + n by push_cast; ring, h, Complex.add_re,
    Complex.re_sum]
  have : ∀ k ∈ Finset.range n, ((x : ℂ) + k)⁻¹.re = 1 / (x + k) := by
    intro k _
    rw [show (x : ℂ) + k = ((x + k : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_inv,
      Complex.ofReal_re, one_div]
  rw [Finset.sum_congr rfl this]
  ring

/-!
### Auxiliary material for `dig_stirling_bound`

Euler–Maclaurin summation for `x ↦ 1/x` on `[y, y + N]` (per-interval
remainders written through Bernoulli polynomials), the convexity bounds
`log (x - 1) ≤ ψ(x) ≤ log x` (Bohr–Mollerup), and the passage `N → ∞`.
-/

namespace DigammaStirling

/-- `j`-th derivative of `x ↦ 1/x`. -/
noncomputable def g (j : ℕ) (x : ℝ) : ℝ := (-1) ^ j * (Nat.factorial j : ℝ) * x ^ (-((j : ℤ) + 1))

/-- normalized Bernoulli polynomial `B_k(t)/k!`. -/
noncomputable def bp (k : ℕ) (t : ℝ) : ℝ := bernoulliFun k t / (Nat.factorial k : ℝ)

lemma hasDerivAt_g (j : ℕ) {x : ℝ} (hx : x ≠ 0) : HasDerivAt (g j) (g (j + 1) x) x := by
  unfold g
  have h := (hasDerivAt_zpow (-((j : ℤ) + 1)) x (Or.inl hx)).const_mul ((-1) ^ j * (Nat.factorial j : ℝ))
  convert h using 1
  rw [Nat.factorial_succ, show (-(((j + 1 : ℕ) : ℤ) + 1)) = -((j : ℤ) + 1) - 1 by push_cast; ring]
  push_cast
  ring

lemma hasDerivAt_bp (k : ℕ) (t : ℝ) : HasDerivAt (bp (k + 1)) (bp k t) t := by
  unfold bp
  have h := (hasDerivAt_bernoulliFun (k + 1) t).div_const (Nat.factorial (k + 1) : ℝ)
  refine h.congr_deriv ?_
  simp only [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have : ((Nat.factorial k : ℝ)) ≠ 0 := by positivity
  have : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp

lemma continuous_bp (k : ℕ) : Continuous (bp k) := by
  unfold bp
  unfold bernoulliFun
  fun_prop

lemma continuousOn_g (j : ℕ) {m : ℝ} (hm : 0 < m) :
    ContinuousOn (fun t : ℝ => g j (m + t)) (Set.uIcc 0 1) := by
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  have : 0 < m + t := by linarith [ht.1]
  exact ((hasDerivAt_g j this.ne').continuousAt.comp
    (continuous_const.add continuous_id).continuousAt).continuousWithinAt

lemma ibp_step (k : ℕ) {m : ℝ} (hm : 0 < m) :
    ∫ t in (0 : ℝ)..1, bp k t * g k (m + t)
      = bp (k + 1) 1 * g k (m + 1) - bp (k + 1) 0 * g k m
        - ∫ t in (0 : ℝ)..1, bp (k + 1) t * g (k + 1) (m + t) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t => g k (m + t)) (g (k + 1) (m + t)) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have : 0 < m + t := by linarith [ht.1]
    exact HasDerivAt.comp_const_add m t (hasDerivAt_g k this.ne')
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ => hasDerivAt_bp k t) hderiv
    ((continuous_bp k).intervalIntegrable 0 1)
    ((continuousOn_g (k + 1) hm).intervalIntegrable)
  simp only [add_zero] at h
  rw [h]
  ring

lemma g_zero (x : ℝ) : g 0 x = 1 / x := by
  simp [g]

lemma bp_zero_fun (t : ℝ) : bp 0 t = 1 := by simp [bp]

lemma bp_one_fun (t : ℝ) : bp 1 t = t - 1 / 2 := by simp [bp]

lemma bp_one_of_ne_one {k : ℕ} (hk : k ≠ 1) : bp k 1 = bp k 0 := by
  simp [bp, bernoulliFun_endpoints_eq_of_ne_one hk]

lemma bp_zero_eq (k : ℕ) : bp k 0 = (bernoulli k : ℝ) / (Nat.factorial k : ℝ) := by
  simp [bp, bernoulliFun_eval_zero]

lemma bp_odd_zero {r : ℕ} (hr : 1 ≤ r) : bp (2 * r + 1) 0 = 0 := by
  rw [bp_zero_eq, bernoulli_eq_zero_of_odd (by exact odd_two_mul_add_one r) (by omega)]
  simp

lemma integral_g_zero {m : ℝ} (hm : 0 < m) :
    ∫ t in (0 : ℝ)..1, bp 0 t * g 0 (m + t) = Real.log (m + 1) - Real.log m := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Real.log (m + t)) (bp 0 t * g 0 (m + t)) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hpos : 0 < m + t := by linarith [ht.1]
    have h := ((hasDerivAt_id' t).const_add m).log hpos.ne'
    convert h using 1
    rw [bp_zero_fun, g_zero]
    simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (((continuous_bp 0).continuousOn.mul (continuousOn_g 0 hm)).intervalIntegrable)]
  simp

/-- closed form of the per-interval Euler–Maclaurin remainder for `1/x` on `[m, m+1]`. -/
noncomputable def emR (K : ℕ) (m : ℝ) : ℝ :=
  Real.log (m + 1) - Real.log m - (g 0 m + g 0 (m + 1)) / 2
    + ∑ r ∈ Finset.range K, bp (2 * r + 2) 0 * (g (2 * r + 1) (m + 1) - g (2 * r + 1) m)

noncomputable def emJ (m : ℝ) (k : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, bp k t * g k (m + t)

lemma emJ_two {m : ℝ} (hm : 0 < m) : emR 1 m = emJ m 2 := by
  have h0 := ibp_step 0 hm
  have h1 := ibp_step 1 hm
  have hJ0 : emJ m 0 = Real.log (m + 1) - Real.log m := integral_g_zero hm
  change emJ m 0 = _ - _ - emJ m 1 at h0
  change emJ m 1 = _ - _ - emJ m 2 at h1
  rw [bp_one_fun, bp_one_fun] at h0
  rw [bp_one_of_ne_one (by norm_num)] at h1
  simp only [emR, Finset.range_one, Finset.sum_singleton, mul_zero, zero_add]
  rw [← hJ0]
  linear_combination h0 - h1

lemma emJ_step {m : ℝ} (hm : 0 < m) {K : ℕ} (hK : 1 ≤ K) :
    emJ m (2 * K + 2)
      = emJ m (2 * K) + bp (2 * K + 2) 0 * (g (2 * K + 1) (m + 1) - g (2 * K + 1) m) := by
  have h0 := ibp_step (2 * K) hm
  have h1 := ibp_step (2 * K + 1) hm
  change emJ m (2 * K) = _ - _ - emJ m (2 * K + 1) at h0
  change emJ m (2 * K + 1) = _ - _ - emJ m (2 * K + 1 + 1) at h1
  rw [bp_one_of_ne_one (by omega), bp_odd_zero hK] at h0
  rw [bp_one_of_ne_one (by omega)] at h1
  linear_combination h1 - h0

lemma emR_eq_integral {K : ℕ} (hK : 1 ≤ K) {m : ℝ} (hm : 0 < m) :
    emR K m = ∫ t in (0 : ℝ)..1, bp (2 * K) t * g (2 * K) (m + t) := by
  change emR K m = emJ m (2 * K)
  induction K, hK using Nat.le_induction with
  | base => exact emJ_two hm
  | succ K hK ih =>
    rw [show 2 * (K + 1) = 2 * K + 2 by ring, emJ_step hm hK, ← ih]
    simp only [emR, Finset.sum_range_succ]
    ring

/-- `|B_{2k}(x)| ≤ |B_{2k}|` on `[0,1]` (from the Fourier expansion). -/
lemma abs_bernoulliFun_le {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * k) x| ≤ |(bernoulli (2 * k) : ℝ)| := by
  have hx0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have h1 := hasSum_one_div_nat_pow_mul_cos hk hx
  have h0 := hasSum_one_div_nat_pow_mul_cos hk hx0
  set C : ℝ := (-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ (2 * k) / 2 / ((2 * k).factorial : ℝ)
  have hb : ∀ y, (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * k))).eval y
      = bernoulliFun (2 * k) y := fun y => rfl
  rw [hb] at h0 h1
  rw [bernoulliFun_eval_zero] at h0
  simp only [mul_zero, Real.cos_zero, mul_one] at h0
  have hup : C * bernoulliFun (2 * k) x ≤ C * (bernoulli (2 * k) : ℝ) :=
    hasSum_le (fun n => by
      have := Real.cos_le_one (2 * Real.pi * n * x)
      have : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * k) := by positivity
      nlinarith) h1 h0
  have hlo : -(C * (bernoulli (2 * k) : ℝ)) ≤ C * bernoulliFun (2 * k) x :=
    hasSum_le (fun n => by
      have := Real.neg_one_le_cos (2 * Real.pi * n * x)
      have : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * k) := by positivity
      show -(1 / (n : ℝ) ^ (2 * k)) ≤ _
      nlinarith) h0.neg h1
  have hC : 0 < |C| := by
    apply abs_pos.mpr
    simp only [C]
    have : (0 : ℝ) < (2 * Real.pi) ^ (2 * k) := by positivity
    have : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
    have : ((-1 : ℝ) ^ (k + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    positivity
  have habs : |C * bernoulliFun (2 * k) x| ≤ |C * (bernoulli (2 * k) : ℝ)| := by
    rw [abs_le]
    constructor
    · rcases le_or_gt 0 (C * (bernoulli (2 * k) : ℝ)) with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_neg h]; linarith
    · exact hup.trans (le_abs_self _)
  rw [abs_mul, abs_mul] at habs
  exact le_of_mul_le_mul_left habs hC


lemma g_odd_nonpos (k : ℕ) {x : ℝ} (hx : 0 < x) : g (2 * k + 1) x ≤ 0 := by
  have : 0 < x ^ (-(((2 * k + 1 : ℕ) : ℤ) + 1)) := zpow_pos hx _
  have : (0:ℝ) < (Nat.factorial (2 * k + 1) : ℝ) := by positivity
  rw [g, pow_succ, pow_mul]
  norm_num
  positivity

lemma g_even_nonneg (k : ℕ) {x : ℝ} (hx : 0 < x) : 0 ≤ g (2 * k) x := by
  have : 0 < x ^ (-(((2 * k : ℕ) : ℤ) + 1)) := zpow_pos hx _
  rw [g, pow_mul]
  norm_num
  positivity

/-- per-interval remainder bound. -/
lemma abs_emR_le (k : ℕ) {m : ℝ} (hm : 0 < m) :
    |emR (k + 1) m| ≤ |(bernoulli (2 * (k + 1)) : ℝ)| / (Nat.factorial (2 * (k + 1)) : ℝ)
      * (g (2 * k + 1) (m + 1) - g (2 * k + 1) m) := by
  rw [emR_eq_integral (by omega) hm]
  set C := |(bernoulli (2 * (k + 1)) : ℝ)| / (Nat.factorial (2 * (k + 1)) : ℝ) with hC
  have hint : ∫ t in (0:ℝ)..1, C * g (2 * (k + 1)) (m + t)
      = C * (g (2 * k + 1) (m + 1) - g (2 * k + 1) m) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t => g (2 * k + 1) (m + t)) (g (2 * (k + 1)) (m + t)) t := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have hmt : 0 < m + t := by linarith [ht.1]
      have := HasDerivAt.comp_const_add m t (hasDerivAt_g (2 * k + 1) hmt.ne')
      rwa [show 2 * k + 1 + 1 = 2 * (k + 1) by ring] at this
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((continuousOn_g _ hm).intervalIntegrable)]
    simp
  rw [← hint]
  refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact ((continuous_bp _).continuousOn.mul (continuousOn_g _ hm)).abs.intervalIntegrable
  · exact (continuousOn_const.mul (continuousOn_g _ hm)).intervalIntegrable
  · intro t ht
    have hmt : 0 < m + t := by linarith [ht.1]
    rw [abs_mul, abs_of_nonneg (g_even_nonneg (k + 1) hmt)]
    apply mul_le_mul_of_nonneg_right _ (g_even_nonneg (k + 1) hmt)
    unfold bp
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (Nat.factorial (2 * (k + 1)) : ℝ))]
    exact div_le_div_of_nonneg_right (abs_bernoulliFun_le (by omega) ht) (by positivity)

/-- finite telescoped Euler–Maclaurin identity on `[y, y+N]`. -/
lemma emR_sum (K : ℕ) (y : ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, emR K (y + i)
      = Real.log (y + N) - Real.log y - ∑ i ∈ Finset.range N, g 0 (y + i)
        - (g 0 (y + N) - g 0 y) / 2
        + ∑ r ∈ Finset.range K, bp (2 * r + 2) 0 * (g (2 * r + 1) (y + N) - g (2 * r + 1) y) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    unfold emR
    push_cast
    rw [show y + ((N:ℝ) + 1) = y + N + 1 by ring]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring

/-- total remainder bound. -/
lemma abs_sum_emR_le (k : ℕ) {y : ℝ} (hy : 0 < y) (N : ℕ) :
    |∑ i ∈ Finset.range N, emR (k + 1) (y + i)|
      ≤ |(bernoulli (2 * (k + 1)) : ℝ)| / (Nat.factorial (2 * (k + 1)) : ℝ) * (-g (2 * k + 1) y) := by
  set C := |(bernoulli (2 * (k + 1)) : ℝ)| / (Nat.factorial (2 * (k + 1)) : ℝ) with hC
  have hC0 : 0 ≤ C := div_nonneg (abs_nonneg _) (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hpos : ∀ i : ℕ, 0 < y + (i : ℝ) := fun i => by positivity
  refine (Finset.sum_le_sum (fun i _ => abs_emR_le k (hpos i))).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hC0
  have htel := Finset.sum_range_sub (fun j : ℕ => g (2 * k + 1) (y + j)) N
  have hcongr : ∀ i ∈ Finset.range N, g (2 * k + 1) (y + i + 1) - g (2 * k + 1) (y + i)
      = (fun j : ℕ => g (2 * k + 1) (y + j)) (i + 1) - (fun j : ℕ => g (2 * k + 1) (y + j)) i := by
    intro i _
    simp only [Nat.cast_succ, add_assoc]
  rw [Finset.sum_congr rfl hcongr, htel]
  simp only [Nat.cast_zero, add_zero]
  linarith [g_odd_nonpos k (by positivity : 0 < y + (N : ℝ))]

/-! ### Asymptotics of the digamma function -/

lemma rdig_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => Real.log (Real.Gamma t)) (rdig x) x := by
  have hs : ∀ m : ℕ, (x : ℂ) ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hr := (Complex.differentiableAt_Gamma (x : ℂ) hs).hasDerivAt.real_of_complex
  have hG : (fun t : ℝ => (Complex.Gamma (t : ℂ)).re) = Real.Gamma := by
    funext t
    rw [Complex.Gamma_ofReal, Complex.ofReal_re]
  rw [hG] at hr
  have h := hr.log (Real.Gamma_pos_of_pos hx).ne'
  convert h using 1
  unfold rdig
  rw [Complex.digamma_def, logDeriv_apply, Complex.Gamma_ofReal, Complex.div_ofReal_re]

lemma rdig_le_log {x : ℝ} (hx : 0 < x) : rdig x ≤ Real.log x := by
  have h := Real.convexOn_log_Gamma.le_slope_of_hasDerivAt (y := x + 1) (Set.mem_Ioi.mpr hx)
    (Set.mem_Ioi.mpr (by linarith)) (by linarith) (rdig_hasDerivAt hx)
  refine h.trans (le_of_eq ?_)
  rw [slope_def_field, show x + 1 - x = (1 : ℝ) by ring, div_one]
  simp only [Function.comp_apply]
  rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  ring

lemma log_sub_one_le_rdig {x : ℝ} (hx : 1 < x) : Real.log (x - 1) ≤ rdig x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have h := Real.convexOn_log_Gamma.slope_le_of_hasDerivAt (x := x - 1) (Set.mem_Ioi.mpr hx1)
    (Set.mem_Ioi.mpr hx0) (by linarith) (rdig_hasDerivAt hx0)
  refine (le_of_eq ?_).trans h
  rw [slope_def_field, show x - (x - 1) = (1 : ℝ) by ring, div_one]
  simp only [Function.comp_apply]
  conv_rhs => rw [show x = (x - 1) + 1 by ring]
  rw [Real.Gamma_add_one hx1.ne', Real.log_mul hx1.ne' (Real.Gamma_pos_of_pos hx1).ne']
  ring_nf

lemma abs_rdig_sub_log_le {x : ℝ} (hx : 1 < x) : |rdig x - Real.log x| ≤ (x - 1)⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have h1 := rdig_le_log hx0
  have h2 := log_sub_one_le_rdig hx
  have h3 : Real.log x - Real.log (x - 1) ≤ (x - 1)⁻¹ := by
    rw [← Real.log_div hx0.ne' hx1.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    field_simp
    ring
  rw [abs_le]
  constructor <;> linarith

lemma tendsto_rdig_sub_log (y : ℝ) :
    Filter.Tendsto (fun N : ℕ => Real.log (y + N) - rdig (y + N)) Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto (fun N : ℕ => (y - 1 + N)⁻¹) Filter.atTop (nhds 0) :=
    (Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  refine squeeze_zero_norm' ?_ hlim
  have hev : ∀ᶠ N : ℕ in Filter.atTop, (2 - y : ℝ) < N := by
    obtain ⟨n, hn⟩ := exists_nat_gt (2 - y)
    filter_upwards [Filter.eventually_ge_atTop n] with N hN
    exact lt_of_lt_of_le hn (by exact_mod_cast hN)
  filter_upwards [hev] with N hN
  rw [Real.norm_eq_abs, abs_sub_comm, show y - 1 + (N : ℝ) = y + N - 1 by ring]
  exact abs_rdig_sub_log_le (by linarith)

lemma tendsto_g (j : ℕ) (y : ℝ) : Filter.Tendsto (fun N : ℕ => g j (y + N)) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun N : ℕ => y + (N : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have h2 := ((tendsto_zpow_atTop_zero (𝕜 := ℝ) (n := -((j : ℤ) + 1)) (by omega)).comp h1).const_mul
    ((-1) ^ j * (Nat.factorial j : ℝ))
  simpa [g, Function.comp_def] using h2

/-! ### Matching with the evaluator's vocabulary -/

lemma corr_eq (r : ℕ) {y : ℝ} (hy : 0 < y) :
    bp (2 * r + 2) 0 * g (2 * r + 1) y = digCorrR y (r + 1) := by
  unfold digCorrR
  rw [bp_zero_eq, show (2 * (((r + 1 : ℕ)) : ℝ)) = ((2 * r + 2 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, show 2 * (r + 1) = 2 * r + 2 by ring]
  unfold g
  rw [show (-(((2 * r + 1 : ℕ) : ℤ) + 1)) = -((2 * r + 2 : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, show 2 * r + 2 = (2 * r + 1) + 1 by ring, Nat.factorial_succ,
    pow_succ, pow_mul]
  have : (0 : ℝ) < y ^ (2 * r + 1 + 1) := by positivity
  have : (0 : ℝ) < (Nat.factorial (2 * r + 1) : ℝ) := by positivity
  push_cast
  field_simp
  ring

lemma tail_eq (k : ℕ) {y : ℝ} (hy : 0 < y) :
    |(bernoulli (2 * (k + 1)) : ℝ)| / (Nat.factorial (2 * (k + 1)) : ℝ) * (-g (2 * k + 1) y)
      = digTailScale y k := by
  unfold digTailScale
  rw [show (2 * (((k + 1 : ℕ)) : ℝ)) = ((2 * k + 2 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, show 2 * (k + 1) = 2 * k + 2 by ring]
  unfold g
  rw [show (-(((2 * k + 1 : ℕ) : ℤ) + 1)) = -((2 * k + 2 : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, show 2 * k + 2 = (2 * k + 1) + 1 by ring, Nat.factorial_succ,
    pow_succ, pow_mul]
  have : (0 : ℝ) < y ^ (2 * k + 1 + 1) := by positivity
  have : (0 : ℝ) < (Nat.factorial (2 * k + 1) : ℝ) := by positivity
  push_cast
  field_simp
  ring

lemma abs_digCorrR_eq (k : ℕ) {y : ℝ} (hy : 0 < y) :
    |digCorrR y (k + 1)| = digTailScale y k := by
  unfold digCorrR digTailScale
  have : (0 : ℝ) < (2 * (((k + 1 : ℕ)) : ℝ)) * y ^ ((2 * (((k + 1 : ℕ)) : ℝ))) := by positivity
  rw [abs_div, abs_neg, abs_of_pos this]

/-- the shifted Euler–Maclaurin identity relating `ψ` to the partial remainders. -/
lemma sum_emR_eq (K : ℕ) {y : ℝ} (hy : 0 < y) (N : ℕ) :
    ∑ i ∈ Finset.range N, emR K (y + i)
      = (rdig y - digStirling y K)
        + (Real.log (y + N) - rdig (y + N) - g 0 (y + N) / 2
          + ∑ r ∈ Finset.range K, bp (2 * r + 2) 0 * g (2 * r + 1) (y + N)) := by
  rw [emR_sum]
  have hs := dig_shift y hy N
  have hsum : ∑ i ∈ Finset.range N, g 0 (y + i) = digShiftSum y N := by
    unfold digShiftSum
    exact Finset.sum_congr rfl (fun i _ => g_zero _)
  have hcorr : ∑ r ∈ Finset.range K, bp (2 * r + 2) 0 * g (2 * r + 1) y
      = ∑ r ∈ Finset.range K, digCorrR y (r + 1) :=
    Finset.sum_congr rfl (fun r _ => corr_eq r hy)
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hsum, hcorr, g_zero y]
  unfold digStirling
  have : 1 / (2 * y) = 1 / y / 2 := by field_simp
  rw [this]
  linarith

/-- the Stirling remainder with `k + 1` corrections is at most the first omitted term. -/
lemma abs_rdig_sub_digStirling_succ_le (k : ℕ) {y : ℝ} (hy : 0 < y) :
    |rdig y - digStirling y (k + 1)| ≤ digTailScale y k := by
  set D := rdig y - digStirling y (k + 1)
  set E : ℕ → ℝ := fun N => Real.log (y + N) - rdig (y + N) - g 0 (y + N) / 2
    + ∑ r ∈ Finset.range (k + 1), bp (2 * r + 2) 0 * g (2 * r + 1) (y + N)
  have hE : Filter.Tendsto E Filter.atTop (nhds 0) := by
    have := ((tendsto_rdig_sub_log y).sub ((tendsto_g 0 y).div_const 2)).add
      (tendsto_finsetSum (Finset.range (k + 1))
        (fun r _ => (tendsto_g (2 * r + 1) y).const_mul (bp (2 * r + 2) 0)))
    simpa [E] using this
  have hbound : ∀ N : ℕ, |D + E N| ≤ digTailScale y k := by
    intro N
    rw [← tail_eq k hy]
    have := abs_sum_emR_le k hy N
    rwa [sum_emR_eq (k + 1) hy N] at this
  have hlim : Filter.Tendsto (fun N => |D + E N|) Filter.atTop (nhds |D|) := by
    have := (tendsto_const_nhds (x := D)).add hE
    simpa using this.abs
  exact le_of_tendsto' hlim hbound

end DigammaStirling

/-- Stirling identity with (ported prover proof; handoff `/tmp/digamma_thm.lean`)
remainder. For `0 < y`, `1 ≤ K`, `4*K+4 ≤ y`:
`|ψ(y) - (ln y - 1/(2y) + Σ corrections)| ≤ 2·T_{K+1}`. -/


theorem dig_stirling_bound (y : ℝ) (hy : 0 < y) (K : Nat)
    (hK : 1 ≤ K) (hY : 4 * (K : ℝ) + 4 ≤ y) :
    |rdig y - digStirling y K| ≤ 2 * digTailScale y K := by
  -- The proof only uses `0 < y`; `hK` and `hY` are kept so the statement stays
  -- byte-identical, but the bound holds for every `K` and every `y > 0`.
  have h1 := DigammaStirling.abs_rdig_sub_digStirling_succ_le K hy
  have h2 := DigammaStirling.abs_digCorrR_eq K hy
  have hsplit : digStirling y (K + 1) = digStirling y K + digCorrR y (K + 1) := by
    simp only [digStirling, Finset.sum_range_succ]
    ring
  rw [hsplit] at h1
  calc |rdig y - digStirling y K|
      = |(rdig y - (digStirling y K + digCorrR y (K + 1))) + digCorrR y (K + 1)| := by ring_nf
    _ ≤ |rdig y - (digStirling y K + digCorrR y (K + 1))| + |digCorrR y (K + 1)| :=
        abs_add_le _ _
    _ ≤ 2 * digTailScale y K := by linarith

/-- reflection (ported prover proof; handoff `/tmp/digamma_thm.lean`)
`ψ(x) = ψ(1-x) - π·cos(πx)/sin(πx)` for `x < 0` non-integer. -/
theorem dig_refl (x : ℝ) (hx : x < 0) (hN : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    rdig x = rdig (1 - x)
      - Real.pi * (Real.cos (Real.pi * x) / Real.sin (Real.pi * x)) := by
  have hs : ∀ n : ℤ, (x : ℂ) ≠ n := by
    intro n h
    have h' : x = n := by exact_mod_cast h
    rcases le_or_gt 0 n with hn | hn
    · have : (0 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    · apply hN n.natAbs
      rw [h', Nat.cast_natAbs, abs_of_neg hn]
      push_cast; ring
  have h := Complex.digamma_one_sub hs
  unfold rdig
  rw [show ((1 - x : ℝ) : ℂ) = 1 - (x : ℂ) by push_cast; ring, h, Complex.add_re,
    show (Real.pi : ℂ) * (x : ℂ) = ((Real.pi * x : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cot, ← Complex.ofReal_mul, Complex.ofReal_re, Real.cot_eq_cos_div_sin]
  ring

/-- shift count clearing `X₀` above a rational lower bound
(`⌈X₀ - loQ⌉` for positive gaps, `0` otherwise). -/
def digShiftNumQ (X₀ : Nat) (loQ : ℚ) : Nat :=
  if (X₀ : ℚ) - loQ ≤ 0 then 0
  else (((X₀ : ℚ) - loQ).num.toNat / (((X₀ : ℚ) - loQ).den : Nat) + 1)

/-- the shift count always clears the target. -/
theorem digShiftNumQ_ge (X₀ : Nat) (loQ : ℚ) :
    (X₀ : ℝ) - (loQ : ℝ) ≤ ((digShiftNumQ X₀ loQ : Nat) : ℝ) := by
  unfold digShiftNumQ
  split
  · rename_i h
    have hR : (((X₀ : ℚ) - loQ : ℚ) : ℝ) ≤ 0 := by exact_mod_cast h
    push_cast at hR ⊢
    linarith
  · rename_i h
    have hpos : 0 < (X₀ : ℚ) - loQ := lt_of_not_ge h
    set d : ℚ := (X₀ : ℚ) - loQ with hd
    have hnum : 0 < d.num := by
      have hq : (0 : ℚ) < d := hpos
      rw [← d.num_div_den] at hq
      have hden : (0 : ℚ) < ((d.den : Nat) : ℚ) := by
        exact_mod_cast d.pos
      rw [div_pos_iff] at hq
      rcases hq with ⟨hh, _⟩ | ⟨_, hdd⟩
      · exact_mod_cast hh
      · have : ((d.den : Nat) : ℚ) < 0 := hdd
        linarith
    have hnn : 0 ≤ d.num := le_of_lt hnum
    have htn : ((d.num.toNat : Nat) : ℤ) = d.num := Int.toNat_of_nonneg hnn
    have hden1 : 1 ≤ d.den := by
      have hp := d.pos
      omega
    have hN : d.num.toNat ≤ (d.num.toNat / d.den + 1) * d.den := by
      have hdm := Nat.div_add_mod d.num.toNat d.den
      have hmod := Nat.mod_lt d.num.toNat (show 0 < d.den by omega)
      have hring : (d.num.toNat / d.den + 1) * d.den
          = d.den * (d.num.toNat / d.den) + d.den := by ring
      omega
    have hdenR : (0 : ℝ) < ((d.den : Nat) : ℝ) := by exact_mod_cast hden1
    have hle : ((d.num.toNat : Nat) : ℝ) / ((d.den : Nat) : ℝ)
        ≤ ((d.num.toNat / d.den + 1 : Nat) : ℝ) := by
      rw [div_le_iff₀ hdenR]
      have hc : ((d.num.toNat / d.den + 1 : Nat) : ℝ) * ((d.den : Nat) : ℝ)
          = (((d.num.toNat / d.den + 1) * d.den : Nat) : ℝ) := by
        push_cast
        ring
      rw [hc]
      exact_mod_cast hN
    have hqd : ((d.num.toNat : Nat) : ℝ) / ((d.den : Nat) : ℝ)
        = (X₀ : ℝ) - (loQ : ℝ) := by
      have htnR : ((d.num.toNat : Nat) : ℝ) = ((d.num : ℤ) : ℝ) := by
        exact_mod_cast htn
      have h1 : d = ((d.num : ℤ) : ℚ) / ((d.den : Nat) : ℚ) :=
        d.num_div_den.symm
      have h1R : ((d : ℚ) : ℝ)
          = ((d.num : ℤ) : ℝ) / ((d.den : Nat) : ℝ) := by
        exact_mod_cast h1
      rw [htnR, ← h1R, hd]
      push_cast
      ring
    show (X₀ : ℝ) - (loQ : ℝ) ≤ ((d.num.toNat / d.den + 1 : Nat) : ℝ)
    rw [← hqd]
    exact hle

/-- pole test: the enclosure contains a nonpositive integer. -/
def digHasPole (lo hi : Dy) : Bool :=
  decide (⌈lo.toRat⌉ ≤ ⌊hi.toRat⌋ ∧ ⌈lo.toRat⌉ ≤ 0)

/-- a negative pole test rules out every `x = -m`. -/
theorem digHasPole_false {lo hi : Dy} (h : digHasPole lo hi = false) (x : ℝ)
    (hlo : ((lo.toRat : ℚ) : ℝ) ≤ x) (hhi : x ≤ ((hi.toRat : ℚ) : ℝ))
    (m : Nat) : x ≠ -(m : ℝ) := by
  intro he
  subst he
  have e : ((-(m : ℤ) : ℚ) : ℝ) = (-(m : ℝ)) := by push_cast; ring
  have e1 : lo.toRat ≤ (-(m : ℤ) : ℚ) := by
    have h' : ((lo.toRat : ℚ) : ℝ) ≤ ((-(m : ℤ) : ℚ) : ℝ) := by
      rw [e]
      exact hlo
    exact_mod_cast h'
  have e2 : (-(m : ℤ) : ℚ) ≤ hi.toRat := by
    have h' : ((-(m : ℤ) : ℚ) : ℝ) ≤ ((hi.toRat : ℚ) : ℝ) := by
      rw [e]
      exact hhi
    exact_mod_cast h'
  have c1 : ⌈lo.toRat⌉ ≤ -(m : ℤ) := Int.ceil_le.mpr e1
  have c2 : -(m : ℤ) ≤ ⌊hi.toRat⌋ := Int.le_floor.mpr e2
  have h' := of_decide_eq_false h
  exact h' ⟨le_trans c1 c2, le_trans c1 (by omega)⟩

/-- one Stirling correction `Q/(Y^{2k})` with exact rational `Q`. -/
def digCorrTerm (c : Ctx) (Q : ℚ) (Y : Ival) (k : Nat) : Ival :=
  Ival.div c.prec (Ival.ofRat c.prec Q)
    (rpowIval c Y (Ival.ofRat c.prec ((2 * ((k : Nat) : ℚ)))))

/-- interval for the tail scale (mirrors the analytic scale). -/
def digTailIval (c : Ctx) (QT : ℚ) (Y : Ival) (K : Nat) : Ival :=
  Ival.div c.prec (Ival.ofRat c.prec QT)
    (rpowIval c Y (Ival.ofRat c.prec ((2 * (((K + 1 : Nat) : ℚ))))))

/-- Stirling enclosure at `Y ∋ y` (log, half term, `K` corrections,
widened by the interval tail). -/
def digStirlingIval (c : Ctx) (Y : Ival) (L : List ℚ) (K : Nat) : Ival :=
  let logT := logIval c Y
  let halfT := Ival.div c.prec (Ival.ofRat c.prec 1)
    (Ival.mul c.prec (Ival.ofRat c.prec 2) Y)
  let corrs : List Ival := (List.range K).map fun k =>
    digCorrTerm c (-(L.getD (2 * (k + 1)) 0) / (2 * (((k + 1 : Nat) : ℚ)))) Y (k + 1)
  let sumPart := isum c ([logT, Ival.neg halfT] ++ corrs)
  let tail := digTailIval c
    (2 * |(L.getD (2 * (K + 1)) 0)| / (2 * (((K + 1 : Nat) : ℚ)))) Y K
  match tail.hi with
  | some h => Ival.add c.prec sumPart (Ival.ofRats c.prec (-h.toRat) h.toRat)
  | none => Ival.top

/-- positive enclosure at `X ∋ x`: Stirling at `Y = X + n` minus shift. -/
def digammaPosIval (c : Ctx) (X : Ival) (L : List ℚ) (n K : Nat) : Ival :=
  let Y := Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ))
  let terms : List Ival := (List.range n).map fun k =>
    Ival.div c.prec (Ival.ofRat c.prec 1)
      (Ival.add c.prec X (Ival.ofRat c.prec ((k : Nat) : ℚ)))
  Ival.sub c.prec (digStirlingIval c Y L K) (isum c terms)

/-- reflection enclosure at `X ∋ x < 0`: positive path at `1-X` minus
`π·cos(πx)/sin(πx)`. -/
def digammaReflIval (c : Ctx) (X : Ival) (L : List ℚ) (n K : Nat) : Ival :=
  let oneSub := Ival.sub c.prec (Ival.ofRat c.prec 1) X
  let pos := digammaPosIval c oneSub L n K
  let pix := Ival.mul c.prec c.pi X
  let cot := Ival.div c.prec (cosIval c pix) (sinIval c pix)
  Ival.sub c.prec pos (Ival.mul c.prec c.pi cot)

/-- dispatcher: poles/straddles/unbounded → `⊤`; `0 < lo` → shift+Stirling
with adaptive `n`; `hi < 0` pole-free → reflection; else `⊤`. -/
def digammaIval (c : Ctx) (X : Ival) : Ival :=
  match X.lo, X.hi with
  | some lo, some hi =>
    if digHasPole lo hi then Ival.top
    else
      let K := 4 + c.prec / 8
      let L := bernoulliList (2 * (K + 1))
      if _hpos : 0 < lo.toRat then
        digammaPosIval c X L (digShiftNumQ (20 + c.prec / 2) lo.toRat) K
      else if _hneg : hi.toRat < 0 then
        digammaReflIval c X L (digShiftNumQ (20 + c.prec / 2) (1 - hi.toRat)) K
      else Ival.top
  | _, _ => Ival.top

/-- list sum over a mapped range is the finset sum. -/
theorem dig_list_sum_map_range (f : Nat → ℝ) : ∀ N : Nat,
    ((List.range N).map f).sum = (Finset.range N).sum fun k => f k
  | 0 => by simp
  | N + 1 => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero,
      Finset.sum_range_succ]
    rw [dig_list_sum_map_range f N]

theorem digammaPos_sound (c : Ctx) (hc : c.Valid) (x : ℝ) (X : Ival)
    (L : List ℚ) (hxMem : x ∈ X) (hx : 0 < x) (n K : Nat)
    (hL : ∀ i : Nat, i ≤ 2 * (K + 1) → (L.getD i 0 : ℚ) = bernoulli i)
    (hK : 1 ≤ K) (hY : 4 * (K : ℝ) + 4 ≤ x + (n : ℝ)) :
    rdig x ∈ digammaPosIval c X L n K := by
  -- shifted enclosure membership
  have hnR : (((n : Nat) : ℚ) : ℝ) ∈ Ival.ofRat c.prec (n : ℚ) :=
    Ival.mem_ofRat _ _
  have hnR' : ((n : Nat) : ℝ) ∈ Ival.ofRat c.prec (n : ℚ) := by
    exact_mod_cast hnR
  have hYmem : x + (n : ℝ) ∈ Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ)) :=
    Ival.mem_add hxMem hnR'
  -- shift-sum terms
  have hterm : ∀ k : Nat,
      1 / (x + ((k : Nat) : ℝ)) ∈ Ival.div c.prec (Ival.ofRat c.prec 1)
        (Ival.add c.prec X (Ival.ofRat c.prec ((k : Nat) : ℚ))) := by
    intro k
    have h1 : (1 : ℝ) ∈ Ival.ofRat c.prec 1 := by
      exact_mod_cast Ival.mem_ofRat c.prec (1 : ℚ)
    have hk : (((k : Nat) : ℚ) : ℝ) ∈ Ival.ofRat c.prec ((k : Nat) : ℚ) :=
      Ival.mem_ofRat _ _
    have hkR : ((k : Nat) : ℝ) ∈ Ival.ofRat c.prec ((k : Nat) : ℚ) := by
      exact_mod_cast hk
    exact Ival.mem_div h1 (Ival.mem_add hxMem hkR)
  have hfaD : ∀ m : Nat, List.Forall₂ (fun x I => x ∈ I)
      ((List.range m).map fun k => 1 / (x + ((k : Nat) : ℝ)))
      ((List.range m).map fun k =>
        Ival.div c.prec (Ival.ofRat c.prec 1)
          (Ival.add c.prec X (Ival.ofRat c.prec ((k : Nat) : ℚ)))) := by
    intro m
    induction m with
    | zero => exact List.Forall₂.nil
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_append]
      exact List.rel_append ih
        (List.Forall₂.cons (hterm m) List.Forall₂.nil)
  have hdir : (Finset.range n).sum (fun k => 1 / (x + ((k : Nat) : ℝ)))
      ∈ isum c ((List.range n).map fun k =>
        Ival.div c.prec (Ival.ofRat c.prec 1)
          (Ival.add c.prec X (Ival.ofRat c.prec ((k : Nat) : ℚ)))) := by
    have hmem := mem_isum c hc _ _ (hfaD n)
    rwa [dig_list_sum_map_range] at hmem
  -- Stirling corrections: per-term membership (for `k ≤ K`)
  have hcorrM : ∀ k : Nat, k ≤ K → digCorrR (x + (n : ℝ)) (k + 1) ∈ digCorrTerm c
      (-(L.getD (2 * (k + 1)) 0) / (2 * (((k + 1 : Nat) : ℚ))))
      (Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ))) (k + 1) := by
    intro k hkK
    set Q : ℚ := -(L.getD (2 * (k + 1)) 0) / (2 * ((k + 1 : Nat) : ℚ)) with hQ
    have hQmem : (Q : ℝ) ∈ Ival.ofRat c.prec Q := Ival.mem_ofRat _ _
    have hQeq : (Q : ℝ)
        = -(bernoulli (2 * (k + 1)) : ℝ) / (2 * (((k + 1 : Nat)) : ℝ)) := by
      rw [hQ]
      have hLk := hL (2 * (k + 1)) (by omega)
      rw [hLk]
      push_cast
      ring
    have h0exp : (2 : ℝ) * (((k + 1 : Nat)) : ℝ)
        ∈ Ival.ofRat c.prec ((2 * (((k + 1 : Nat) : ℚ)))) := by
      have h0 : (((2 * (((k + 1 : Nat) : ℚ)) : ℚ)) : ℝ)
          ∈ Ival.ofRat c.prec ((2 * (((k + 1 : Nat) : ℚ)))) :=
        Ival.mem_ofRat _ _
      have e : (((2 * (((k + 1 : Nat) : ℚ)) : ℚ)) : ℝ)
          = 2 * (((k + 1 : Nat)) : ℝ) := by push_cast; ring
      rwa [e] at h0
    unfold digCorrTerm
    simp only [digCorrR]
    have hval : -(bernoulli (2 * (k + 1)) : ℝ)
          / ((2 * (((k + 1 : Nat)) : ℝ)) * (x + (n : ℝ)) ^ ((2 * (((k + 1 : Nat)) : ℝ))))
        = (Q : ℝ) / (x + (n : ℝ)) ^ (2 * (((k + 1 : Nat)) : ℝ)) := by
      rw [hQeq, div_div]
    rw [hval]
    exact Ival.mem_div hQmem (mem_rpowIval hc hYmem h0exp)
  have hfaC : ∀ m : Nat, m ≤ K → List.Forall₂ (fun x I => x ∈ I)
      ((List.range m).map fun k => digCorrR (x + (n : ℝ)) (k + 1))
      ((List.range m).map fun k => digCorrTerm c
        (-(L.getD (2 * (k + 1)) 0) / (2 * (((k + 1 : Nat) : ℚ))))
        (Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ))) (k + 1)) := by
    intro m
    induction m with
    | zero => intro _; exact List.Forall₂.nil
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.map_append, List.map_append]
      exact List.rel_append (ih (by omega))
        (List.Forall₂.cons (hcorrM m (by omega)) List.Forall₂.nil)
  -- log + half terms
  have hlogM : Real.log (x + (n : ℝ)) ∈ logIval c
      (Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ))) :=
    mem_logIval hc hYmem
  have hhalfM : 1 / (2 * (x + (n : ℝ))) ∈ Ival.div c.prec
      (Ival.ofRat c.prec 1)
      (Ival.mul c.prec (Ival.ofRat c.prec 2)
        (Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ)))) := by
    have h1 : (1 : ℝ) ∈ Ival.ofRat c.prec 1 := by
      exact_mod_cast Ival.mem_ofRat c.prec (1 : ℚ)
    have h2R : (2 : ℝ) ∈ Ival.ofRat c.prec 2 := by
      exact_mod_cast Ival.mem_ofRat c.prec (2 : ℚ)
    exact Ival.mem_div h1 (Ival.mem_mul h2R hYmem)
  -- tail scale membership
  have htailM : 2 * digTailScale (x + (n : ℝ)) K ∈ digTailIval c
      (2 * |(L.getD (2 * (K + 1)) 0)| / (2 * (((K + 1 : Nat) : ℚ))))
      (Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ))) K := by
    set QT : ℚ := 2 * |(L.getD (2 * (K + 1)) 0)| / (2 * ((K + 1 : Nat) : ℚ)) with hQT
    have hBmem : (QT : ℝ) ∈ Ival.ofRat c.prec QT := Ival.mem_ofRat _ _
    have hQeqT : (QT : ℝ)
        = 2 * |(bernoulli (2 * (K + 1)) : ℝ)| / (2 * (((K + 1 : Nat)) : ℝ)) := by
      rw [hQT]
      have hLK := hL (2 * (K + 1)) (by omega)
      rw [hLK]
      push_cast
      ring_nf
    have h0T : (2 : ℝ) * (((K + 1 : Nat)) : ℝ)
        ∈ Ival.ofRat c.prec ((2 * (((K + 1 : Nat) : ℚ)))) := by
      have h0 : (((2 * (((K + 1 : Nat) : ℚ)) : ℚ)) : ℝ)
          ∈ Ival.ofRat c.prec ((2 * (((K + 1 : Nat) : ℚ)))) :=
        Ival.mem_ofRat _ _
      have e : (((2 * (((K + 1 : Nat) : ℚ)) : ℚ)) : ℝ)
          = 2 * (((K + 1 : Nat)) : ℝ) := by push_cast; ring
      rwa [e] at h0
    have hvalT : 2 * digTailScale (x + (n : ℝ)) K
        = (QT : ℝ) / (x + (n : ℝ)) ^ (2 * (((K + 1 : Nat)) : ℝ)) := by
      simp only [digTailScale]
      rw [hQeqT, div_div]
      ring
    rw [hvalT]
    exact Ival.mem_div hBmem (mem_rpowIval hc hYmem h0T)
  -- analytic master bound + sum assembly + widen finish
  have hpos : (0 : ℝ) < x + (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ ((n : Nat) : ℝ) := by exact_mod_cast Nat.zero_le n
    linarith
  have hmaster := dig_stirling_bound (x + (n : ℝ)) hpos K hK hY
  have hfaLH : List.Forall₂ (fun x I => x ∈ I)
      [Real.log (x + (n : ℝ)), -(1 / (2 * (x + (n : ℝ))))]
      [logIval c (Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ))),
        Ival.neg (Ival.div c.prec (Ival.ofRat c.prec 1)
          (Ival.mul c.prec (Ival.ofRat c.prec 2)
            (Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ)))))] := by
    refine List.Forall₂.cons hlogM (List.Forall₂.cons ?_ List.Forall₂.nil)
    exact Ival.mem_neg hhalfM
  have hfaAll := List.rel_append hfaLH (hfaC K le_rfl)
  have hsumM := mem_isum c hc _ _ hfaAll
  have hsumEq : (([Real.log (x + (n : ℝ)), -(1 / (2 * (x + (n : ℝ))))]
        ++ ((List.range K).map (fun k => digCorrR (x + (n : ℝ)) (k + 1))))).sum
      = (Real.log (x + (n : ℝ)) - 1 / (2 * (x + (n : ℝ)))
        + (Finset.range K).sum (fun k => digCorrR (x + (n : ℝ)) (k + 1))) := by
    simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    rw [dig_list_sum_map_range]
    ring
  rw [hsumEq] at hsumM
  simp only [digammaPosIval, digStirlingIval]
  split
  · rename_i h hiH
    have h2Tle : 2 * digTailScale (x + (n : ℝ)) K ≤ h.toReal := by
      have h2 := htailM
      rw [Ival.mem_def, hiH] at h2
      simp only [Ival.leHi_some] at h2
      exact h2.2
    rw [Dy.toReal_def] at h2Tle
    have habs := abs_le.mp hmaster
    simp only [digStirling] at habs
    have heq : rdig x
        = ((digStirling (x + (n : ℝ)) K
          + (rdig (x + (n : ℝ)) - digStirling (x + (n : ℝ)) K))
          - (Finset.range n).sum (fun k => 1 / (x + ((k : Nat) : ℝ)))) := by
      have hsh := dig_shift x hx n
      rw [digShiftSum_eq] at hsh
      rw [hsh]
      ring
    have hRmem : rdig (x + (n : ℝ))
        - (Real.log (x + (n : ℝ)) - 1 / (2 * (x + (n : ℝ)))
          + (Finset.range K).sum (fun k => digCorrR (x + (n : ℝ)) (k + 1)))
        ∈ Ival.ofRats c.prec (-h.toRat) h.toRat := by
      refine Ival.mem_ofRats ?_ ?_ <;>
        (push_cast at habs h2Tle ⊢; linarith [habs.1, habs.2, h2Tle])
    rw [heq]
    simp only [digStirling]
    exact Ival.mem_sub (Ival.mem_add hsumM hRmem) hdir
  · exact Ival.mem_top _

theorem digammaRefl_sound (c : Ctx) (hc : c.Valid) (x : ℝ) (X : Ival)
    (L : List ℚ) (hxMem : x ∈ X) (hx : x < 0)
    (hN : ∀ m : ℕ, x ≠ -(m : ℝ)) (n K : Nat)
    (hL : ∀ i : Nat, i ≤ 2 * (K + 1) → (L.getD i 0 : ℚ) = bernoulli i)
    (hK : 1 ≤ K) (hY : 4 * (K : ℝ) + 4 ≤ (1 - x) + (n : ℝ)) :
    rdig x ∈ digammaReflIval c X L n K := by
  have h1R : (1 : ℝ) ∈ Ival.ofRat c.prec 1 := by
    exact_mod_cast Ival.mem_ofRat c.prec (1 : ℚ)
  have h1x : 1 - x ∈ Ival.sub c.prec (Ival.ofRat c.prec 1) X :=
    Ival.mem_sub h1R hxMem
  have hx' : 0 < 1 - x := by linarith
  have hpos := digammaPos_sound c hc (1 - x)
    (Ival.sub c.prec (Ival.ofRat c.prec 1) X) L h1x hx' n K hL hK hY
  have hpi : Real.pi ∈ c.pi := hc.pi_mem
  have hpix : Real.pi * x ∈ Ival.mul c.prec c.pi X :=
    Ival.mem_mul hpi hxMem
  have hcos : Real.cos (Real.pi * x) ∈ cosIval c (Ival.mul c.prec c.pi X) :=
    mem_cosIval hc hpix
  have hsin : Real.sin (Real.pi * x) ∈ sinIval c (Ival.mul c.prec c.pi X) :=
    mem_sinIval hc hpix
  have hcot : Real.cos (Real.pi * x) / Real.sin (Real.pi * x) ∈ Ival.div c.prec
      (cosIval c (Ival.mul c.prec c.pi X)) (sinIval c (Ival.mul c.prec c.pi X)) :=
    Ival.mem_div hcos hsin
  have hpicot : Real.pi * (Real.cos (Real.pi * x) / Real.sin (Real.pi * x)) ∈
      Ival.mul c.prec c.pi (Ival.div c.prec
        (cosIval c (Ival.mul c.prec c.pi X))
        (sinIval c (Ival.mul c.prec c.pi X))) :=
    Ival.mem_mul hpi hcot
  have hre := dig_refl x hx hN
  simp only [digammaReflIval]
  rw [hre]
  exact Ival.mem_sub hpos hpicot

theorem digammaIval_sound (c : Ctx) (hc : c.Valid) (x : ℝ) (X : Ival)
    (hx : x ∈ X) : rdig x ∈ digammaIval c X := by
  obtain ⟨hxlo, hxhi⟩ := hx
  cases hlo : X.lo with
  | none =>
    cases hhi : X.hi with
    | none => simp only [digammaIval, hlo, hhi]; exact Ival.mem_top _
    | some hi => simp only [digammaIval, hlo, hhi]; exact Ival.mem_top _
  | some lo =>
    cases hhi : X.hi with
    | none => simp only [digammaIval, hlo, hhi]; exact Ival.mem_top _
    | some hi =>
      have hloR : lo.toReal ≤ x := hxlo lo hlo
      have hhiR : x ≤ hi.toReal := hxhi hi hhi
      rw [Dy.toReal_def] at hloR hhiR
      have hxM : x ∈ X := Ival.mem_def.mpr ⟨hxlo, hxhi⟩
      simp only [digammaIval, hlo, hhi]
      split
      · rename_i hpole
        exact Ival.mem_top _
      · rename_i hpole
        have hpoleF : digHasPole lo hi = false := Bool.eq_false_iff.mpr hpole
        have hN : ∀ m : Nat, x ≠ -(m : ℝ) := fun m =>
          digHasPole_false hpoleF x hloR hhiR m
        split
        · rename_i hpos
          show rdig x ∈ digammaPosIval c X
            (bernoulliList (2 * ((4 + c.prec / 8) + 1)))
            (digShiftNumQ (20 + c.prec / 2) lo.toRat) (4 + c.prec / 8)
          have hx0 : 0 < x := by
            have hlor : (0 : ℝ) < (lo.toRat : ℝ) := by
              exact_mod_cast hpos
            linarith
          have hL : ∀ i : Nat, i ≤ 2 * ((4 + c.prec / 8) + 1) →
              ((bernoulliList (2 * ((4 + c.prec / 8) + 1))).getD i 0 : ℚ)
                = bernoulli i := fun i hi => bernoulliList_getD _ _ hi
          have hK : 1 ≤ 4 + c.prec / 8 := by omega
          have hXK : 4 * ((4 + c.prec / 8 : Nat) : ℝ) + 4
              ≤ ((20 + c.prec / 2 : Nat) : ℝ) := by
            have hnat : 4 * (4 + c.prec / 8) + 4 ≤ 20 + c.prec / 2 := by omega
            exact_mod_cast hnat
          have hY : 4 * ((4 + c.prec / 8 : Nat) : ℝ) + 4
              ≤ x + ((digShiftNumQ (20 + c.prec / 2) lo.toRat : Nat) : ℝ) := by
            have hn := digShiftNumQ_ge (20 + c.prec / 2) lo.toRat
            push_cast at hn hXK ⊢
            linarith [hloR, hn, hXK]
          exact digammaPos_sound c hc x X _ hxM hx0 _ _ hL hK hY
        · rename_i hnpos
          split
          · rename_i hneg
            show rdig x ∈ digammaReflIval c X
              (bernoulliList (2 * ((4 + c.prec / 8) + 1)))
              (digShiftNumQ (20 + c.prec / 2) (1 - hi.toRat)) (4 + c.prec / 8)
            have hxneg : x < 0 := by
              have hhir : (hi.toRat : ℝ) < 0 := by exact_mod_cast hneg
              linarith
            have hL : ∀ i : Nat, i ≤ 2 * ((4 + c.prec / 8) + 1) →
                ((bernoulliList (2 * ((4 + c.prec / 8) + 1))).getD i 0 : ℚ)
                  = bernoulli i := fun i hi => bernoulliList_getD _ _ hi
            have hK : 1 ≤ 4 + c.prec / 8 := by omega
            have hXK : 4 * ((4 + c.prec / 8 : Nat) : ℝ) + 4
                ≤ ((20 + c.prec / 2 : Nat) : ℝ) := by
              have hnat : 4 * (4 + c.prec / 8) + 4 ≤ 20 + c.prec / 2 := by omega
              exact_mod_cast hnat
            have hY : 4 * ((4 + c.prec / 8 : Nat) : ℝ) + 4
                ≤ (1 - x)
                  + ((digShiftNumQ (20 + c.prec / 2) (1 - hi.toRat) : Nat) : ℝ) := by
              have hn := digShiftNumQ_ge (20 + c.prec / 2) (1 - hi.toRat)
              have hcast : ((1 - hi.toRat : ℚ) : ℝ)
                  = 1 - (hi.toRat : ℝ) := by push_cast; ring
              push_cast at hn hXK hcast ⊢
              linarith [hhiR, hn, hcast, hXK]
            exact digammaRefl_sound c hc x X _ hxM hxneg hN _ _ hL hK hY
          · rename_i hneg2
            exact Ival.mem_top _

@[lynth_cfn] def digammaR : Fn1 .real .real where
  name := "digamma"
  graph x y := y = rdig x
  exu := exu_eq _
  ev c X := digammaIval c X
  sound := fun c x _ X hc hy hx => by
    obtain rfl := hy
    exact digammaIval_sound c hc x X hx
  cost := 800

end Lynth.Interval.Fns
