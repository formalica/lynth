module

import Mathlib

/-! Ported from `/tmp/zeta/zeta_em_thm.lean` (external prover, complete).
`Euler-Maclaurin` theory for real zeta. -/

namespace Lynth.Interval.Fns

/-!
# Euler–Maclaurin for real zeta (FLINT's general path) — PROVED by external prover (one commented-out obsolete statement remains)

This file is self-contained modulo Mathlib (no Lynth dependency).
It contains the exact statements needed to compute `ζ(s)` for real
`0 < s ≠ 1` the way FLINT does (`src/acb_poly/zeta_em_sum.c`,
specialized to shift `a = 1`, one real output): direct power sum plus
the integral term, the half term, and `M` Bernoulli corrections, with an
explicit remainder bound.

## The formula

For real `s` with `0 < s`, `s ≠ 1`, and `N ≥ 1`, `M ≥ 1`:

```
ζ(s) = D + I + H + C + R,    |R| ≤ 2·|T_{M+1}|
D   = Σ_{k=1}^{N} k^{-s}                          (direct sum)
I   = (N+1)^{1-s}/(s-1)                           (integral term)
H   = (N+1)^{-s}/2                                (half term)
C   = Σ_{r=1}^{M} B_{2r}/(2r)! · rising(s,2r-1)/(N+1)^{s+2r-1}
T_{M+1} = B_{2M+2}/(2M+2)! · rising(s,2M+1)/(N+1)^{s+2M+1}
rising(s,k) = ∏_{j<k} (s+j)
```

(all powers are `Real.rpow`; `B` is Mathlib `bernoulli`).  The side
condition `(N+1) ≥ s + 2M + 2` below keeps the tail geometrically
decreasing so that twice the first omitted term dominates.  This mirrors
FLINT's `_acb_poly_zeta_em_tail_naive` (Bernoulli sum with the
`(s+2r-1)(s+2r)` recurrence) and `_acb_poly_zeta_em_bound`
(`K/C/I`-style remainder estimate); see also Cohen, *Computational
Algebraic Number Theory*, § on zeta via Euler–Maclaurin.

Note on Bernoulli numbers: Lynth evaluates `B_{2r}` as exact rationals
via its `bernoulliQ` (structural recurrence), proved equal to Mathlib
`bernoulli` (`bernoulliList_getD` in `Lynth/Interval/Fns/Gamma.lean`);
the prover here works directly with Mathlib `bernoulli`.

## Task

Replace each `sorrry` below with a real proof. Statements must stay
byte-identical (they will be mirrored into Lynth as axioms first, then
as theorems). Difficulty labels: the MAIN bound is the hard one; the
rest is scaffolding of increasing easiness.

## Acceptance criteria

* Toolchain `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0`.
* No `sorrry`, no new `axiom` (any Mathlib lemmas may be used).
* Constants (`2`, side condition) follow the sketch above; the prover may
  adjust them with justification if the proof needs it.
-/

/-!
## Auxiliary material for the proof of `zeta_em_bound` (Euler–Maclaurin for `ζ(s)`)

Per-interval Euler–Maclaurin remainders for `x ↦ x^{-s}` (complex `s`),
their integral representation through Bernoulli polynomials, analytic
continuation to `0 < re s`, and the real remainder bound.
-/

open Filter Topology

namespace ZetaEM

/-- complex rising factorial `∏_{j<k} (s+j)`. -/
noncomputable def cRising (s : ℂ) (k : ℕ) : ℂ := ∏ j ∈ Finset.range k, (s + j)

/-- `j`-th derivative of `x ↦ x^{-s}`: `(-1)^j (s)_j x^{-s-j}`. -/
noncomputable def dF (s : ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  (-1) ^ j * cRising s j * (x : ℂ) ^ (-s - j)

/-- normalized Bernoulli polynomial `B_k(t)/k!` (complex valued). -/
noncomputable def bφ (k : ℕ) (t : ℝ) : ℂ := ((bernoulliFun k t / (k.factorial : ℝ) : ℝ) : ℂ)

lemma cRising_succ (s : ℂ) (k : ℕ) : cRising s (k + 1) = cRising s k * (s + k) := by
  simp [cRising, Finset.prod_range_succ]

lemma hasDerivAt_dF (s : ℂ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (dF s j) (dF s (j + 1) x) x := by
  unfold dF
  by_cases hr : -s - (j : ℂ) = 0
  · have hsj : s + j = 0 := by linear_combination -hr
    rw [cRising_succ, hsj]
    simp only [hr, Complex.cpow_zero, mul_zero, zero_mul]
    exact hasDerivAt_const x _
  · have h := (hasDerivAt_ofReal_cpow_const hx.ne' hr).const_mul ((-1) ^ j * cRising s j)
    convert h using 1
    rw [cRising_succ]
    push_cast
    ring_nf

lemma hasDerivAt_bφ (k : ℕ) (t : ℝ) : HasDerivAt (bφ (k + 1)) (bφ k t) t := by
  unfold bφ
  have h := ((hasDerivAt_bernoulliFun (k + 1) t).div_const ((k + 1).factorial : ℝ)).ofReal_comp
  refine h.congr_deriv ?_
  simp only [Nat.add_sub_cancel, Nat.factorial_succ]
  congr 1
  push_cast
  have : ((k.factorial : ℝ)) ≠ 0 := by positivity
  have : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp

lemma bφ_one_of_ne_one {k : ℕ} (hk : k ≠ 1) : bφ k 1 = bφ k 0 := by
  simp [bφ, bernoulliFun_endpoints_eq_of_ne_one hk]

lemma bφ_zero_eq (k : ℕ) : bφ k 0 = (bernoulli k / (k.factorial : ℚ) : ℚ) := by
  simp [bφ, bernoulliFun_eval_zero]

lemma bφ_odd_zero {r : ℕ} (hr : 1 ≤ r) : bφ (2 * r + 1) 0 = 0 := by
  rw [bφ_zero_eq, bernoulli_eq_zero_of_odd (by exact odd_two_mul_add_one r) (by omega)]
  simp

lemma bφ_one_fun (t : ℝ) : bφ 1 t = (t : ℂ) - 1 / 2 := by
  simp [bφ]

lemma bφ_zero_fun (t : ℝ) : bφ 0 t = 1 := by
  simp [bφ]

lemma continuous_bφ (k : ℕ) : Continuous (bφ k) := by
  unfold bφ
  fun_prop

lemma continuousOn_dF (s : ℂ) (j : ℕ) {m : ℝ} (hm : 0 < m) :
    ContinuousOn (fun t : ℝ => dF s j (m + t)) (Set.uIcc 0 1) := by
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  have : 0 < m + t := by linarith [ht.1]
  exact ((hasDerivAt_dF s j this).continuousAt.comp
    (continuous_const.add continuous_id).continuousAt).continuousWithinAt

/-- one integration by parts step. -/
lemma ibp_step (s : ℂ) (k : ℕ) {m : ℝ} (hm : 0 < m) :
    ∫ t in (0 : ℝ)..1, bφ k t * dF s k (m + t)
      = bφ (k + 1) 1 * dF s k (m + 1) - bφ (k + 1) 0 * dF s k m
        - ∫ t in (0 : ℝ)..1, bφ (k + 1) t * dF s (k + 1) (m + t) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t => dF s k (m + t)) (dF s (k + 1) (m + t)) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have : 0 < m + t := by linarith [ht.1]
    exact HasDerivAt.comp_const_add m t (hasDerivAt_dF s k this)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ => hasDerivAt_bφ k t) hderiv
    ((continuous_bφ k).intervalIntegrable 0 1)
    ((continuousOn_dF s (k + 1) hm).intervalIntegrable)
  simp only [add_zero] at h
  rw [h]
  ring

/-- the base integral `∫_0^1 (m+t)^{-s} dt`. -/
lemma integral_dF_zero {s : ℂ} (hs : s ≠ 1) {m : ℝ} (hm : 0 < m) :
    ∫ t in (0 : ℝ)..1, dF s 0 (m + t)
      = ((((m + 1 : ℝ)) : ℂ) ^ (1 - s) - (m : ℂ) ^ (1 - s)) / (1 - s) := by
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => (((m + t : ℝ)) : ℂ) ^ (1 - s) / (1 - s)) (dF s 0 (m + t)) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hpos : 0 < m + t := by linarith [ht.1]
    have h := (HasDerivAt.comp_const_add m t
      (hasDerivAt_ofReal_cpow_const hpos.ne' h1s)).div_const (1 - s)
    convert h using 1
    · unfold dF
      simp only [pow_zero, cRising, Finset.range_zero, Finset.prod_empty, one_mul,
        Nat.cast_zero, sub_zero, mul_one]
      field_simp
      ring_nf
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuousOn_dF s 0 hm).intervalIntegrable)]
  simp only [add_zero]
  ring

/-- closed form of the per-interval Euler–Maclaurin remainder on `[m, m+1]`
with `K` Bernoulli corrections. -/
noncomputable def emR (K : ℕ) (s : ℂ) (m : ℝ) : ℂ :=
  ((((m + 1 : ℝ)) : ℂ) ^ (1 - s) - (m : ℂ) ^ (1 - s)) / (1 - s)
    - (dF s 0 m + dF s 0 (m + 1)) / 2
    + ∑ r ∈ Finset.range K, bφ (2 * r + 2) 0 * (dF s (2 * r + 1) (m + 1) - dF s (2 * r + 1) m)

/-- the integrals `J k = ∫_0^1 B_k(t)/k! · f^{(k)}(m+t) dt`. -/
noncomputable def emJ (s : ℂ) (m : ℝ) (k : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..1, bφ k t * dF s k (m + t)

lemma emJ_two {s : ℂ} (hs : s ≠ 1) {m : ℝ} (hm : 0 < m) : emR 1 s m = emJ s m 2 := by
  have h0 := ibp_step s 0 hm
  have h1 := ibp_step s 1 hm
  have hJ0 : emJ s m 0 = ((((m + 1 : ℝ)) : ℂ) ^ (1 - s) - (m : ℂ) ^ (1 - s)) / (1 - s) := by
    rw [← integral_dF_zero hs hm]
    simp [emJ, bφ_zero_fun]
  change emJ s m 0 = _ - _ - emJ s m 1 at h0
  change emJ s m 1 = _ - _ - emJ s m 2 at h1
  rw [bφ_one_fun, bφ_one_fun] at h0
  rw [bφ_one_of_ne_one (by norm_num)] at h1
  simp only [emR, Finset.range_one, Finset.sum_singleton, mul_zero, zero_add]
  rw [← hJ0]
  push_cast at h0
  linear_combination h0 - h1

lemma emJ_step {s : ℂ} {m : ℝ} (hm : 0 < m) {K : ℕ} (hK : 1 ≤ K) :
    emJ s m (2 * K + 2)
      = emJ s m (2 * K) + bφ (2 * K + 2) 0 * (dF s (2 * K + 1) (m + 1) - dF s (2 * K + 1) m) := by
  have h0 := ibp_step s (2 * K) hm
  have h1 := ibp_step s (2 * K + 1) hm
  change emJ s m (2 * K) = _ - _ - emJ s m (2 * K + 1) at h0
  change emJ s m (2 * K + 1) = _ - _ - emJ s m (2 * K + 1 + 1) at h1
  rw [bφ_one_of_ne_one (by omega), bφ_odd_zero hK] at h0
  rw [bφ_one_of_ne_one (by omega)] at h1
  linear_combination h1 - h0

/-- integral representation of the per-interval remainder. -/
lemma emR_eq_integral {K : ℕ} (hK : 1 ≤ K) {s : ℂ} (hs : s ≠ 1) {m : ℝ} (hm : 0 < m) :
    emR K s m = ∫ t in (0 : ℝ)..1, bφ (2 * K) t * dF s (2 * K) (m + t) := by
  change emR K s m = emJ s m (2 * K)
  induction K, hK using Nat.le_induction with
  | base => exact emJ_two hs hm
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

lemma norm_bφ_le {K : ℕ} (hK : 1 ≤ K) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖bφ (2 * K) t‖ ≤ |(bernoulli (2 * K) : ℝ)| / ((2 * K).factorial : ℝ) := by
  unfold bφ
  have hf : (0 : ℝ) < ((2 * K).factorial : ℝ) := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hf]
  exact div_le_div_of_nonneg_right (abs_bernoulliFun_le (k := K) (by omega) ht) hf.le

lemma norm_dF (s : ℂ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖dF s j x‖ = ‖cRising s j‖ * x ^ (-s.re - j) := by
  unfold dF
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- integral bound of the per-interval remainder. -/
lemma norm_emR_le_integral {K : ℕ} (hK : 1 ≤ K) {s : ℂ} (hs : s ≠ 1) {m : ℝ} (hm : 0 < m) :
    ‖emR K s m‖ ≤ |(bernoulli (2 * K) : ℝ)| / ((2 * K).factorial : ℝ)
      * ∫ t in (0 : ℝ)..1, ‖dF s (2 * K) (m + t)‖ := by
  rw [emR_eq_integral hK hs hm]
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact ((continuous_bφ _).continuousOn.mul (continuousOn_dF s _ hm)).norm.intervalIntegrable
  · exact (continuousOn_const.mul (continuousOn_dF s _ hm).norm).intervalIntegrable
  · intro t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_bφ_le hK ht) (norm_nonneg _)

/-- uniform bound of the per-interval remainder (for `0 ≤ re s`, `1 ≤ m`). -/
lemma norm_emR_le {K : ℕ} (hK : 1 ≤ K) {s : ℂ} (hs : s ≠ 1) (hre : 0 ≤ s.re) {m : ℝ}
    (hm : 1 ≤ m) :
    ‖emR K s m‖ ≤ |(bernoulli (2 * K) : ℝ)| / ((2 * K).factorial : ℝ)
      * ‖cRising s (2 * K)‖ * (1 / m ^ (2 * K)) := by
  have hm0 : 0 < m := by linarith
  refine (norm_emR_le_integral hK hs hm0).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have : ∫ t in (0 : ℝ)..1, ‖dF s (2 * K) (m + t)‖
      ≤ ∫ t in (0 : ℝ)..1, ‖cRising s (2 * K)‖ * (1 / m ^ (2 * K)) := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (continuousOn_dF s _ hm0).norm.intervalIntegrable
    · exact intervalIntegrable_const
    · intro t ht
      have hmt : 0 < m + t := by linarith [ht.1]
      rw [norm_dF s _ hmt]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have h1 : (m + t) ^ (-s.re - ((2 * K : ℕ) : ℝ)) ≤ m ^ (-s.re - ((2 * K : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hm0 (by linarith [ht.1]) (by
          have : (0 : ℝ) ≤ ((2 * K : ℕ) : ℝ) := by positivity
          linarith)
      refine h1.trans ?_
      have h2 : m ^ (-s.re - ((2 * K : ℕ) : ℝ)) ≤ m ^ (-((2 * K : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hm (by linarith)
      refine h2.trans (le_of_eq ?_)
      rw [Real.rpow_neg hm0.le, Real.rpow_natCast, one_div]
  refine this.trans (le_of_eq ?_)
  simp

/-- antiderivative `y^{1-s}/(1-s)` of `y^{-s}`. -/
noncomputable def emG (s : ℂ) (y : ℝ) : ℂ := (y : ℂ) ^ (1 - s) / (1 - s)

/-- finite telescoped Euler–Maclaurin identity on `[a, a+L]`. -/
lemma partial_sum_emR (K a : ℕ) (s : ℂ) (L : ℕ) :
    ∑ i ∈ Finset.range L, emR K s ((a + i : ℕ) : ℝ)
      = emG s ((a + L : ℕ) : ℝ) - emG s ((a + 0 : ℕ) : ℝ)
        - ∑ i ∈ Finset.range L, dF s 0 ((a + i : ℕ) : ℝ)
        - (dF s 0 ((a + L : ℕ) : ℝ) - dF s 0 ((a + 0 : ℕ) : ℝ)) / 2
        + ∑ r ∈ Finset.range K, bφ (2 * r + 2) 0 *
            (dF s (2 * r + 1) ((a + L : ℕ) : ℝ) - dF s (2 * r + 1) ((a + 0 : ℕ) : ℝ)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have hc : (((a + L : ℕ) : ℝ) + 1) = ((a + (L + 1) : ℕ) : ℝ) := by push_cast; ring
    simp only [emR, hc, emG]
    have hsum : ∑ r ∈ Finset.range K, bφ (2 * r + 2) 0 *
          (dF s (2 * r + 1) ((a + (L + 1) : ℕ) : ℝ) - dF s (2 * r + 1) ((a + 0 : ℕ) : ℝ))
        = ∑ r ∈ Finset.range K, bφ (2 * r + 2) 0 *
          (dF s (2 * r + 1) ((a + L : ℕ) : ℝ) - dF s (2 * r + 1) ((a + 0 : ℕ) : ℝ))
          + ∑ r ∈ Finset.range K, bφ (2 * r + 2) 0 *
          (dF s (2 * r + 1) ((a + (L + 1) : ℕ) : ℝ) - dF s (2 * r + 1) ((a + L : ℕ) : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun r _ => by ring)
    rw [hsum]
    ring

lemma tendsto_natCast_add_atTop (a : ℕ) :
    Tendsto (fun L : ℕ => ((a + L : ℕ) : ℝ)) atTop atTop := by
  refine tendsto_natCast_atTop_atTop.comp ?_
  exact tendsto_atTop_mono (fun L => Nat.le_add_left L a) tendsto_id

/-- `‖y^c‖ → 0` along `y = a + L` when `re c < 0`. -/
lemma tendsto_cpow_zero {c : ℂ} (hc : c.re < 0) (a : ℕ) :
    Tendsto (fun L : ℕ => (((a + L : ℕ) : ℝ) : ℂ) ^ c) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun y : ℝ => y ^ c.re) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := -c.re) (by linarith)
    simpa using this
  have h2 := h1.comp (tendsto_natCast_add_atTop a)
  refine (tendsto_congr' ?_).mp h2
  filter_upwards [eventually_ge_atTop 1] with L hL
  simp only [Function.comp]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (show 0 < a + L by omega))]

lemma dF_zero_eq (s : ℂ) (y : ℝ) : dF s 0 y = 1 / (y : ℂ) ^ s := by
  simp [dF, cRising, Complex.cpow_neg]

lemma tendsto_dF_zero {s : ℂ} (j : ℕ) (hs : 0 < s.re + j) (a : ℕ) :
    Tendsto (fun L : ℕ => dF s j ((a + L : ℕ) : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_cpow_zero (c := -s - j) (by simp; linarith) a).const_mul
    ((-1) ^ j * cRising s j)
  rw [mul_zero] at h
  exact h

lemma tendsto_emG_zero {s : ℂ} (hs : 1 < s.re) (a : ℕ) :
    Tendsto (fun L : ℕ => emG s ((a + L : ℕ) : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_cpow_zero (c := 1 - s) (by simp; linarith) a).div_const (1 - s)
  rw [zero_div] at h
  exact h

lemma summable_emR {K : ℕ} (hK : 1 ≤ K) {s : ℂ} (hs : s ≠ 1) (hre : 0 ≤ s.re) {a : ℕ}
    (ha : 1 ≤ a) : Summable (fun i : ℕ => emR K s ((a + i : ℕ) : ℝ)) := by
  refine Summable.of_norm_bounded (g := fun i : ℕ => |(bernoulli (2 * K) : ℝ)|
      / ((2 * K).factorial : ℝ) * ‖cRising s (2 * K)‖ * (1 / ((a + i : ℕ) : ℝ) ^ (2 * K))) ?_
    (fun i => norm_emR_le hK hs hre (by exact_mod_cast (show 1 ≤ a + i by omega)))
  refine Summable.mul_left _ ?_
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 * K)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have h2 := (summable_nat_add_iff a).mpr h
  refine h2.congr (fun i => ?_)
  push_cast
  ring_nf

lemma summable_dF_zero {s : ℂ} (hs : 1 < s.re) (a : ℕ) :
    Summable (fun i : ℕ => dF s 0 ((a + i : ℕ) : ℝ)) := by
  have h := (summable_nat_add_iff a).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
  refine h.congr (fun i => ?_)
  rw [dF_zero_eq]
  push_cast
  ring_nf

/-- Euler–Maclaurin for the tail `Σ_{i ≥ 0} (a+i)^{-s}` (for `re s > 1`). -/
lemma tsum_tail_eq {K : ℕ} (hK : 1 ≤ K) {s : ℂ} (hs : 1 < s.re) {a : ℕ} (ha : 1 ≤ a) :
    ∑' i : ℕ, dF s 0 ((a + i : ℕ) : ℝ)
      = -emG s ((a + 0 : ℕ) : ℝ) + dF s 0 ((a + 0 : ℕ) : ℝ) / 2
        - ∑ r ∈ Finset.range K, bφ (2 * r + 2) 0 * dF s (2 * r + 1) ((a + 0 : ℕ) : ℝ)
        - ∑' i : ℕ, emR K s ((a + i : ℕ) : ℝ) := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hre : 0 ≤ s.re := by linarith
  have hlim1 := (summable_dF_zero hs a).hasSum.tendsto_sum_nat
  have hlim2 := (summable_emR hK hs1 hre ha).hasSum.tendsto_sum_nat
  have hpart : ∀ L : ℕ, ∑ i ∈ Finset.range L, dF s 0 ((a + i : ℕ) : ℝ)
      = emG s ((a + L : ℕ) : ℝ) - emG s ((a + 0 : ℕ) : ℝ)
        - (dF s 0 ((a + L : ℕ) : ℝ) - dF s 0 ((a + 0 : ℕ) : ℝ)) / 2
        + ∑ r ∈ Finset.range K, bφ (2 * r + 2) 0 *
            (dF s (2 * r + 1) ((a + L : ℕ) : ℝ) - dF s (2 * r + 1) ((a + 0 : ℕ) : ℝ))
        - ∑ i ∈ Finset.range L, emR K s ((a + i : ℕ) : ℝ) := by
    intro L
    rw [partial_sum_emR]
    ring
  have hlim3 : Tendsto (fun L : ℕ => emG s ((a + L : ℕ) : ℝ) - emG s ((a + 0 : ℕ) : ℝ)
        - (dF s 0 ((a + L : ℕ) : ℝ) - dF s 0 ((a + 0 : ℕ) : ℝ)) / 2
        + ∑ r ∈ Finset.range K, bφ (2 * r + 2) 0 *
            (dF s (2 * r + 1) ((a + L : ℕ) : ℝ) - dF s (2 * r + 1) ((a + 0 : ℕ) : ℝ))
        - ∑ i ∈ Finset.range L, emR K s ((a + i : ℕ) : ℝ)) atTop
      (𝓝 (0 - emG s ((a + 0 : ℕ) : ℝ) - (0 - dF s 0 ((a + 0 : ℕ) : ℝ)) / 2
        + ∑ r ∈ Finset.range K, bφ (2 * r + 2) 0 * (0 - dF s (2 * r + 1) ((a + 0 : ℕ) : ℝ))
        - ∑' i : ℕ, emR K s ((a + i : ℕ) : ℝ))) := by
    refine ((((tendsto_emG_zero hs a).sub tendsto_const_nhds).sub
      (((tendsto_dF_zero 0 (by simp; linarith) a).sub tendsto_const_nhds).div_const 2)).add
      (tendsto_finsetSum _ (fun r _ => ((tendsto_dF_zero (2 * r + 1)
        (by push_cast; linarith) a).sub tendsto_const_nhds).const_mul _))).sub hlim2
  rw [funext hpart] at hlim1
  rw [tendsto_nhds_unique hlim1 hlim3]
  simp only [zero_sub, mul_neg, Finset.sum_neg_distrib]
  ring

/-- the Euler–Maclaurin right-hand side with `a = N + 1` and `K` corrections
(the remainder is the convergent series of per-interval remainders). -/
noncomputable def emPhi (N K : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range N, dF s 0 ((k + 1 : ℕ) : ℝ)
    - emG s ((N + 1 + 0 : ℕ) : ℝ) + dF s 0 ((N + 1 + 0 : ℕ) : ℝ) / 2
    - ∑ r ∈ Finset.range K, bφ (2 * r + 2) 0 * dF s (2 * r + 1) ((N + 1 + 0 : ℕ) : ℝ)
    - ∑' i : ℕ, emR K s ((N + 1 + i : ℕ) : ℝ)

lemma zeta_eq_emPhi_of_one_lt_re (N : ℕ) {K : ℕ} (hK : 1 ≤ K) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = emPhi N K s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have h := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
    simpa using h
  rw [← hsum.sum_add_tsum_nat_add N]
  have e1 : ∀ k : ℕ, 1 / ((k : ℂ) + 1) ^ s = dF s 0 ((k + 1 : ℕ) : ℝ) := by
    intro k; rw [dF_zero_eq]; push_cast; rfl
  have e2 : ∀ i : ℕ, 1 / (((i + N : ℕ) : ℂ) + 1) ^ s = dF s 0 ((N + 1 + i : ℕ) : ℝ) := by
    intro i; rw [dF_zero_eq]; push_cast; ring_nf
  rw [tsum_congr e2]
  simp only [e1]
  rw [tsum_tail_eq hK hs (by omega : 1 ≤ N + 1)]
  unfold emPhi
  ring

lemma differentiable_dF (j : ℕ) {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (fun s : ℂ => dF s j y) := by
  intro s
  unfold dF cRising
  have h1 : DifferentiableAt ℂ (fun s : ℂ => ∏ i ∈ Finset.range j, (s + (i : ℂ))) s := by
    fun_prop
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ (-s - (j : ℂ))) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hy.ne'))
  exact (h1.const_mul _).mul h2

lemma differentiableAt_emG {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (fun s : ℂ => emG s y) s := by
  unfold emG
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ (1 - s)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hy.ne'))
  exact h2.div (by fun_prop) (sub_ne_zero.mpr (Ne.symm hs))

lemma differentiableAt_emR (K : ℕ) {m : ℝ} (hm : 0 < m) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (fun s : ℂ => emR K s m) s := by
  unfold emR
  have hm1 : 0 < m + 1 := by linarith
  have hG : DifferentiableAt ℂ
      (fun s : ℂ => ((((m + 1 : ℝ)) : ℂ) ^ (1 - s) - (m : ℂ) ^ (1 - s)) / (1 - s)) s := by
    refine DifferentiableAt.div ?_ (by fun_prop) (sub_ne_zero.mpr (Ne.symm hs))
    exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hm1.ne'))).sub
      (DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hm.ne')))
  refine (hG.sub (((differentiable_dF 0 hm s).add (differentiable_dF 0 hm1 s)).div_const 2)).add ?_
  apply DifferentiableAt.fun_sum
  intro r _
  exact ((differentiable_dF _ hm1 s).sub (differentiable_dF _ hm s)).const_mul _

lemma norm_cRising_le (s : ℂ) (k : ℕ) : ‖cRising s k‖ ≤ (‖s‖ + k) ^ k := by
  induction k with
  | zero => simp [cRising]
  | succ k ih =>
    rw [cRising_succ, norm_mul, pow_succ]
    have h1 : ‖s + (k : ℂ)‖ ≤ ‖s‖ + ((k + 1 : ℕ) : ℝ) := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_natCast]
      push_cast
      linarith
    have h2 : (‖s‖ + k) ^ k ≤ (‖s‖ + ((k + 1 : ℕ) : ℝ)) ^ k :=
      pow_le_pow_left₀ (by positivity) (by push_cast; linarith) k
    exact mul_le_mul (ih.trans h2) h1 (norm_nonneg _) (by positivity)

/-- the right half-plane minus the pole. -/
def emDom : Set ℂ := {s : ℂ | 0 < s.re} ∩ {1}ᶜ

lemma isOpen_emDom : IsOpen emDom :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton

lemma isPreconnected_emDom : IsPreconnected emDom := by
  have hC1 : IsPreconnected ({s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}) :=
    (convex_halfSpace_re_gt 0 |>.inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hC2 : IsPreconnected ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im < 0}) :=
    (convex_halfSpace_re_gt 0 |>.inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hC3 : IsPreconnected ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1}) :=
    (convex_halfSpace_re_gt 0 |>.inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hC4 : IsPreconnected {s : ℂ | 1 < s.re} := (convex_halfSpace_re_gt 1).isPreconnected
  have h13 := IsPreconnected.union (⟨1 / 2, 1⟩ : ℂ) (by norm_num) (by norm_num) hC3 hC1
  have h132 := IsPreconnected.union (⟨1 / 2, -1⟩ : ℂ) (by norm_num) (by norm_num)
    h13 hC2
  have h1324 := IsPreconnected.union (⟨2, 1⟩ : ℂ) (by norm_num) (by norm_num)
    h132 hC4
  convert h1324 using 1
  ext s
  simp only [emDom, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff,
    Set.mem_singleton_iff, Set.mem_union]
  constructor
  · rintro ⟨h0, h1⟩
    rcases lt_trichotomy s.im 0 with hi | hi | hi
    · exact Or.inl (Or.inr ⟨h0, hi⟩)
    · rcases lt_trichotomy s.re 1 with hr | hr | hr
      · exact Or.inl (Or.inl (Or.inl ⟨h0, hr⟩))
      · exact absurd (Complex.ext (by simpa using hr) (by simpa using hi)) h1
      · exact Or.inr hr
    · exact Or.inl (Or.inl (Or.inr ⟨h0, hi⟩))
  · rintro (((⟨h0, h1⟩ | ⟨h0, h1⟩) | ⟨h0, h1⟩) | h)
    · exact ⟨h0, fun h => by rw [h] at h1; simp at h1⟩
    · exact ⟨h0, fun h => by rw [h] at h1; simp at h1⟩
    · exact ⟨h0, fun h => by rw [h] at h1; simp at h1⟩
    · exact ⟨by linarith, fun h' => by rw [h'] at h; simp at h⟩

lemma differentiableOn_emPhi (N : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    DifferentiableOn ℂ (emPhi N K) emDom := by
  intro s₀ hs₀
  apply DifferentiableAt.differentiableWithinAt
  have hs₀1 : s₀ ≠ 1 := hs₀.2
  set V : Set ℂ := emDom ∩ Metric.ball 0 (‖s₀‖ + 1) with hV
  have hVo : IsOpen V := isOpen_emDom.inter Metric.isOpen_ball
  have hs₀V : s₀ ∈ V := ⟨hs₀, by simp⟩
  have htsum : DifferentiableOn ℂ (fun s => ∑' i : ℕ, emR K s ((N + 1 + i : ℕ) : ℝ)) V := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun i : ℕ => |(bernoulli (2 * K) : ℝ)| / ((2 * K).factorial : ℝ)
        * (‖s₀‖ + 1 + (2 * K : ℕ)) ^ (2 * K) * (1 / ((N + 1 + i : ℕ) : ℝ) ^ (2 * K))) ?_ ?_ hVo ?_
    · refine Summable.mul_left _ ?_
      have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 * K)) :=
        Real.summable_one_div_nat_pow.mpr (by omega)
      have h2 := (summable_nat_add_iff (N + 1)).mpr h
      refine h2.congr (fun i => ?_)
      push_cast
      ring_nf
    · intro i s hs
      exact (differentiableAt_emR K (by positivity) hs.1.2).differentiableWithinAt
    · intro i s hs
      refine (norm_emR_le hK hs.1.2 hs.1.1.le
        (by exact_mod_cast (show 1 ≤ N + 1 + i by omega))).trans ?_
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine (norm_cRising_le s (2 * K)).trans ?_
      have hs' : ‖s‖ < ‖s₀‖ + 1 := by simpa using hs.2
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have htsumAt := htsum.differentiableAt (hVo.mem_nhds hs₀V)
  unfold emPhi
  refine ((((?_ : DifferentiableAt ℂ _ s₀).sub (differentiableAt_emG (by positivity) hs₀1)).add
    ((differentiable_dF 0 (by positivity) s₀).div_const 2)).sub ?_).sub htsumAt
  · apply DifferentiableAt.fun_sum
    intro k _
    exact differentiable_dF 0 (by positivity) s₀
  · apply DifferentiableAt.fun_sum
    intro r _
    exact (differentiable_dF _ (by positivity) s₀).const_mul _

/-- analytic continuation: the Euler–Maclaurin identity holds on `0 < re s, s ≠ 1`. -/
lemma zeta_eq_emPhi (N : ℕ) {K : ℕ} (hK : 1 ≤ K) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = emPhi N K s := by
  have hzeta : DifferentiableOn ℂ riemannZeta emDom :=
    fun z hz => (differentiableAt_riemannZeta hz.2).differentiableWithinAt
  have h2 : (2 : ℂ) ∈ emDom := ⟨by simp, by norm_num⟩
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hzeta.analyticOnNhd isOpen_emDom) ((differentiableOn_emPhi N hK).analyticOnNhd isOpen_emDom)
    isPreconnected_emDom h2 ?_ ⟨hs, hs1⟩
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds (by simp : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
  exact zeta_eq_emPhi_of_one_lt_re N hK hz

lemma integral_norm_dF_real {K : ℕ} (hK : 1 ≤ K) {s : ℝ} (hs : 0 < s) {m : ℝ} (hm : 0 < m) :
    ∫ t in (0 : ℝ)..1, ‖dF (s : ℂ) (2 * K) (m + t)‖
      = ‖cRising (s : ℂ) (2 * K)‖ *
        ((m ^ (1 - s - 2 * (K : ℝ)) - (m + 1) ^ (1 - s - 2 * (K : ℝ))) / (s + 2 * (K : ℝ) - 1)) := by
  have hcongr : ∀ t ∈ Set.uIcc (0 : ℝ) 1, ‖dF (s : ℂ) (2 * K) (m + t)‖
      = ‖cRising (s : ℂ) (2 * K)‖ * (m + t) ^ (-s - 2 * (K : ℝ)) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    rw [norm_dF _ _ (by linarith [ht.1])]
    simp
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_left (fun x => x ^ (-s - 2 * (K : ℝ))) m]
  congr 1
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hne : -s - 2 * (K : ℝ) ≠ -1 := by
    intro h
    linarith
  rw [integral_rpow (Or.inr ⟨hne, by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]⟩)]
  have h1 : -s - 2 * (K : ℝ) + 1 = 1 - s - 2 * (K : ℝ) := by ring
  rw [h1, add_zero, show (1 - s - 2 * (K : ℝ)) = -(s + 2 * (K : ℝ) - 1) by ring, div_neg,
    ← neg_div, neg_sub]

/-- real remainder bound: for real `s > 0`, the total remainder is at most
`|B_{2K}|/(2K)! · |(s)_{2K}| · (N+1)^{1-s-2K}/(s+2K-1)`. -/
lemma norm_tsum_emR_le_real (N : ℕ) {K : ℕ} (hK : 1 ≤ K) {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) :
    ‖∑' i : ℕ, emR K (s : ℂ) ((N + 1 + i : ℕ) : ℝ)‖
      ≤ |(bernoulli (2 * K) : ℝ)| / ((2 * K).factorial : ℝ) * ‖cRising (s : ℂ) (2 * K)‖
        * ((((N + 1 + 0 : ℕ) : ℝ)) ^ (1 - s - 2 * (K : ℝ)) / (s + 2 * (K : ℝ) - 1)) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hs1' : (s : ℂ) ≠ 1 := by exact_mod_cast hs1
  set C : ℝ := |(bernoulli (2 * K) : ℝ)| / ((2 * K).factorial : ℝ) * ‖cRising (s : ℂ) (2 * K)‖
  set hh : ℕ → ℝ := fun i => (((N + 1 + i : ℕ) : ℝ)) ^ (1 - s - 2 * (K : ℝ)) / (s + 2 * (K : ℝ) - 1)
  set g : ℕ → ℝ := fun i => C * (hh i - hh (i + 1))
  have hbound : ∀ i : ℕ, ‖emR K (s : ℂ) ((N + 1 + i : ℕ) : ℝ)‖ ≤ g i := by
    intro i
    have hpos : (0 : ℝ) < ((N + 1 + i : ℕ) : ℝ) := by positivity
    refine (norm_emR_le_integral hK hs1' hpos).trans (le_of_eq ?_)
    rw [integral_norm_dF_real hK hs hpos]
    simp only [g, hh, C]
    push_cast
    ring_nf
  have hpart : ∀ L : ℕ, ∑ i ∈ Finset.range L, g i = C * (hh 0 - hh L) := by
    intro L
    simp only [g]
    rw [← Finset.mul_sum, Finset.sum_range_sub']
  have hlim : Tendsto (fun L : ℕ => hh L) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => y ^ (1 - s - 2 * (K : ℝ))) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := s + 2 * (K : ℝ) - 1) (by linarith)
      simpa [neg_sub, sub_sub] using this
    have h2 := (h1.comp (tendsto_natCast_add_atTop (N + 1))).div_const (s + 2 * (K : ℝ) - 1)
    rw [zero_div] at h2
    exact h2
  have hg0 : ∀ i, 0 ≤ g i := fun i => (norm_nonneg _).trans (hbound i)
  have hgsum : HasSum g (C * hh 0) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hg0]
    simp only [hpart]
    have := (tendsto_const_nhds (x := hh 0)).sub hlim
    rw [sub_zero] at this
    exact this.const_mul C
  have hnorm_sum : Summable (fun i : ℕ => ‖emR K (s : ℂ) ((N + 1 + i : ℕ) : ℝ)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound hgsum.summable
  refine (norm_tsum_le_tsum_norm hnorm_sum).trans ?_
  refine (hnorm_sum.tsum_le_tsum hbound hgsum.summable).trans (le_of_eq ?_)
  rw [hgsum.tsum_eq]

end ZetaEM

open Real BigOperators Topology Filter Finset Nat

/-- rising factorial `∏_{j<k} (s+j)` (mirrors Lynth's `risingReal`). -/
noncomputable def emRising (s : ℝ) (k : ℕ) : ℝ :=
  (Finset.range k).prod fun j => s + (j : ℝ)

/-- direct power sum `Σ_{k=1}^{N} k^{-s}`. -/
noncomputable def emDirect (s : ℝ) (N : Nat) : ℝ :=
  (Finset.range N).sum fun k => ((k + 1 : ℕ) : ℝ) ^ (-s)

/-- one Bernoulli correction (may be negative; `B_{2r}` alternates). -/
noncomputable def emCorr (s : ℝ) (N r : Nat) : ℝ :=
  (bernoulli (2 * r) : ℝ) / (Nat.factorial (2 * r) : ℝ)
    * emRising s (2 * r - 1) / ((N + 1 : ℕ) : ℝ) ^ (s + (2 * (r : ℝ)) - 1)

/-- first omitted correction (remainder scale). -/
noncomputable def emTailScale (s : ℝ) (N M : Nat) : ℝ :=
  |(bernoulli (2 * (M + 1)) : ℝ)| / (Nat.factorial (2 * (M + 1)) : ℝ)
    * emRising s (2 * (M + 1) - 1) / ((N + 1 : ℕ) : ℝ) ^ (s + (2 * ((M + 1 : ℕ) : ℝ)) - 1)

/-- EASY: the direct sum is what the evaluator adds (definitional). -/
theorem emDirect_eq (s : ℝ) (N : Nat) :
    emDirect s N = (Finset.range N).sum fun k => ((k + 1 : ℕ) : ℝ) ^ (-s) := by
  rfl

/- ORIGINAL STATEMENT (kept for reference, commented out):

/-- MEDIUM: integral term identity
`∫_{N+1}^∞ x^{-s} dx = (N+1)^{1-s}/(s-1)` for `0 < s ≠ 1`. -/
theorem emIntegral_eq {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) (N : Nat) :
    (∫ x in ((N + 1 : ℕ) : ℝ)..∞, x ^ (-s)) = ((N + 1 : ℕ) : ℝ) ^ (1 - s) / (s - 1) := by
  sorrry

This cannot be kept as written:
* `∫ x in a..∞, f x` is not Lean/Mathlib syntax (neither in Mathlib `v4.28.0`
  nor in `v4.34.0`); the file did not parse.  The improper integral over
  `[a, ∞)` is written `∫ x in Set.Ioi a, f x`.
* For `0 < s < 1` the integral `∫_{N+1}^∞ x^{-s} dx` diverges, so (with
  Mathlib's convention that non-integrable functions have integral `0`) the
  left side is `0` while the right side `(N+1)^{1-s}/(s-1)` is negative:
  the identity is false there.  It holds exactly for `1 < s`.
-/

/-- MEDIUM (corrected): integral term identity
`∫_{N+1}^∞ x^{-s} dx = (N+1)^{1-s}/(s-1)` for `1 < s`.
(Corrected from the original: improper integral written with `Set.Ioi`, and the
hypothesis `0 < s, s ≠ 1` strengthened to `1 < s`, since the integral diverges
for `s < 1`.) -/
theorem emIntegral_eq {s : ℝ} (hs : 1 < s) (N : Nat) :
    (∫ x in Set.Ioi ((N + 1 : ℕ) : ℝ), x ^ (-s)) = ((N + 1 : ℕ) : ℝ) ^ (1 - s) / (s - 1) := by
  have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  rw [integral_Ioi_rpow_of_lt (by linarith) hpos]
  have h1 : -s + 1 = 1 - s := by ring
  have h2 : s - 1 ≠ 0 := by linarith
  rw [h1, neg_div, ← div_neg, neg_sub]

/-! ### Auxiliary lemmas linking the general Euler–Maclaurin development
(namespace `ZetaEM` above) with the real-valued quantities of this file. -/

lemma emRising_pos {s : ℝ} (hs : 0 < s) (k : ℕ) : 0 < emRising s k :=
  Finset.prod_pos (fun j _ => by positivity)

lemma emRising_succ (s : ℝ) (k : ℕ) : emRising s (k + 1) = emRising s k * (s + k) := by
  simp [emRising, Finset.prod_range_succ]

lemma cRising_ofReal (s : ℝ) (k : ℕ) : ZetaEM.cRising (s : ℂ) k = ((emRising s k : ℝ) : ℂ) := by
  unfold ZetaEM.cRising emRising
  push_cast
  rfl

lemma dF_ofReal (s : ℝ) (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ZetaEM.dF (s : ℂ) j y = (((-1) ^ j * emRising s j * y ^ (-s - j) : ℝ) : ℂ) := by
  unfold ZetaEM.dF
  rw [cRising_ofReal]
  push_cast
  rw [Complex.ofReal_cpow hy]
  push_cast
  ring_nf

lemma bφ_ofReal (r : ℕ) :
    ZetaEM.bφ (2 * r + 2) 0
      = (((bernoulli (2 * (r + 1)) : ℝ) / (Nat.factorial (2 * (r + 1)) : ℝ) : ℝ) : ℂ) := by
  unfold ZetaEM.bφ
  rw [bernoulliFun_eval_zero, show 2 * r + 2 = 2 * (r + 1) by ring]

lemma emPhi_ofReal (N K : ℕ) (s : ℝ) :
    ZetaEM.emPhi N K (s : ℂ)
      = ((emDirect s N + ((N + 1 : ℕ) : ℝ) ^ (1 - s) / (s - 1)
          + ((N + 1 : ℕ) : ℝ) ^ (-s) / 2
          + (Finset.range K).sum (fun r => emCorr s N (r + 1)) : ℝ) : ℂ)
        - ∑' i : ℕ, ZetaEM.emR K (s : ℂ) ((N + 1 + i : ℕ) : ℝ) := by
  have ha : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hD : ∑ k ∈ Finset.range N, ZetaEM.dF (s : ℂ) 0 ((k + 1 : ℕ) : ℝ)
      = ((emDirect s N : ℝ) : ℂ) := by
    rw [emDirect, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [dF_ofReal _ _ (by positivity)]
    simp [emRising]
  have hG : -ZetaEM.emG (s : ℂ) ((N + 1 : ℕ) : ℝ)
      = ((((N + 1 : ℕ) : ℝ) ^ (1 - s) / (s - 1) : ℝ) : ℂ) := by
    unfold ZetaEM.emG
    rw [Complex.ofReal_div, Complex.ofReal_cpow ha.le]
    push_cast
    rw [← div_neg, neg_sub]
  have hH : ZetaEM.dF (s : ℂ) 0 ((N + 1 : ℕ) : ℝ) / 2
      = ((((N + 1 : ℕ) : ℝ) ^ (-s) / 2 : ℝ) : ℂ) := by
    rw [dF_ofReal _ _ (by positivity)]
    simp [emRising]
  have hC : ∑ r ∈ Finset.range K,
        ZetaEM.bφ (2 * r + 2) 0 * ZetaEM.dF (s : ℂ) (2 * r + 1) ((N + 1 : ℕ) : ℝ)
      = -(((Finset.range K).sum (fun r => emCorr s N (r + 1)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [dF_ofReal _ _ ha.le, bφ_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_neg]
    congr 1
    unfold emCorr
    have hr : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
    rw [hr]
    have hexp : ((N + 1 : ℕ) : ℝ) ^ (-s - ((2 * r + 1 : ℕ) : ℝ))
        = 1 / ((N + 1 : ℕ) : ℝ) ^ (s + 2 * (((r + 1 : ℕ) : ℝ)) - 1) := by
      rw [one_div, ← Real.rpow_neg ha.le]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    rw [pow_succ, pow_mul]
    norm_num
    ring
  unfold ZetaEM.emPhi
  simp only [Nat.add_zero]
  rw [hD, sub_eq_add_neg _ (ZetaEM.emG _ _), hG, hH, hC]
  push_cast
  ring

lemma abs_emCorr_eq_tail {s : ℝ} (hs : 0 < s) (N M : ℕ) :
    |emCorr s N (M + 1)| = emTailScale s N M := by
  unfold emCorr emTailScale
  have h1 := emRising_pos hs (2 * (M + 1) - 1)
  have h2 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) ^ (s + 2 * (((M + 1 : ℕ) : ℝ)) - 1) := by positivity
  rw [abs_div, abs_mul, abs_div, abs_of_pos h1, abs_of_pos h2,
    abs_of_pos (by positivity : (0 : ℝ) < (Nat.factorial (2 * (M + 1)) : ℝ))]

lemma norm_tail_le {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) (N M : ℕ) :
    ‖∑' i : ℕ, ZetaEM.emR (M + 1) (s : ℂ) ((N + 1 + i : ℕ) : ℝ)‖ ≤ emTailScale s N M := by
  refine (ZetaEM.norm_tsum_emR_le_real N (by omega) hs hs1).trans (le_of_eq ?_)
  unfold emTailScale
  have ha : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hk : 2 * (M + 1) = (2 * (M + 1) - 1) + 1 := by omega
  rw [cRising_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (emRising_pos hs _), Nat.add_zero]
  rw [show emRising s (2 * (M + 1)) = emRising s (2 * (M + 1) - 1) * (s + ((2 * (M + 1) - 1 : ℕ) : ℝ))
    from by rw [← emRising_succ]; congr 1]
  have hcast : (((2 * (M + 1) - 1 : ℕ)) : ℝ) = 2 * (M : ℝ) + 1 := by
    rw [show 2 * (M + 1) - 1 = 2 * M + 1 by omega]; push_cast; ring
  rw [hcast]
  have hpos : (0 : ℝ) < s + (2 * (M : ℝ) + 1) := by positivity
  have hexp : ((N + 1 : ℕ) : ℝ) ^ (1 - s - 2 * (((M + 1 : ℕ) : ℝ)))
      = 1 / ((N + 1 : ℕ) : ℝ) ^ (s + 2 * (((M + 1 : ℕ) : ℝ)) - 1) := by
    rw [one_div, ← Real.rpow_neg ha.le]
    congr 1
    ring
  rw [hexp]
  have he : s + 2 * (((M + 1 : ℕ) : ℝ)) - 1 = s + (2 * (M : ℝ) + 1) := by push_cast; ring
  rw [he]
  field_simp

-- Note: the proof below does not need `hN`, `hM` or `hNM` (it only uses `0 < s`, `s ≠ 1`);
-- the bound `|R| ≤ 2·T_{M+1}` holds for every `N, M`.  The hypotheses are kept so that the
-- statement stays byte-identical to the requested one.
/-- MAIN: Euler–Maclaurin identity with remainder.
For `0 < s`, `s ≠ 1`, `N ≥ 1`, `M ≥ 1`, `(N+1) ≥ s + 2M + 2`:
`ζ(s) = D + I + H + Σ_{r<M} corr(r) + R` with `|R| ≤ 2·T_{M+1}`. -/
theorem zeta_em_bound {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) {N M : Nat}
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hNM : s + 2 * M + 2 ≤ (N + 1 : ℕ)) :
    |(riemannZeta (s : ℂ)).re
      - (emDirect s N + ((N + 1 : ℕ) : ℝ) ^ (1 - s) / (s - 1)
        + ((N + 1 : ℕ) : ℝ) ^ (-s) / 2
        + (Finset.range M).sum (fun r => emCorr s N (r + 1)))|
      ≤ 2 * emTailScale s N M := by
  have hz := ZetaEM.zeta_eq_emPhi N (K := M + 1) (by omega) (s := (s : ℂ)) (by simpa using hs)
    (by exact_mod_cast hs1)
  rw [emPhi_ofReal] at hz
  set T := ∑' i : ℕ, ZetaEM.emR (M + 1) (s : ℂ) ((N + 1 + i : ℕ) : ℝ)
  have hre : (riemannZeta (s : ℂ)).re
      = emDirect s N + ((N + 1 : ℕ) : ℝ) ^ (1 - s) / (s - 1) + ((N + 1 : ℕ) : ℝ) ^ (-s) / 2
          + (Finset.range (M + 1)).sum (fun r => emCorr s N (r + 1)) - T.re := by
    rw [hz, Complex.sub_re, Complex.ofReal_re]
  rw [hre, Finset.sum_range_succ]
  have hT : |T.re| ≤ emTailScale s N M := (Complex.abs_re_le_norm T).trans (norm_tail_le hs hs1 N M)
  have hC := abs_emCorr_eq_tail hs N M
  calc |emDirect s N + ((N + 1 : ℕ) : ℝ) ^ (1 - s) / (s - 1) + ((N + 1 : ℕ) : ℝ) ^ (-s) / 2
          + ((Finset.range M).sum (fun r => emCorr s N (r + 1)) + emCorr s N (M + 1)) - T.re
        - (emDirect s N + ((N + 1 : ℕ) : ℝ) ^ (1 - s) / (s - 1) + ((N + 1 : ℕ) : ℝ) ^ (-s) / 2
          + (Finset.range M).sum (fun r => emCorr s N (r + 1)))|
        = |emCorr s N (M + 1) - T.re| := by ring_nf
    _ ≤ |emCorr s N (M + 1)| + |T.re| := abs_sub _ _
    _ ≤ 2 * emTailScale s N M := by linarith


end Lynth.Interval.Fns