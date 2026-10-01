import Mathlib

/-!
# Power series on the unit disc

A small toolbox for power series `∑ₙ cₙ zⁿ` that converge on the open unit disc — which is the
case for all the hypergeometric series considered in this project.  The identities are proved by
differentiating such a series term by term.

* `Complex.SeriesOnDisc c` : the series `∑ₙ ‖cₙ‖ rⁿ` converges for every `0 ≤ r < 1`;
* `Complex.seriesOnDisc_of_bdd` : bounded coefficients define such a series;
* `Complex.SeriesOnDisc.summable` : the series converges absolutely on the open unit disc;
* `Complex.SeriesOnDisc.shift` : the differentiated coefficients `(n+1) cₙ₊₁` again define such a
  series;
* `Complex.SeriesOnDisc.hasDerivAt` : term-by-term differentiation,
  `d/dz ∑ₙ cₙ zⁿ = ∑ₙ (n+1) cₙ₊₁ zⁿ` on the open unit disc.
-/

open Metric

namespace Complex

/-- The coefficients `c` define a power series that converges absolutely on the open unit disc. -/
def SeriesOnDisc (c : ℕ → ℂ) : Prop :=
  ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun n : ℕ => ‖c n‖ * r ^ n

theorem seriesOnDisc_of_bdd {c : ℕ → ℂ} {B : ℝ} (h : ∀ n, ‖c n‖ ≤ B) : SeriesOnDisc c := by
  intro r hr0 hr1
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left B)
  exact mul_le_mul_of_nonneg_right (h n) (by positivity)

/-- A ratio test: if eventually `‖cₙ₊₁‖ ≤ (1 + K/(n+1)) ‖cₙ‖`, the coefficients grow at most
polynomially and the series converges on the open unit disc. -/
theorem seriesOnDisc_of_ratio_bound {c : ℕ → ℂ} {K : ℝ} (N : ℕ)
    (h : ∀ n ≥ N, ‖c (n + 1)‖ ≤ (1 + K / (n + 1)) * ‖c n‖) : SeriesOnDisc c := by
  intro r hr0 hr1
  rcases eq_or_lt_of_le hr0 with hr | hr
  · -- `r = 0`: only the term `n = 0` is nonzero
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have hn0 : n ≠ 0 := by simpa using hn
    rw [← hr, zero_pow hn0, mul_zero]
  · set q : ℝ := (r + 1) / 2 with hq
    have hq1 : q < 1 := by rw [hq]; linarith
    have hrq : r < q := by rw [hq]; linarith
    refine summable_of_ratio_norm_eventually_le hq1 ?_
    -- choose `n` large enough that `r (1 + K/(n+1)) ≤ q`
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt (K * r / (q - r))
    filter_upwards [Filter.eventually_ge_atTop (max N N₁)] with n hn
    have hnN : n ≥ N := le_trans (le_max_left _ _) hn
    have hnN₁ : (N₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hn
    have hkey : r * (1 + K / (n + 1)) ≤ q := by
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h1 : K * r / (q - r) < (n : ℝ) + 1 := by linarith [hN₁]
      have h2 : K * r < (q - r) * ((n : ℝ) + 1) := by
        rw [div_lt_iff₀ (by linarith)] at h1
        linarith
      have h3 : r * (K / ((n : ℝ) + 1)) ≤ q - r := by
        rw [mul_div_assoc', div_le_iff₀ hn1]
        linarith
      have hexp : r * (1 + K / ((n : ℝ) + 1)) = r + r * (K / ((n : ℝ) + 1)) := by ring
      linarith
    have hcn := h n hnN
    have hnorm : ‖c (n + 1)‖ * r ^ (n + 1) ≤ q * (‖c n‖ * r ^ n) := by
      have hrn : (0 : ℝ) < r ^ n := by positivity
      calc ‖c (n + 1)‖ * r ^ (n + 1) ≤ ((1 + K / (n + 1)) * ‖c n‖) * r ^ (n + 1) := by gcongr
        _ = (r * (1 + K / (n + 1))) * (‖c n‖ * r ^ n) := by ring
        _ ≤ q * (‖c n‖ * r ^ n) := by gcongr
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    exact hnorm

namespace SeriesOnDisc

variable {c : ℕ → ℂ} {z : ℂ}

theorem summable_norm (hc : SeriesOnDisc c) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖c n * z ^ n‖ := by
  refine (hc ‖z‖ (norm_nonneg z) hz).congr fun n => ?_
  rw [norm_mul, norm_pow]

theorem summable (hc : SeriesOnDisc c) (hz : ‖z‖ < 1) : Summable fun n : ℕ => c n * z ^ n :=
  Summable.of_norm (hc.summable_norm hz)

theorem hasSum (hc : SeriesOnDisc c) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => c n * z ^ n) (∑' n : ℕ, c n * z ^ n) :=
  (hc.summable hz).hasSum

/-- The terms `‖cₙ‖ rⁿ` are bounded for `r < 1`. -/
theorem exists_bound (hc : SeriesOnDisc c) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ n, ‖c n‖ * r ^ n ≤ M := by
  have hsum := hc r hr0 hr1
  refine ⟨max (∑' n : ℕ, ‖c n‖ * r ^ n) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun n => le_trans ?_ (le_max_left _ _)⟩
  exact hsum.le_tsum n fun i _ => by positivity

/-- The termwise derivative of a series convergent on the unit disc is dominated by a summable
sequence on every smaller disc. -/
theorem summable_deriv_bound (hc : SeriesOnDisc c) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => ‖c n‖ * n * r ^ (n - 1) := by
  set r₁ : ℝ := (r + 1) / 2 with hr₁def
  have hr₁0 : 0 < r₁ := by rw [hr₁def]; linarith
  have hr₁1 : r₁ < 1 := by rw [hr₁def]; linarith
  have hrr₁ : r < r₁ := by rw [hr₁def]; linarith
  obtain ⟨M, hM0, hM⟩ := hc.exists_bound hr₁0.le hr₁1
  set q : ℝ := r / r₁ with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hqdef, div_lt_one hr₁0]; exact hrr₁
  have hgeo : Summable fun n : ℕ => (n : ℝ) * q ^ (n - 1) := by
    rw [← summable_nat_add_iff 1]
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := q)
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])
    refine (h.add (summable_geometric_of_lt_one hq0 hq1)).congr fun n => ?_
    push_cast
    ring
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hgeo.mul_left (M / r₁))
  match n with
  | 0 => simp
  | (m + 1) =>
      have hcm : ‖c (m + 1)‖ * r₁ ^ (m + 1) ≤ M := hM (m + 1)
      have hcm' : ‖c (m + 1)‖ ≤ M / r₁ ^ (m + 1) :=
        (le_div_iff₀ (by positivity)).mpr hcm
      have hq : q ^ m = r ^ m / r₁ ^ m := by rw [hqdef, div_pow]
      simp only [Nat.add_sub_cancel, hq, Nat.cast_add, Nat.cast_one]
      have h1 : ‖c (m + 1)‖ * ((m : ℝ) + 1) * r ^ m
          ≤ (M / r₁ ^ (m + 1)) * ((m : ℝ) + 1) * r ^ m := by gcongr
      refine h1.trans_eq ?_
      field_simp
      ring

theorem shift (hc : SeriesOnDisc c) : SeriesOnDisc fun n : ℕ => ((n : ℂ) + 1) * c (n + 1) := by
  intro r hr0 hr1
  have h := hc.summable_deriv_bound hr0 hr1
  rw [← summable_nat_add_iff 1] at h
  refine h.congr fun n => ?_
  rw [norm_mul]
  have : ‖((n : ℂ) + 1)‖ = ((n : ℝ) + 1) := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [this]
  push_cast
  ring

/-- Term-by-term differentiation of a power series on the open unit disc. -/
theorem hasDerivAt (hc : SeriesOnDisc c) (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : ℂ => ∑' n : ℕ, c n * w ^ n)
      (∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * z ^ n) z := by
  set r : ℝ := (‖z‖ + 1) / 2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hr1 : r < 1 := by rw [hrdef]; linarith
  have hzr : z ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, hrdef]; linarith
  have hmem : ∀ w ∈ ball (0 : ℂ) r, ‖w‖ < 1 := fun w hw =>
    lt_trans (mem_ball_zero_iff.mp hw) hr1
  have hderiv := hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => ‖c n‖ * n * r ^ (n - 1))
    (g := fun n w => c n * w ^ n) (g' := fun n w => c n * ((n : ℂ) * w ^ (n - 1)))
    (hc.summable_deriv_bound hr0.le hr1) isOpen_ball (convex_ball _ _).isPreconnected
    (fun n w _ => (hasDerivAt_pow n w).const_mul (c n))
    (fun n w hw => by
      have hwr : ‖w‖ ≤ r := (mem_ball_zero_iff.mp hw).le
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hwr _) (by positivity))
    (mem_ball_self hr0) (hc.summable (z := 0) (by simp)) hzr
  refine hderiv.congr_deriv ?_
  -- reindex the derivative series
  set S : ℂ := ∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * z ^ n with hS
  have h1 : HasSum (fun n : ℕ => ((n : ℂ) + 1) * c (n + 1) * z ^ n) S := hc.shift.hasSum hz
  have h2 : HasSum (fun n : ℕ => c (n + 1) * ((((n + 1 : ℕ)) : ℂ) * z ^ ((n + 1) - 1))) S :=
    h1.congr_fun fun n => by push_cast; ring
  have h3 := (hasSum_nat_add_iff (f := fun n : ℕ => c n * ((n : ℂ) * z ^ (n - 1))) 1).mp h2
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, mul_zero,
    add_zero] at h3
  exact h3.tsum_eq

/-- `∑ₙ n cₙ zⁿ = z ∑ₙ (n+1) cₙ₊₁ zⁿ`. -/
theorem hasSum_mul_index (hc : SeriesOnDisc c) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (n : ℂ) * c n * z ^ n)
      (z * ∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * z ^ n) := by
  set S : ℂ := ∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * z ^ n with hS
  have h1 : HasSum (fun n : ℕ => ((n : ℂ) + 1) * c (n + 1) * z ^ n) S := hc.shift.hasSum hz
  have h2 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * c (n + 1) * z ^ (n + 1)) (z * S) := by
    refine (h1.mul_left z).congr_fun fun n => ?_
    push_cast
    ring
  have h3 := (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℂ) * c n * z ^ n) 1).mp h2
  simpa using h3

/-- The combination appearing when differentiating `v ↦ v · ∑ₙ cₙ (v²)ⁿ`. -/
theorem hasSum_deriv_combo (hc : SeriesOnDisc c) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (2 * (n : ℂ) + 1) * c n * z ^ n)
      ((∑' n : ℕ, c n * z ^ n) + 2 * z * ∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * z ^ n) := by
  have h := (hc.hasSum hz).add ((hc.hasSum_mul_index hz).mul_left 2)
  have h' : HasSum (fun n : ℕ => (2 * (n : ℂ) + 1) * c n * z ^ n)
      ((∑' n : ℕ, c n * z ^ n) + 2 * (z * ∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * z ^ n)) :=
    h.congr_fun fun n => by ring
  simpa [mul_assoc] using h'

/-- The same combination for the differentiated coefficients, written directly in terms of `c`. -/
theorem hasSum_deriv_combo_shift (hc : SeriesOnDisc c) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (2 * (n : ℂ) + 1) * (((n : ℂ) + 1) * c (n + 1)) * z ^ n)
      ((∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * z ^ n)
        + 2 * z * ∑' n : ℕ, ((n : ℂ) + 1) * (((n : ℂ) + 1 + 1) * c (n + 1 + 1)) * z ^ n) := by
  have h := hc.shift.hasSum_deriv_combo hz
  have hC : (∑' n : ℕ, ((n : ℂ) + 1) * ((((n + 1 : ℕ) : ℂ) + 1) * c (n + 1 + 1)) * z ^ n)
      = ∑' n : ℕ, ((n : ℂ) + 1) * (((n : ℂ) + 1 + 1) * c (n + 1 + 1)) * z ^ n :=
    tsum_congr fun n => by push_cast; ring
  rw [hC] at h
  exact h

/-- Termwise differentiation of the even series `v ↦ ∑ₙ cₙ (v²)ⁿ`. -/
theorem hasDerivAt_even_series (hc : SeriesOnDisc c) {v : ℂ} (hv : ‖v‖ < 1) :
    HasDerivAt (fun w : ℂ => ∑' n : ℕ, c n * (w ^ 2) ^ n)
      (2 * v * ∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * (v ^ 2) ^ n) v := by
  have hv2 : ‖v ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg v]
  have h1 : HasDerivAt (fun w : ℂ => w ^ 2) (2 * v) v := by
    simpa using hasDerivAt_pow 2 v
  have h2 := (hc.hasDerivAt hv2).comp v h1
  simp only [Function.comp_def] at h2
  exact h2.congr_deriv (by ring)

/-- Termwise differentiation of the odd series `v ↦ v · ∑ₙ cₙ (v²)ⁿ`. -/
theorem hasDerivAt_odd_series (hc : SeriesOnDisc c) {v : ℂ} (hv : ‖v‖ < 1) :
    HasDerivAt (fun w : ℂ => w * ∑' n : ℕ, c n * (w ^ 2) ^ n)
      ((∑' n : ℕ, c n * (v ^ 2) ^ n)
        + 2 * v ^ 2 * ∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * (v ^ 2) ^ n) v := by
  have h := (hasDerivAt_id v).mul (hc.hasDerivAt_even_series hv)
  simp only [id_eq] at h
  exact h.congr_deriv (by ring)

end SeriesOnDisc

/-- Two holomorphic functions on a disc centred at `0` with the same derivative and the same
value at `0` agree. -/
theorem eq_of_hasDerivAt_ball {F G D : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hF : ∀ w ∈ ball (0 : ℂ) r, HasDerivAt F (D w) w)
    (hG : ∀ w ∈ ball (0 : ℂ) r, HasDerivAt G (D w) w)
    (h0 : F 0 = G 0) {v : ℂ} (hv : v ∈ ball (0 : ℂ) r) : F v = G v := by
  set H : ℂ → ℂ := fun w => F w - G w with hH
  have hderiv : ∀ w ∈ ball (0 : ℂ) r, HasDerivAt H 0 w := fun w hw =>
    ((hF w hw).sub (hG w hw)).congr_deriv (sub_self _)
  have hdiff : DifferentiableOn ℂ H (ball (0 : ℂ) r) := fun w hw =>
    ((hderiv w hw).differentiableAt).differentiableWithinAt
  have hd0 : Set.EqOn (deriv H) 0 (ball (0 : ℂ) r) := fun w hw => by simp [(hderiv w hw).deriv]
  have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
    hdiff hd0 hv (mem_ball_self hr)
  have : F v - G v = F 0 - G 0 := hconst
  rw [h0] at this
  linear_combination this

end Complex
