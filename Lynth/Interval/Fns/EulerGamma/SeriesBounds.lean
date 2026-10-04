import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Brent–McMillan B3 formula for Euler–Mascheroni (FLINT's version)

## Note on the sign of the `K` summand

The originally supplied summand carried a factor `(-1)^k`:

```
noncomputable def bmKterm (m : ℝ) (k : ℕ) : ℝ :=
  (-1) ^ k * ((2 * k)! : ℝ) ^ 3 / ((k ! : ℝ) ^ 4 * (16 * m) ^ (2 * k))
```

With that sign the main bound `eulerMascheroni_bmk` is false (formally refuted by
the prover as theorem `eulerMascheroni_bmk_alt_false`, delivered separately and
not kept here): the asymptotic
expansion of `I₀(2m)·K₀(2m)` has all positive terms, matching FLINT's actual code
(the `(-1)^k` in FLINT's header comment is a typo). The definition below therefore
drops the sign; all other statements are kept as given.
-/

open Real BigOperators Topology Filter Finset Nat

/-- summand of `B`: `x^k/(k!)²`. -/
noncomputable def bmBterm (x : ℝ) (k : ℕ) : ℝ := x ^ k / ((k ! : ℝ)) ^ 2

/-- summand of `A`: `H_k·x^k/(k!)²` (`H_0 = 0`, so the `k = 0` term vanishes). -/
noncomputable def bmAterm (x : ℝ) (k : ℕ) : ℝ := (harmonic k : ℝ) * (x ^ k / ((k ! : ℝ)) ^ 2)

/-- summand of the finite `K` series (all-positive terms; see the note
on FLINT's `(−1)^k` comment typo above). -/
noncomputable def bmKterm (m : ℝ) (k : ℕ) : ℝ :=
  ((2 * k)! : ℝ) ^ 3 / ((k ! : ℝ) ^ 4 * (16 * m) ^ (2 * k))

/-- `B(x) = Σ_{k≥0} x^k/(k!)²` (FLINT's `I₀` at argument `m²`). -/
noncomputable def bmB (x : ℝ) : ℝ := ∑' k : ℕ, bmBterm x k

/-- `A(x) = Σ_{k≥0} H_k·x^k/(k!)²` (FLINT's `S₀`). -/
noncomputable def bmA (x : ℝ) : ℝ := ∑' k : ℕ, bmAterm x k

/-- `K(m) = (1/4m)·Σ_{k<2m} …` (FLINT's `I₀(2m)·K₀(2m)` asymptotic truncation). -/
noncomputable def bmK (m : ℕ) : ℝ :=
  (1 / (4 * (m : ℝ))) * ∑ k ∈ Finset.range (2 * m), bmKterm (m : ℝ) k

lemma harmonic_le_self (k : ℕ) : (harmonic k : ℝ) ≤ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ]; push_cast
    have : (1 : ℝ) / (n + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    rw [one_div] at this
    linarith

lemma harmonic_nonneg' (k : ℕ) : (0 : ℝ) ≤ harmonic k := by
  induction k with
  | zero => simp
  | succ n ih => rw [harmonic_succ]; push_cast; positivity

/-- EASY: the `B` series converges (compare with `exp`: `(k!)² ≥ k!`). -/
theorem bmB_summable (x : ℝ) : Summable (bmBterm x) := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial |x|) (fun k => ?_)
  have h1 : (1 : ℝ) ≤ k ! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [Real.norm_eq_abs, bmBterm, abs_div, abs_pow, abs_of_pos (by positivity : (0:ℝ) < (k ! : ℝ) ^ 2)]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

/-- EASY: the `A` series converges (`H_k ≤ k`, then as for `B`). -/
theorem bmA_summable (x : ℝ) : Summable (bmAterm x) := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial |x|) (fun k => ?_)
  have h1 : (k : ℝ) ≤ k ! := by exact_mod_cast Nat.self_le_factorial k
  have hk : (0 : ℝ) < k ! := by positivity
  rw [Real.norm_eq_abs, bmAterm, abs_mul, abs_div, abs_pow,
    abs_of_pos (by positivity : (0:ℝ) < (k ! : ℝ) ^ 2), abs_of_nonneg (harmonic_nonneg' k)]
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hk]
  have := harmonic_le_self k
  have h2 : (harmonic k : ℝ) * |x| ^ k * (k ! : ℝ) ≤ (k ! : ℝ) * |x| ^ k * (k ! : ℝ) := by
    gcongr; linarith
  nlinarith [pow_nonneg (abs_nonneg x) k]

lemma bmBterm_nonneg (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : 0 ≤ bmBterm x k := by
  unfold bmBterm; positivity

/-- EASY: `B(x) > 0` for `x ≥ 0` (every term is nonnegative, the `k = 0` term is `1`). -/
theorem bmB_pos (x : ℝ) (hx : 0 ≤ x) : 0 < bmB x := by
  have := (bmB_summable x).le_tsum 0 (fun j _ => bmBterm_nonneg x hx j)
  have h0 : bmBterm x 0 = 1 := by simp [bmBterm]
  unfold bmB; linarith

/-- Corrected `bmB_partial_ge_one`: partial sums of `B` with at least one term
stay above `1` (the hypothesis `1 ≤ N` was added; without it the claim fails for `N = 0`,
as shown by the prover's refutation `bmB_partial_ge_one_false`). -/
theorem bmB_partial_ge_one' (x : ℝ) (hx : 0 ≤ x) (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ ∑ k ∈ Finset.range N, bmBterm x k := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have : bmBterm x 0 = 1 := by simp [bmBterm]
  rw [this]
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range n) => bmBterm_nonneg x hx (i + 1))
  linarith

/-- Generic geometric tail bound. -/
lemma tsum_tail_le_geom {f : ℕ → ℝ} {q : ℝ} (hq0 : 0 ≤ q) (N : ℕ) (hr : ∀ k, N ≤ k → f (k + 1) ≤ q * f k) (k : ℕ) : f (k + N) ≤ f N * q ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have := hr (n + N) (by omega)
    rw [show n + 1 + N = n + N + 1 by omega, pow_succ]
    nlinarith

lemma bmBterm_succ (x : ℝ) (k : ℕ) :
    bmBterm x (k + 1) = bmBterm x k * (x / ((k : ℝ) + 1) ^ 2) := by
  unfold bmBterm
  rw [Nat.factorial_succ]; push_cast
  have : (k ! : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma bmBterm_ratio (m N : ℕ) (k : ℕ) (hk : N ≤ k) :
    bmBterm ((m : ℝ) ^ 2) (k + 1) ≤
      ((m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) * bmBterm ((m : ℝ) ^ 2) k := by
  rw [bmBterm_succ, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (bmBterm_nonneg _ (by positivity) k)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have : (N : ℝ) ≤ k := by exact_mod_cast hk
  gcongr

lemma q_lt_one (m N : ℕ) (hN : (m : ℝ) < (N : ℝ) + 1) :
    (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2) < 1 := by
  rw [div_lt_one (by positivity)]
  have : (0:ℝ) ≤ m := by positivity
  nlinarith

/-- MEDIUM: geometric tail bound for `B`. For `k ≥ N` the term ratio is
`x/(k+1)² ≤ q`, so the tail is at most `t_N/(1−q)`. -/
theorem bmB_tail (m : ℕ) (N : ℕ) (hN : (m : ℝ) < (N : ℝ) + 1) :
    |bmB ((m : ℝ) ^ 2) - ∑ k ∈ Finset.range N, bmBterm ((m : ℝ) ^ 2) k|
      ≤ bmBterm ((m : ℝ) ^ 2) N
        / (1 - (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2)) := by
  set x := (m : ℝ) ^ 2 with hx
  set q := (m : ℝ) ^ 2 / (((N : ℝ) + 1) ^ 2) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := q_lt_one m N hN
  have hx0 : 0 ≤ x := by positivity
  have hs := bmB_summable x
  have hsplit := (hs.sum_add_tsum_nat_add N)
  unfold bmB
  rw [← hsplit, add_sub_cancel_left]
  have hb : ∀ k, bmBterm x (k + N) ≤ bmBterm x N * q ^ k :=
    tsum_tail_le_geom hq0 N (fun k hk => bmBterm_ratio m N k hk)
  have hnn : 0 ≤ ∑' k, bmBterm x (k + N) :=
    tsum_nonneg (fun k => bmBterm_nonneg x hx0 _)
  rw [abs_of_nonneg hnn]
  have hg : Summable (fun k : ℕ => bmBterm x N * q ^ k) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  calc ∑' k, bmBterm x (k + N) ≤ ∑' k : ℕ, bmBterm x N * q ^ k :=
        Summable.tsum_le_tsum hb ((summable_nat_add_iff N).mpr hs) hg
    _ = bmBterm x N / (1 - q) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]

lemma harmonic_add_le (N k : ℕ) :
    (harmonic (k + N) : ℝ) ≤ harmonic N + k / ((N : ℝ) + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + N = (n + N) + 1 by omega, harmonic_succ]; push_cast
    have h1 : ((n + N : ℕ) : ℝ) + 1 ≥ (N : ℝ) + 1 := by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have h2 : ((n + N : ℕ) + 1 : ℝ)⁻¹ ≤ ((N : ℝ) + 1)⁻¹ := by
      apply inv_anti₀ (by positivity); push_cast at h1 ⊢; linarith
    push_cast at h2
    have : ((n : ℝ) + 1) / ((N : ℝ) + 1) = n / ((N : ℝ) + 1) + ((N : ℝ) + 1)⁻¹ := by
      field_simp
    rw [this]; linarith

/-- MEDIUM: tail bound for `A`. Uses `H_k ≤ H_N + (k−N)/(N+1)` for `k ≥ N`
(the harmonic tail past `N` grows at most linearly with slope `1/(N+1)`),
combined with the same geometric majorant as `bmB_tail`. -/
theorem bmA_tail (m : ℕ) (N : ℕ) (hN : (m : ℝ) < (N : ℝ) + 1) (hN1 : 1 ≤ N) :
    let x := (m : ℝ) ^ 2
    let q := x / (((N : ℝ) + 1) ^ 2)
    |bmA x - ∑ k ∈ Finset.range N, bmAterm x k|
      ≤ bmBterm x N
        * ((harmonic N : ℝ) / (1 - q) + q / (((N : ℝ) + 1) * (1 - q) ^ 2)) := by
  intro x q
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := q_lt_one m N hN
  have hx0 : 0 ≤ x := by positivity
  have hs := bmA_summable x
  have hsplit := (hs.sum_add_tsum_nat_add N)
  unfold bmA
  rw [← hsplit, add_sub_cancel_left]
  have hA : ∀ k, bmAterm x k = (harmonic k : ℝ) * bmBterm x k := fun k => rfl
  have hb : ∀ k, bmBterm x (k + N) ≤ bmBterm x N * q ^ k :=
    tsum_tail_le_geom hq0 N (fun k hk => bmBterm_ratio m N k hk)
  have hnn : 0 ≤ ∑' k, bmAterm x (k + N) :=
    tsum_nonneg (fun k => by rw [hA]; exact mul_nonneg (harmonic_nonneg' _) (bmBterm_nonneg x hx0 _))
  rw [abs_of_nonneg hnn]
  have htN := bmBterm_nonneg x hx0 N
  have hbound : ∀ k : ℕ, bmAterm x (k + N) ≤
      bmBterm x N * (harmonic N : ℝ) * q ^ k + bmBterm x N / ((N : ℝ) + 1) * (k * q ^ k) := by
    intro k
    rw [hA]
    have h1 := harmonic_add_le N k
    have h2 := hb k
    have h3 := bmBterm_nonneg x hx0 (k + N)
    have h4 := harmonic_nonneg' (k + N)
    calc (harmonic (k + N) : ℝ) * bmBterm x (k + N)
        ≤ (harmonic N + k / ((N : ℝ) + 1)) * (bmBterm x N * q ^ k) := by
          exact mul_le_mul h1 h2 h3 (add_nonneg (harmonic_nonneg' N) (by positivity))
      _ = _ := by ring
  have hnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have hg1 : Summable (fun k : ℕ => bmBterm x N * (harmonic N : ℝ) * q ^ k) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hg2 : Summable (fun k : ℕ => bmBterm x N / ((N : ℝ) + 1) * (k * q ^ k)) := by
    apply Summable.mul_left
    have := summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
    simpa using this
  calc ∑' k, bmAterm x (k + N)
      ≤ ∑' k : ℕ, (bmBterm x N * (harmonic N : ℝ) * q ^ k
          + bmBterm x N / ((N : ℝ) + 1) * (k * q ^ k)) :=
        Summable.tsum_le_tsum hbound ((summable_nat_add_iff N).mpr hs) (hg1.add hg2)
    _ = bmBterm x N * (harmonic N : ℝ) * (1 - q)⁻¹
          + bmBterm x N / ((N : ℝ) + 1) * (q / (1 - q) ^ 2) := by
        rw [Summable.tsum_add hg1 hg2, tsum_mul_left, tsum_mul_left,
          tsum_geometric_of_lt_one hq0 hq1, tsum_coe_mul_geometric_of_norm_lt_one hnorm]
    _ = _ := by
        have : (1 - q) ≠ 0 := by linarith
        field_simp

