import Lynth.Interval.Fns.EulerGamma.Proof.Coefficients

open Real

namespace BM

lemma mc_eq_cc (n : ℕ) : Ring.choose ((1/2 : ℝ) + n - 1) n = cc n := by
  rw [← Ring.multichoose_eq]
  induction n with
  | zero => simp [cc_zero]
  | succ n ih =>
    have h1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1/2 : ℝ) (n + 1)
    have h2 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1/2 : ℝ) n
    rw [Polynomial.ascPochhammer_smeval_eq_eval] at h1 h2
    rw [ascPochhammer_succ_eval, ← h2, ih] at h1
    rw [cc_succ]
    simp only [nsmul_eq_mul, Nat.factorial_succ] at h1
    push_cast at h1
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    have h3 : ((n : ℝ) + 1) * Ring.multichoose (1 / 2 : ℝ) (n + 1) = cc n * (1 / 2 + n) := by
      apply mul_left_cancel₀ hf; linear_combination h1
    linear_combination 2 * h3

lemma cc_hasSum {u : ℝ} (hu0 : 0 ≤ u) (hu : u < 1) :
    HasSum (fun j => cc j * u ^ j) ((1 - u) ^ (-(1 / 2 : ℝ))) := by
  have hp := one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℝ)
  have hmem : u ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right]
    have : ‖u‖₊ < 1 := by
      rw [← NNReal.coe_lt_coe]; simp [abs_of_nonneg hu0, hu]
    rw [enorm_eq_nnnorm]
    exact_mod_cast this
  have h := hp.hasSum hmem
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at h
  simp_rw [mc_eq_cc] at h
  rw [Real.rpow_neg (by linarith), ← one_div]
  exact h

lemma cc_antitone : Antitone cc := by
  refine antitone_nat_of_succ_le (fun j => ?_)
  rw [cc_succ]
  have h1 : (2 * (j : ℝ) + 1) / (2 * j + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have := cc_pos j
  nlinarith

lemma cc_tail_bounds (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu : u < 1) :
    0 ≤ (1 - u) ^ (-(1 / 2 : ℝ)) - ∑ j ∈ Finset.range N, cc j * u ^ j ∧
    (1 - u) ^ (-(1 / 2 : ℝ)) - ∑ j ∈ Finset.range N, cc j * u ^ j
      ≤ u ^ N * (1 - u) ^ (-(1 / 2 : ℝ)) := by
  have hs := cc_hasSum hu0 hu
  have hsum := hs.summable
  have hshift : Summable (fun i => cc (i + N) * u ^ (i + N)) :=
    (summable_nat_add_iff N).mpr hsum
  have heq : (1 - u) ^ (-(1 / 2 : ℝ)) - ∑ j ∈ Finset.range N, cc j * u ^ j
      = ∑' i, cc (i + N) * u ^ (i + N) := by
    rw [← hs.tsum_eq, ← hsum.sum_add_tsum_nat_add N]; ring
  rw [heq]
  constructor
  · exact tsum_nonneg (fun i => by have := cc_pos (i + N); positivity)
  · rw [← hs.tsum_eq, ← tsum_mul_left]
    refine hshift.tsum_le_tsum (fun i => ?_) (hsum.mul_left _)
    rw [pow_add]
    have h1 := cc_antitone (Nat.le_add_right i N)
    have := pow_nonneg hu0 i
    have := pow_nonneg hu0 N
    calc cc (i + N) * (u ^ i * u ^ N) ≤ cc i * (u ^ i * u ^ N) := by gcongr
      _ = u ^ N * (cc i * u ^ i) := by ring

end BM
