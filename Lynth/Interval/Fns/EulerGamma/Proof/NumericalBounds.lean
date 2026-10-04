import Lynth.Interval.Fns.EulerGamma.Proof.Coefficients

/-!
# Elementary numerical bounds on `c_j`, `n!` and `p_j`
-/

open Real Finset Nat

namespace BM

lemma cc_sq_le (n : ℕ) : cc n ^ 2 ≤ 1 / (3 * n + 1) := by
  induction n with
  | zero => simp [cc_zero]
  | succ n ih =>
    rw [cc_succ, mul_pow]
    have h0 : (0 : ℝ) ≤ ((2 * n + 1) / (2 * n + 2)) ^ 2 := by positivity
    calc cc n ^ 2 * ((2 * (n : ℝ) + 1) / (2 * n + 2)) ^ 2
        ≤ 1 / (3 * n + 1) * ((2 * (n : ℝ) + 1) / (2 * n + 2)) ^ 2 :=
          mul_le_mul_of_nonneg_right ih h0
      _ ≤ 1 / (3 * ((n + 1 : ℕ) : ℝ) + 1) := by
          push_cast
          rw [show (1:ℝ) / (3 * n + 1) * ((2 * n + 1) / (2 * n + 2)) ^ 2
              = (2 * n + 1) ^ 2 / ((3 * n + 1) * (2 * n + 2) ^ 2) by field_simp,
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith

/-- Stirling-type upper bound `n! ≤ e √n (n/e)^n`. -/
lemma factorial_le_stirling (n : ℕ) (hn : 1 ≤ n) :
    (n ! : ℝ) ≤ exp 1 * √(n : ℝ) * (n : ℝ) ^ n * exp (-(n : ℝ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  simp only [Function.comp, Stirling.stirlingSeq_one] at h
  unfold Stirling.stirlingSeq at h
  have hpos : 0 < √(2 * ((k + 1 : ℕ) : ℝ)) * (((k + 1 : ℕ) : ℝ) / exp 1) ^ (k + 1) := by
    positivity
  rw [div_le_iff₀ hpos] at h
  refine h.trans (le_of_eq ?_)
  rw [div_pow, Real.sqrt_mul (by norm_num), Real.exp_neg, ← Real.exp_nat_mul, mul_one]
  have h2 : √(2:ℝ) ≠ 0 := by positivity
  have he : exp ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

lemma factorial_div_pow_le (n : ℕ) (hn : 1 ≤ n) :
    (n ! : ℝ) / (n : ℝ) ^ n ≤ exp 1 * √(n : ℝ) * exp (-(n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) ^ n := by
    have : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  rw [div_le_iff₀ hn0]
  have := factorial_le_stirling n hn
  linarith

lemma sqrt_pi_le : √π ≤ 1.7725 := by
  rw [Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_lt_d4]

lemma exp_one_le : exp 1 ≤ 2.7183 := by
  have := Real.exp_one_lt_d9; linarith

theorem pp_self_le (n : ℕ) (hn : 4 ≤ n) : pp n n ≤ exp (-(n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  rw [pp_eq]
  unfold aa
  have h1 := cc_sq_le n
  have h2 := factorial_div_pow_le n hn1
  have hsq : √(n : ℝ) ≤ 2 / 13 * (3 * n + 1) := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hen := Real.exp_pos (-(n : ℝ))
  have hc0 : 0 ≤ cc n ^ 2 := by positivity
  have hfac0 : (0 : ℝ) ≤ (n ! : ℝ) / (n : ℝ) ^ n := by positivity
  calc √π * (cc n ^ 2 * (n ! : ℝ)) / (n : ℝ) ^ n
      = √π * cc n ^ 2 * ((n ! : ℝ) / (n : ℝ) ^ n) := by ring
    _ ≤ 1.7725 * (1 / (3 * n + 1)) * (exp 1 * √(n : ℝ) * exp (-(n : ℝ))) := by
        gcongr
        · exact sqrt_pi_le
    _ ≤ 1.7725 * (1 / (3 * n + 1)) * (2.7183 * (2 / 13 * (3 * n + 1)) * exp (-(n : ℝ))) := by
        gcongr
        · exact exp_one_le
    _ = 1.7725 * 2.7183 * (2 / 13) * exp (-(n : ℝ)) := by
        field_simp
    _ ≤ exp (-(n : ℝ)) := by nlinarith

lemma pp_pred_le (n : ℕ) (hn : 4 ≤ n) : pp n (n - 1) ≤ 0.97 * exp (-(n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, pp_eq]
  unfold aa
  have h1 := cc_sq_le k
  have h2 := factorial_div_pow_le (k + 1) hn1
  have hk : ((k : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
  set N : ℝ := ((k + 1 : ℕ) : ℝ) with hN
  have hfac' : (k ! : ℝ) / N ^ k = ((k + 1) ! : ℝ) / N ^ (k + 1) := by
    rw [Nat.factorial_succ, pow_succ]; push_cast
    have : (k : ℝ) + 1 = N := by rw [hN]; push_cast; ring
    rw [this]
    have hN0 : N ≠ 0 := by positivity
    field_simp
  have hsq : √N ≤ 0.2 * (3 * N - 2) := by
    rw [Real.sqrt_le_left (by nlinarith)]; nlinarith
  rw [hk] at h1
  have hen := Real.exp_pos (-N)
  have hc0 : 0 ≤ cc k ^ 2 := by positivity
  have hfac0 : (0 : ℝ) ≤ ((k + 1) ! : ℝ) / N ^ (k + 1) := by positivity
  have h3 : 0 < 3 * N - 2 := by linarith
  calc √π * (cc k ^ 2 * (k ! : ℝ)) / N ^ k
      = √π * cc k ^ 2 * ((k ! : ℝ) / N ^ k) := by ring
    _ = √π * cc k ^ 2 * (((k + 1) ! : ℝ) / N ^ (k + 1)) := by rw [hfac']
    _ ≤ 1.7725 * (1 / (3 * (N - 1) + 1)) * (exp 1 * √N * exp (-N)) := by
        have hpos : 0 < 3 * (N - 1) + 1 := by linarith
        exact mul_le_mul (mul_le_mul sqrt_pi_le h1 hc0 (by norm_num)) h2 hfac0
          (mul_nonneg (by norm_num) (by rw [one_div]; exact inv_nonneg.mpr hpos.le))
    _ ≤ 1.7725 * (1 / (3 * N - 2)) * (2.7183 * (0.2 * (3 * N - 2)) * exp (-N)) := by
        rw [show 3 * (N - 1) + 1 = 3 * N - 2 by ring]
        gcongr
        · exact exp_one_le
    _ = 1.7725 * 2.7183 * 0.2 * exp (-N) := by
        have h3 : 3 * N - 2 ≠ 0 := by intro h; linarith
        field_simp
    _ ≤ 0.97 * exp (-N) := by nlinarith

end BM
