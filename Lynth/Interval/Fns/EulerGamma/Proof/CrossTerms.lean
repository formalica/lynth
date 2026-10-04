import Lynth.Interval.Fns.EulerGamma.Proof.NumericalBounds

/-!
# The cross terms of the product of the two truncated expansions
-/

open Real Finset Nat

namespace BM

lemma pp_succ (n j : ℕ) (hn : 1 ≤ n) :
    pp n (j + 1) = pp n j * ((2 * j + 1) ^ 2 / (4 * (j + 1) * n)) := by
  rw [pp_eq, pp_eq, aa_succ, pow_succ]
  have : (n : ℝ) ≠ 0 := by have : (1:ℝ) ≤ n := by exact_mod_cast hn
                           linarith
  field_simp
  ring

lemma pp_pos (n j : ℕ) (hn : 1 ≤ n) : 0 < pp n j := by
  rw [pp_eq]
  have : (0:ℝ) < n := by exact_mod_cast hn
  have := aa_pos j
  have := Real.sqrt_pos.mpr Real.pi_pos
  positivity

/-- log-convexity of `p_j`: a single swap. -/
lemma pp_swap (n a b : ℕ) (hn : 1 ≤ n) (hab : a < b) :
    pp n (a + 1) * pp n b ≤ pp n a * pp n (b + 1) := by
  rw [pp_succ n a hn, pp_succ n b hn]
  have ha := pp_pos n a hn
  have hb := pp_pos n b hn
  have hr : (2 * (a : ℝ) + 1) ^ 2 / (4 * (a + 1) * n) ≤ (2 * (b : ℝ) + 1) ^ 2 / (4 * (b + 1) * n) := by
    have hnp : (0:ℝ) < n := by exact_mod_cast hn
    have hab' : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have ha0 : (0:ℝ) ≤ a := by positivity
    have hb0 : (0:ℝ) ≤ b := by positivity
    have key : 0 ≤ ((b : ℝ) - a) * (4 * a * b + 4 * (a + b) + 3) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [mul_nonneg key hnp.le]
  calc pp n a * ((2 * (a : ℝ) + 1) ^ 2 / (4 * (a + 1) * n)) * pp n b
      = pp n a * pp n b * ((2 * (a : ℝ) + 1) ^ 2 / (4 * (a + 1) * n)) := by ring
    _ ≤ pp n a * pp n b * ((2 * (b : ℝ) + 1) ^ 2 / (4 * (b + 1) * n)) := by
        gcongr
    _ = _ := by ring

/-- log-convexity of `p_j`: spreading a pair apart increases the product. -/
lemma pp_spread (n : ℕ) (hn : 1 ≤ n) : ∀ (k d l : ℕ), d + k ≤ l →
    pp n (d + k) * pp n l ≤ pp n d * pp n (l + k) := by
  intro k
  induction k with
  | zero => intro d l _; simp
  | succ k ih =>
    intro d l h
    have h1 := pp_swap n (d + k) l hn (by omega)
    have h2 := ih d (l + 1) (by omega)
    have hd := pp_pos n (d + k + 1) hn
    calc pp n (d + (k + 1)) * pp n l = pp n (d + k + 1) * pp n l := by rw [← add_assoc]
      _ ≤ pp n (d + k) * pp n (l + 1) := h1
      _ ≤ pp n d * pp n (l + 1 + k) := h2
      _ = pp n d * pp n (l + (k + 1)) := by rw [add_assoc, add_comm 1 k]

lemma pp_pair_le (n j l : ℕ) (hn : 1 ≤ n) (hj : j < n) (hl : l < n) (hjl : n ≤ j + l) :
    pp n j * pp n l ≤ pp n (j + l + 1 - n) * pp n (n - 1) := by
  rcases le_total j l with h | h
  · have := pp_spread n hn (n - 1 - l) (j + l + 1 - n) l (by omega)
    rw [show j + l + 1 - n + (n - 1 - l) = j by omega, show l + (n - 1 - l) = n - 1 by omega]
      at this
    exact this
  · have := pp_spread n hn (n - 1 - j) (j + l + 1 - n) j (by omega)
    rw [show j + l + 1 - n + (n - 1 - j) = l by omega, show j + (n - 1 - j) = n - 1 by omega]
      at this
    linarith [mul_comm (pp n j) (pp n l)]

lemma factorial_div_pow_le_two (n : ℕ) (hn : 1 ≤ n) : ∀ d : ℕ, 2 ≤ d → d ≤ n →
    (d ! : ℝ) / (n : ℝ) ^ d ≤ 2 / (n : ℝ) ^ 2 := by
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  intro d hd hdn
  induction d with
  | zero => omega
  | succ d ih =>
    rcases Nat.lt_or_ge d 2 with h | h
    · interval_cases d
      · omega
      · simp [Nat.factorial]
    · have := ih h (by omega)
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      have hd1 : ((d : ℝ) + 1) ≤ n := by exact_mod_cast hdn
      calc ((d : ℝ) + 1) * (d ! : ℝ) / ((n : ℝ) ^ d * n)
          = ((d ! : ℝ) / (n : ℝ) ^ d) * (((d : ℝ) + 1) / n) := by field_simp
        _ ≤ (2 / (n : ℝ) ^ 2) * 1 := by
            gcongr
            · rw [div_le_one hnp]; exact hd1
        _ = 2 / (n : ℝ) ^ 2 := by ring

lemma sum_pp_le (n : ℕ) (hn : 2 ≤ n) :
    ∑ d ∈ Finset.Ico 1 n, pp n d ≤ √π * (15 / 28) / n := by
  have hnp : (0:ℝ) < n := by have : (2:ℝ) ≤ n := by exact_mod_cast hn
                             linarith
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have h1 : pp n 1 = √π * (1 / 4) / n := by
    rw [pp_eq]; simp [aa, cc]; ring
  have h2 : ∀ d ∈ Finset.Ico 2 n, pp n d ≤ √π * (2 / 7) / (n : ℝ) ^ 2 := by
    intro d hd
    rw [Finset.mem_Ico] at hd
    rw [pp_eq]; unfold aa
    have hc := cc_sq_le d
    have hd2 : (2:ℝ) ≤ d := by exact_mod_cast hd.1
    have hc' : cc d ^ 2 ≤ 1 / 7 := hc.trans (by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    have hf := factorial_div_pow_le_two n (by omega) d hd.1 hd.2.le
    have hc0 : 0 ≤ cc d ^ 2 := by positivity
    have hs0 : 0 ≤ √π := Real.sqrt_nonneg _
    calc √π * (cc d ^ 2 * (d ! : ℝ)) / (n : ℝ) ^ d
        = √π * cc d ^ 2 * ((d ! : ℝ) / (n : ℝ) ^ d) := by ring
      _ ≤ √π * (1 / 7) * (2 / (n : ℝ) ^ 2) := by gcongr
      _ = √π * (2 / 7) / (n : ℝ) ^ 2 := by ring
  have h3 := Finset.sum_le_card_nsmul _ _ _ h2
  rw [Nat.card_Ico, nsmul_eq_mul] at h3
  have hcard : ((n - 2 : ℕ) : ℝ) ≤ n := by
    have : n - 2 ≤ n := Nat.sub_le n 2
    exact_mod_cast this
  have hb : ((n - 2 : ℕ) : ℝ) * (√π * (2 / 7) / (n : ℝ) ^ 2) ≤ √π * (2 / 7) / n := by
    have : 0 ≤ √π * (2 / 7) / (n : ℝ) ^ 2 := by positivity
    calc ((n - 2 : ℕ) : ℝ) * (√π * (2 / 7) / (n : ℝ) ^ 2)
        ≤ n * (√π * (2 / 7) / (n : ℝ) ^ 2) := by gcongr
      _ = √π * (2 / 7) / n := by field_simp
  rw [h1]
  calc √π * (1 / 4) / n + ∑ d ∈ Finset.Ico (1 + 1) n, pp n d
      ≤ √π * (1 / 4) / n + √π * (2 / 7) / n := by linarith
    _ = √π * (15 / 28) / n := by ring

theorem cross_bound' (n : ℕ) (hn : 4 ≤ n) :
    ∑ j ∈ range n, ∑ l ∈ Ico (n - j) n, pp n j * pp n l ≤ 2 * exp (-(n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hnp : (0:ℝ) < n := by exact_mod_cast hn1
  have hpred := pp_pred_le n hn
  have hS := sum_pp_le n (by omega)
  have hpp0 : 0 ≤ pp n (n - 1) := pp_nonneg _ _
  have hS0 : 0 ≤ ∑ d ∈ Finset.Ico 1 n, pp n d := Finset.sum_nonneg (fun _ _ => pp_nonneg _ _)
  -- each inner sum is bounded by `p_{n-1} Σ_{d ∈ [1,n)} p_d`
  have hinner : ∀ j ∈ range n, ∑ l ∈ Ico (n - j) n, pp n j * pp n l
      ≤ pp n (n - 1) * ∑ d ∈ Finset.Ico 1 n, pp n d := by
    intro j hj
    rw [Finset.mem_range] at hj
    calc ∑ l ∈ Ico (n - j) n, pp n j * pp n l
        ≤ ∑ l ∈ Ico (n - j) n, pp n (j + l + 1 - n) * pp n (n - 1) := by
          refine Finset.sum_le_sum (fun l hl => ?_)
          rw [Finset.mem_Ico] at hl
          exact pp_pair_le n j l hn1 hj hl.2 (by omega)
      _ = pp n (n - 1) * ∑ l ∈ Ico (n - j) n, pp n (j + l + 1 - n) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ ≤ pp n (n - 1) * ∑ d ∈ Finset.Ico 1 n, pp n d := by
          gcongr
          -- reindex `d = j + l + 1 - n`, which ranges over `[1, j] ⊆ [1, n)`
          have : ∑ l ∈ Ico (n - j) n, pp n (j + l + 1 - n) = ∑ d ∈ Ico 1 (j + 1), pp n d := by
            refine Finset.sum_nbij' (fun l => j + l + 1 - n) (fun d => d + n - j - 1) ?_ ?_ ?_ ?_ ?_
            · intro l hl; simp only [Finset.mem_Ico] at hl ⊢; omega
            · intro d hd; simp only [Finset.mem_Ico] at hd ⊢; omega
            · intro l hl; simp only [Finset.mem_Ico] at hl ⊢; omega
            · intro d hd; simp only [Finset.mem_Ico] at hd ⊢; omega
            · intro l hl; rfl
          rw [this]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Ico_subset_Ico_right (by omega)) (fun _ _ _ => pp_nonneg _ _)
  calc ∑ j ∈ range n, ∑ l ∈ Ico (n - j) n, pp n j * pp n l
      ≤ ∑ j ∈ range n, pp n (n - 1) * ∑ d ∈ Finset.Ico 1 n, pp n d := Finset.sum_le_sum hinner
    _ = n * (pp n (n - 1) * ∑ d ∈ Finset.Ico 1 n, pp n d) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ n * (0.97 * exp (-(n : ℝ)) * (√π * (15 / 28) / n)) := by
        gcongr
    _ = 0.97 * √π * (15 / 28) * exp (-(n : ℝ)) := by field_simp
    _ ≤ 2 * exp (-(n : ℝ)) := by
        have := sqrt_pi_le
        have := Real.exp_pos (-(n : ℝ))
        nlinarith

end BM
