module

import Mathlib

/-! Portable real endpoint bounds needed by principal complex projections. -/
namespace Intgrl

/-- A square root of an integral logarithmic weight fits the next integer
logarithmic exponent, with a remaining real coefficient between zero and one. -/
theorem real_sqrt_log_scaled {t p a : ℝ} {m : ℕ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧
      Real.sqrt (t^p * (1-Real.log t)^m * a) =
        t^(p/2) * (1-Real.log t)^((m+1)/2) * (u * Real.sqrt a) := by
  let L : ℝ := 1 - Real.log t
  have hlog : Real.log t ≤ 0 := Real.log_nonpos (le_of_lt ht) ht1
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLnonneg : 0 ≤ L := le_of_lt hLpos
  have htp : 0 < t^p := Real.rpow_pos_of_pos ht p
  have hLm : 0 ≤ L^m := by positivity
  have hsqt : Real.sqrt (t^p) = t^(p/2) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul (le_of_lt ht) p (1/2)]
    congr 1
    ring
  have hsqm : Real.sqrt (L^m) = L^((m:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast L m]
    rw [← Real.rpow_mul hLnonneg (m:ℝ) (1/2)]
    congr 1
    ring
  let q : ℝ := ((m+1)/2 : ℕ)
  have hq : (m:ℝ)/2 ≤ q := by
    have hn : m ≤ 2 * ((m+1)/2) := by omega
    have hn' : (m:ℝ) ≤ 2 * (((m+1)/2 : ℕ):ℝ) := by exact_mod_cast hn
    dsimp [q]
    nlinarith
  let u : ℝ := L^((m:ℝ)/2 - q)
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact Real.rpow_nonneg hLnonneg _
  have hu1 : u ≤ 1 := by
    dsimp [u]
    exact Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  refine ⟨u, hu0, hu1, ?_⟩
  rw [show t^p * (1-Real.log t)^m * a = (t^p * (1-Real.log t)^m) * a by ring]
  rw [Real.sqrt_mul (mul_nonneg (le_of_lt htp) (by positivity))]
  rw [Real.sqrt_mul (le_of_lt htp)]
  rw [hsqt]
  have hsqm' : Real.sqrt ((1-Real.log t)^m) = (1-Real.log t)^((m:ℝ)/2) := by
    simpa [L] using hsqm
  rw [hsqm']
  have hpow : L^q * L^((m:ℝ)/2 - q) = L^((m:ℝ)/2) := by
    rw [← Real.rpow_add hLpos]
    congr 1
    ring
  have hfactor : L^((m:ℝ)/2) * Real.sqrt a =
      L^q * (u * Real.sqrt a) := by
    dsimp [u]
    rw [← hpow]
    ac_rfl
  have hfactor' : (1-Real.log t)^((m:ℝ)/2) * Real.sqrt a =
      (1-Real.log t)^q * (u * Real.sqrt a) := by
    simpa [L] using hfactor
  calc
    _ = t^(p/2) * ((1-Real.log t)^((m:ℝ)/2) * Real.sqrt a) := by ac_rfl
    _ = t^(p/2) * ((1-Real.log t)^q * (u * Real.sqrt a)) :=
        congrArg (fun z : ℝ => t^(p/2) * z) hfactor'
    _ = _ := by simp [q, mul_assoc]

/-- Iterated logarithms grow no faster than an ordinary logarithmic
endpoint envelope. Real.log is total, so a = 0 is allowed. -/
theorem real_log_log_scaled_bound {t p a : ℝ} {m : ℕ}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    |Real.log (t^p * (1-Real.log t)^m * a)| ≤
      (|p| + m + |Real.log a|) * (1-Real.log t) := by
  let L : ℝ := 1 - Real.log t
  have hlogt : Real.log t ≤ 0 := Real.log_nonpos (le_of_lt ht) ht1
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogL : Real.log L ≤ L := by
    have h := Real.log_le_sub_one_of_pos hLpos
    dsimp [L] at h ⊢
    linarith
  have habslogt : |Real.log t| ≤ L := by
    rw [abs_of_nonpos hlogt]
    dsimp [L]
    linarith
  by_cases ha : a = 0
  · simpa [ha, Real.log_zero, L] using
      (show 0 ≤ (|p| + (m:ℝ) + |Real.log (0:ℝ)|) * (1 - Real.log t) by positivity)
  · have htPow : t^p ≠ 0 := (Real.rpow_pos_of_pos ht p).ne'
    have hLPow : L^m ≠ 0 := by positivity
    have hProd : t^p * L^m ≠ 0 := mul_ne_zero htPow hLPow
    have hlogeq : Real.log (t^p * L^m * a) =
        p * Real.log t + (m:ℝ) * Real.log L + Real.log a := by
      rw [show t^p * L^m * a = (t^p * L^m) * a by ring,
        Real.log_mul hProd ha, Real.log_mul htPow hLPow,
        Real.log_rpow ht p, Real.log_pow]
    rw [hlogeq]
    have h1 : |p * Real.log t| ≤ |p| * L := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left habslogt (abs_nonneg p)
    have h2 : |(m:ℝ) * Real.log L| ≤ (m:ℝ) * L := by
      rw [abs_of_nonneg (mul_nonneg (by positivity) hlogL0)]
      exact mul_le_mul_of_nonneg_left hlogL (by positivity)
    have h3 : |Real.log a| ≤ |Real.log a| * L := by
      calc
        |Real.log a| = |Real.log a| * 1 := by ring
        _ ≤ |Real.log a| * L := mul_le_mul_of_nonneg_left hL (abs_nonneg _)
    calc
      |p * Real.log t + (m:ℝ) * Real.log L + Real.log a| ≤
          |p * Real.log t| + |(m:ℝ) * Real.log L| + |Real.log a| := by
            calc
              _ ≤ |p * Real.log t + (m:ℝ) * Real.log L| + |Real.log a| := abs_add_le _ _
              _ ≤ _ := by linarith [abs_add_le (p * Real.log t) ((m:ℝ) * Real.log L)]
      _ ≤ (|p| + (m:ℝ) + |Real.log a|) * L := by nlinarith [h1, h2, h3]
      _ = (|p| + m + |Real.log a|) * (1 - Real.log t) := by simp [L, mul_comm]
/-- Uniform divided-difference bounds for a logarithm vanishing at an endpoint. -/
theorem real_log_one_sub_div_bounds {t d : ℝ} (ht : 0 < t) (htd : t ≤ d)
    (hd : d ≤ 1/2) :
    -1/(1-d) ≤ Real.log (1-t)/t ∧ Real.log (1-t)/t ≤ -1 := by
  have h1t : 0 < 1-t := by linarith
  have h1d : 0 < 1-d := by linarith
  have hInv : 0 < (1-t)⁻¹ := inv_pos.mpr h1t
  have hUpperLog := Real.log_le_sub_one_of_pos h1t
  have hLowerInv := Real.log_le_sub_one_of_pos hInv
  have hUpper : Real.log (1-t) ≤ -t := by linarith
  have hRatio : t/(1-t) ≤ t/(1-d) :=
    div_le_div_of_nonneg_left (le_of_lt ht) h1d (by linarith)
  have hInvSimpl : (1-t)⁻¹ - 1 = t/(1-t) := by field_simp; ring
  have hLower : -(t/(1-d)) ≤ Real.log (1-t) := by
    rw [Real.log_inv] at hLowerInv
    rw [hInvSimpl] at hLowerInv
    linarith
  constructor
  · apply (le_div_iff₀ ht).2
    calc
      (-1/(1-d)) * t = -(t/(1-d)) := by ring
      _ ≤ Real.log (1-t) := hLower
  · apply (div_le_iff₀ ht).2
    calc
      Real.log (1-t) ≤ -t := hUpper
      _ = -1 * t := by ring
end Intgrl
