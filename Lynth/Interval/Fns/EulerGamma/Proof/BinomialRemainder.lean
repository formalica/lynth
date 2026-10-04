import Lynth.Interval.Fns.EulerGamma.Proof.Coefficients

/-!
# Alternating remainder bound for the binomial series of `(1+u)^{-a}`
-/

open Real Set Finset

namespace BM

/-- `bc a l = (a)_l / l!`, the binomial coefficients of `(1-u)^{-a}`. -/
noncomputable def bc (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | l + 1 => bc a l * ((a + l) / (l + 1))

lemma bc_succ_mul (a : ℝ) (l : ℕ) : bc a (l + 1) * (l + 1) = a * bc (a + 1) l := by
  induction l with
  | zero => simp [bc]
  | succ l ih =>
    have h1 : bc a (l + 1 + 1) = bc a (l + 1) * ((a + (l + 1 : ℕ)) / ((l + 1 : ℕ) + 1)) := rfl
    have h2 : bc (a + 1) (l + 1) = bc (a + 1) l * ((a + 1 + l) / (l + 1)) := rfl
    rw [h1, h2]
    push_cast
    have hl : (l : ℝ) + 1 ≠ 0 := by positivity
    have hl2 : (l : ℝ) + 1 + 1 ≠ 0 := by positivity
    rw [← mul_assoc a, ← ih]
    field_simp
    ring

lemma bc_half (l : ℕ) : bc (1 / 2) l = cc l := by
  induction l with
  | zero => simp [bc, cc_zero]
  | succ l ih =>
    simp only [bc]; rw [ih, cc_succ]
    field_simp
    ring

/-- the remainder `R_{a,L}(u) = (1+u)^{-a} - Σ_{l<L} (-1)^l bc a l u^l` -/
noncomputable def binRem (a : ℝ) (L : ℕ) (u : ℝ) : ℝ :=
  (1 + u) ^ (-a) - ∑ l ∈ range L, (-1) ^ l * bc a l * u ^ l

lemma hasDerivAt_binRem (a : ℝ) (L : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    HasDerivAt (binRem a (L + 1)) (-a * binRem (a + 1) L u) u := by
  unfold binRem
  have h1 : HasDerivAt (fun u : ℝ => (1 + u) ^ (-a)) (-a * (1 + u) ^ (-a - 1)) u := by
    have := ((hasDerivAt_id u).const_add 1).rpow_const (p := -a) (Or.inl (by simp; linarith))
    simpa using this
  have h2 : HasDerivAt (fun u : ℝ => ∑ l ∈ range (L + 1), (-1) ^ l * bc a l * u ^ l)
      (∑ l ∈ range (L + 1), (-1) ^ l * bc a l * (l * u ^ (l - 1))) u := by
    apply HasDerivAt.fun_sum
    intro l _
    exact (hasDerivAt_pow l u).const_mul _
  convert h1.sub h2 using 1
  rw [Finset.sum_range_succ']
  simp only [CharP.cast_eq_zero, zero_mul, mul_zero, add_zero]
  rw [show -a - 1 = -(a + 1) by ring, mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  push_cast
  rw [pow_succ]
  have := bc_succ_mul a l
  linear_combination ((-1) ^ l * u ^ l) * this

lemma binRem_zero (a : ℝ) (L : ℕ) : binRem a (L + 1) 0 = 0 := by
  unfold binRem
  rw [Finset.sum_range_succ']
  simp [bc]

lemma continuous_binRem (a : ℝ) (L : ℕ) : ContinuousOn (binRem a L) (Ici 0) := by
  unfold binRem
  apply ContinuousOn.sub
  · apply ContinuousOn.rpow_const (continuousOn_const.add continuousOn_id)
    intro x hx; left; simp at hx ⊢; linarith
  · fun_prop

/-- Alternating remainder: `0 ≤ (-1)^L R_{a,L}(u) ≤ bc a L u^L` for `u ≥ 0`. -/
lemma binRem_bounds : ∀ (L : ℕ) (a : ℝ), 0 < a → ∀ u : ℝ, 0 ≤ u →
    0 ≤ (-1) ^ L * binRem a L u ∧ (-1) ^ L * binRem a L u ≤ bc a L * u ^ L := by
  intro L
  induction L with
  | zero =>
    intro a ha u hu
    simp only [pow_zero, one_mul, binRem, Finset.range_zero, Finset.sum_empty, sub_zero, bc]
    constructor
    · positivity
    · exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  | succ L ih =>
    intro a ha u hu
    have hih := ih (a + 1) (by linarith)
    -- monotonicity arguments on `[0, ∞)`
    have hderiv : ∀ v ∈ interior (Ici (0:ℝ)),
        HasDerivAt (fun v => (-1) ^ (L + 1) * binRem a (L + 1) v)
          (a * ((-1) ^ L * binRem (a + 1) L v)) v := by
      intro v hv
      rw [interior_Ici] at hv
      have := (hasDerivAt_binRem a L v (le_of_lt hv)).const_mul ((-1 : ℝ) ^ (L + 1))
      convert this using 1
      rw [pow_succ]; ring
    have hcont : ContinuousOn (fun v => (-1) ^ (L + 1) * binRem a (L + 1) v) (Ici 0) :=
      continuousOn_const.mul (continuous_binRem a (L + 1))
    constructor
    · have hmono : MonotoneOn (fun v => (-1) ^ (L + 1) * binRem a (L + 1) v) (Ici 0) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hcont
          (fun v hv => (hderiv v hv).hasDerivWithinAt)
        intro v hv
        rw [interior_Ici] at hv
        exact mul_nonneg ha.le (hih v (le_of_lt hv)).1
      have := hmono (self_mem_Ici) hu hu
      simpa [binRem_zero] using this
    · -- `g(v) = bc a (L+1) v^(L+1) - (-1)^(L+1) R(v)` is monotone, `g 0 = 0`
      have hmono : MonotoneOn
          (fun v => bc a (L + 1) * v ^ (L + 1) - (-1) ^ (L + 1) * binRem a (L + 1) v) (Ici 0) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
          ((Continuous.continuousOn (by fun_prop)).sub hcont)
          (fun v hv => (((hasDerivAt_pow (L + 1) v).const_mul (bc a (L + 1))).sub
            (hderiv v hv)).hasDerivWithinAt)
        intro v hv
        rw [interior_Ici] at hv
        have h2 := (hih v (le_of_lt hv)).2
        have h3 := bc_succ_mul a L
        push_cast
        have : bc a (L + 1) * ((L + 1) * v ^ L) = a * (bc (a + 1) L * v ^ L) := by
          rw [← mul_assoc, mul_comm (bc a (L + 1)), ← mul_assoc, mul_comm _ (bc a (L + 1)), h3]
        rw [this, ← mul_sub]
        exact mul_nonneg ha.le (by linarith)
      have := hmono (self_mem_Ici) hu hu
      simp [binRem_zero] at this
      linarith

lemma abs_binRem_le (a : ℝ) (ha : 0 < a) (L : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    |binRem a L u| ≤ bc a L * u ^ L := by
  obtain ⟨h1, h2⟩ := binRem_bounds L a ha u hu
  have : |binRem a L u| = (-1) ^ L * binRem a L u := by
    rcases neg_one_pow_eq_or ℝ L with h | h
    · rw [h, one_mul]; rw [h, one_mul] at h1; exact abs_of_nonneg h1
    · rw [h]; rw [h] at h1; rw [abs_of_nonpos (by linarith)]; ring
  rw [this]; exact h2

end BM
