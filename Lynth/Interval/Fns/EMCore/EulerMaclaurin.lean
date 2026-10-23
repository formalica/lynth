module

import Mathlib

/-!
# Euler–Maclaurin on a unit interval (complex-valued functions)

Shared infrastructure for the Stirling / Euler–Maclaurin handoffs.
-/

open Real intervalIntegral Nat

namespace EMCore

/-- The scaled, shifted Bernoulli function `B_m(x - a) / m!`, as a complex number. -/
noncomputable def bc (m : ℕ) (a x : ℝ) : ℂ := ((bernoulliFun m (x - a) / (m ! : ℝ) : ℝ) : ℂ)

lemma hasDerivAt_bc (m : ℕ) (a x : ℝ) : HasDerivAt (bc (m + 1) a) (bc m a x) x := by
  have h := ((hasDerivAt_bernoulliFun (m + 1) (x - a)).comp x
    ((hasDerivAt_id x).sub_const a)).div_const ((m + 1)! : ℝ)
  have h2 := h.ofReal_comp
  unfold bc
  simp only [Function.comp_apply, id_eq] at h2 ⊢
  convert h2 using 1
  simp only [mul_one, Nat.add_sub_cancel, Complex.ofReal_div, Nat.factorial_succ]
  push_cast
  field_simp

lemma continuous_bc (m : ℕ) (a : ℝ) : Continuous (bc m a) := by
  unfold bc; fun_prop

/-- `|B_{2k}(x)| ≤ |B_{2k}|` on `[0,1]`. -/
lemma abs_bernoulliFun_le {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * k) x| ≤ |(bernoulli (2 * k) : ℝ)| := by
  have h1 := hasSum_one_div_nat_pow_mul_cos hk hx
  have h0 := hasSum_one_div_nat_pow_mul_cos hk (x := 0) (by simp)
  simp only [mul_zero, Real.cos_zero, mul_one] at h0
  set c : ℝ := (-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k).factorial with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; have := pi_pos; positivity
  have e1 : bernoulliFun (2 * k) x
      = c⁻¹ * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * π * n * x) := by
    rw [h1.tsum_eq, bernoulliFun]; field_simp
  have e0 : (bernoulli (2 * k) : ℝ) = c⁻¹ * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k) := by
    rw [← bernoulliFun_eval_zero, h0.tsum_eq, bernoulliFun]; field_simp
  rw [e1, e0, abs_mul, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [abs_of_nonneg (a := ∑' n : ℕ, 1 / (n:ℝ)^(2*k)) (tsum_nonneg (fun n => by positivity)),
    ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm h1.summable.norm).trans ?_
  refine h1.summable.norm.tsum_le_tsum (fun n => ?_) h0.summable
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (n:ℝ) ^ (2*k))]
  exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one _)

lemma em_step (F : ℕ → ℝ → ℂ) (a : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hF : ∀ x ∈ Set.uIcc a (a + 1), HasDerivAt (F m) (F (m + 1) x) x)
    (hc : ContinuousOn (F (m + 1)) (Set.uIcc a (a + 1))) :
    ∫ x in a..a + 1, bc m a x * F m x
      = ((bernoulli (m + 1) : ℝ) / ((m + 1)! : ℝ) : ℝ) * (F m (a + 1) - F m a)
        - ∫ x in a..a + 1, bc (m + 1) a x * F (m + 1) x := by
  have := integral_mul_deriv_eq_deriv_mul (u := bc (m + 1) a) (u' := bc m a) (v := F m)
    (v' := F (m+1)) (fun x _ => hasDerivAt_bc m a x) hF
    ((continuous_bc m a).intervalIntegrable _ _) (hc.intervalIntegrable)
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq'] at this
  rw [this]
  have e1 : bc (m + 1) a (a + 1) = ((bernoulli (m + 1) : ℝ) / ((m + 1)! : ℝ) : ℝ) := by
    unfold bc; simp only [add_sub_cancel_left]
    rw [bernoulliFun_endpoints_eq_of_ne_one (by omega), bernoulliFun_eval_zero]
  have e0 : bc (m + 1) a a = ((bernoulli (m + 1) : ℝ) / ((m + 1)! : ℝ) : ℝ) := by
    unfold bc; simp only [sub_self]
    rw [bernoulliFun_eval_zero]
  rw [e1, e0]; ring

/-- Euler–Maclaurin remainder on `[a, a+1]` of order `p` (with the constant `B_p` subtracted). -/
noncomputable def emR (F : ℕ → ℝ → ℂ) (p : ℕ) (a : ℝ) : ℂ :=
  ∫ x in a..a + 1, (bc p a x - (((bernoulli p : ℝ) / (p ! : ℝ) : ℝ) : ℂ)) * F p x

/-- Hypothesis bundle: each `F (m+1)` is the derivative of `F m` on `[a, a+1]`. -/
def DerivChain (F : ℕ → ℝ → ℂ) (a : ℝ) : Prop :=
  ∀ m, ∀ x ∈ Set.uIcc a (a + 1), HasDerivAt (F m) (F (m + 1) x) x

lemma DerivChain.continuousOn {F : ℕ → ℝ → ℂ} {a : ℝ} (h : DerivChain F a) (m : ℕ) :
    ContinuousOn (F m) (Set.uIcc a (a + 1)) :=
  fun x hx => (h m x hx).continuousAt.continuousWithinAt

lemma DerivChain.integral_eq {F : ℕ → ℝ → ℂ} {a : ℝ} (h : DerivChain F a) (m : ℕ) :
    ∫ x in a..a + 1, F (m + 1) x = F m (a + 1) - F m a :=
  integral_eq_sub_of_hasDerivAt (h m) ((h.continuousOn (m + 1)).intervalIntegrable)

lemma emR_two {F : ℕ → ℝ → ℂ} {a : ℝ} (h : DerivChain F a) :
    ∫ x in a..a + 1, F 0 x = (F 0 a + F 0 (a + 1)) / 2 + emR F 2 a := by
  have h0 := integral_mul_deriv_eq_deriv_mul (u := bc 1 a) (u' := bc 0 a) (v := F 0)
    (v' := F 1) (fun x _ => hasDerivAt_bc 0 a x) (h 0)
    ((continuous_bc 0 a).intervalIntegrable _ _) ((h.continuousOn 1).intervalIntegrable)
  have h1 := em_step F a 1 le_rfl (h 1) (h.continuousOn 2)
  have hb0 : ∀ x, bc 0 a x = 1 := by intro x; simp [bc]
  simp only [hb0, one_mul] at h0
  have e1 : bc 1 a (a + 1) = 1 / 2 := by simp [bc, bernoulliFun_one]; norm_num
  have e0 : bc 1 a a = -1 / 2 := by simp [bc, bernoulliFun_one]; norm_num
  rw [e1, e0] at h0
  unfold emR
  have hsplit : ∫ x in a..a + 1, (bc 2 a x - (((bernoulli 2 : ℝ) / (2 ! : ℝ) : ℝ) : ℂ)) * F 2 x
      = (∫ x in a..a + 1, bc 2 a x * F 2 x)
        - (((bernoulli 2 : ℝ) / (2 ! : ℝ) : ℝ) : ℂ) * ∫ x in a..a + 1, F 2 x := by
    rw [← integral_const_mul, ← integral_sub]
    · congr 1; ext x; ring
    · exact ((continuous_bc 2 a).continuousOn.mul (h.continuousOn 2)).intervalIntegrable
    · exact (continuousOn_const.mul (h.continuousOn 2)).intervalIntegrable
  rw [hsplit, h.integral_eq 1]
  have h1' : ∫ x in a..a + 1, bc 1 a x * F 1 x
      = ((bernoulli 2 : ℝ) / ((2 : ℕ)! : ℝ) : ℝ) * (F 1 (a + 1) - F 1 a)
        - ∫ x in a..a + 1, bc 2 a x * F 2 x := h1
  linear_combination h0 - h1'

lemma emR_succ {F : ℕ → ℝ → ℂ} {a : ℝ} (h : DerivChain F a) (N : ℕ) (hN : 1 ≤ N) :
    emR F (2 * N) a = emR F (2 * N + 2) a
      - (((bernoulli (2 * N) : ℝ) / ((2 * N) ! : ℝ) : ℝ) : ℂ)
        * (F (2 * N - 1) (a + 1) - F (2 * N - 1) a) := by
  have split : ∀ p, emR F p a = (∫ x in a..a + 1, bc p a x * F p x)
      - (((bernoulli p : ℝ) / (p ! : ℝ) : ℝ) : ℂ) * ∫ x in a..a + 1, F p x := by
    intro p
    unfold emR
    rw [← integral_const_mul, ← integral_sub]
    · congr 1; ext x; ring
    · exact ((continuous_bc p a).continuousOn.mul (h.continuousOn p)).intervalIntegrable
    · exact (continuousOn_const.mul (h.continuousOn p)).intervalIntegrable
  have hp : 2 * N = (2 * N - 1) + 1 := by omega
  have s1 := em_step F a (2 * N) (by omega) (h _) (h.continuousOn _)
  have s2 := em_step F a (2 * N + 1) (by omega) (h _) (h.continuousOn _)
  have hodd : (bernoulli (2 * N + 1) : ℝ) = 0 := by
    rw [bernoulli_eq_zero_of_odd (by exact odd_two_mul_add_one N) (by omega)]; simp
  rw [hodd, zero_div] at s1
  rw [split (2 * N), split (2 * N + 2), s1, s2]
  have i1 : ∫ x in a..a + 1, F (2 * N) x = F (2 * N - 1) (a + 1) - F (2 * N - 1) a := by
    have := h.integral_eq (2 * N - 1); rwa [← hp] at this
  have i2 : ∫ x in a..a + 1, F (2 * N + 2) x = F (2 * N + 1) (a + 1) - F (2 * N + 1) a :=
    h.integral_eq (2 * N + 1)
  rw [i1, i2]
  push_cast
  ring

/-- Euler–Maclaurin on one unit interval, order `2N`. -/
lemma em_unit {F : ℕ → ℝ → ℂ} {a : ℝ} (h : DerivChain F a) (N : ℕ) (hN : 1 ≤ N) :
    ∫ x in a..a + 1, F 0 x = (F 0 a + F 0 (a + 1)) / 2
      - ∑ j ∈ Finset.range (N - 1), (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
          * (F (2 * j + 1) (a + 1) - F (2 * j + 1) a)
      + emR F (2 * N) a := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simpa using emR_two h
    · rw [ih hpos, emR_succ h N hpos]
      have : N + 1 - 1 = (N - 1) + 1 := by omega
      rw [this, Finset.sum_range_succ]
      have e : N - 1 + 1 = N := by omega
      have e2 : 2 * (N - 1) + 1 = 2 * N - 1 := by omega
      rw [e, e2, show 2 * (N + 1) = 2 * N + 2 by ring]
      ring

/-- Bound on the unit remainder. -/
lemma norm_emR_le {F : ℕ → ℝ → ℂ} {a : ℝ} (h : DerivChain F a) (N : ℕ) (hN : 1 ≤ N) :
    ‖emR F (2 * N) a‖
      ≤ 2 * |(bernoulli (2 * N) : ℝ)| / ((2 * N) ! : ℝ) * ∫ x in a..a + 1, ‖F (2 * N) x‖ := by
  unfold emR
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (by linarith) ?_ ?_
  · refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hx' : x - a ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hb := abs_bernoulliFun_le (k := N) (by omega) hx'
    unfold bc
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← sub_div, abs_div,
      abs_of_pos (by positivity : (0:ℝ) < ((2 * N) ! : ℝ))]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc |bernoulliFun (2 * N) (x - a) - (bernoulli (2 * N) : ℝ)|
        ≤ |bernoulliFun (2 * N) (x - a)| + |(bernoulli (2 * N) : ℝ)| := abs_sub _ _
      _ ≤ _ := by linarith
  · exact (continuousOn_const.mul (h.continuousOn _).norm).intervalIntegrable

/-- Global derivative chain on `[a, ∞)`. -/
def GChain (F : ℕ → ℝ → ℂ) (a : ℝ) : Prop :=
  ∀ m, ∀ x, a ≤ x → HasDerivAt (F m) (F (m + 1) x) x

lemma GChain.derivChain {F : ℕ → ℝ → ℂ} {a : ℝ} (h : GChain F a) {b : ℝ} (hb : a ≤ b) :
    DerivChain F b := by
  intro m x hx
  rw [Set.uIcc_of_le (by linarith)] at hx
  exact h m x (hb.trans hx.1)

/-- Euler–Maclaurin summation over `a, a+1, …, a+n-1`, order `2N`. -/
lemma em_sum {F : ℕ → ℝ → ℂ} {a : ℝ} (h : GChain F a) (N : ℕ) (hN : 1 ≤ N) (n : ℕ) :
    ∑ k ∈ Finset.range n, F 0 (a + k)
      = (∫ x in a..a + n, F 0 x) - (F 0 (a + n) - F 0 a) / 2
        + ∑ j ∈ Finset.range (N - 1),
            (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
              * (F (2 * j + 1) (a + n) - F (2 * j + 1) a)
        - ∑ k ∈ Finset.range n, emR F (2 * N) (a + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have hu := em_unit (h.derivChain (b := a + n) (by have := n.cast_nonneg (α := ℝ); linarith))
      N hN
    have hint : (∫ x in a..a + ((n + 1 : ℕ) : ℝ), F 0 x)
        = (∫ x in a..a + n, F 0 x) + ∫ x in a + n..a + n + 1, F 0 x := by
      rw [integral_add_adjacent_intervals]
      · push_cast; ring_nf
      · apply ContinuousOn.intervalIntegrable
        intro x hx
        rw [Set.uIcc_of_le (by have := n.cast_nonneg (α := ℝ); linarith)] at hx
        exact (h 0 x hx.1).continuousAt.continuousWithinAt
      · apply ContinuousOn.intervalIntegrable
        intro x hx
        rw [Set.uIcc_of_le (by linarith)] at hx
        exact (h 0 x (by have := n.cast_nonneg (α := ℝ); linarith [hx.1])).continuousAt.continuousWithinAt
    rw [hint, hu]
    have e : a + ((n + 1 : ℕ) : ℝ) = a + n + 1 := by push_cast; ring
    rw [e]
    have hs : ∀ j ∈ Finset.range (N - 1),
        (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
              * (F (2 * j + 1) (a + n + 1) - F (2 * j + 1) a)
        = (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
              * (F (2 * j + 1) (a + n) - F (2 * j + 1) a)
          + (((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)) ! : ℝ) : ℝ) : ℂ)
              * (F (2 * j + 1) (a + n + 1) - F (2 * j + 1) (a + n)) := by
      intro j _; ring
    rw [Finset.sum_congr rfl hs, Finset.sum_add_distrib]
    ring

/-- Telescoping summability/bound. -/
lemma summable_of_telescope {e : ℕ → ℂ} {h : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hh : ∀ k, 0 ≤ h k) (he : ∀ k, ‖e k‖ ≤ C * (h k - h (k + 1))) :
    Summable e ∧ ‖∑' k, e k‖ ≤ C * h 0 := by
  have hb : ∀ n, ∑ k ∈ Finset.range n, ‖e k‖ ≤ C * h 0 := by
    intro n
    calc ∑ k ∈ Finset.range n, ‖e k‖ ≤ ∑ k ∈ Finset.range n, C * (h k - h (k + 1)) :=
          Finset.sum_le_sum (fun k _ => he k)
      _ = C * (h 0 - h n) := by
          rw [← Finset.mul_sum, Finset.sum_range_sub']
      _ ≤ C * h 0 := by nlinarith [hh n]
  have hs : Summable (fun k => ‖e k‖) := summable_of_sum_range_le (fun _ => norm_nonneg _) hb
  exact ⟨hs.of_norm, (norm_tsum_le_tsum_norm hs).trans
    (Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _) hb)⟩

/-- `∫_k^{k+1} (x+r)^{-(q+1)} = h(k) - h(k+1)` with `h(y) = 1/(q (y+r)^q)`. -/
lemma integral_inv_pow_unit {r : ℝ} (hr : 0 < r) {k : ℝ} (hk : 0 ≤ k) {q : ℕ} (hq : 1 ≤ q) :
    ∫ x in k..k + 1, 1 / (x + r) ^ (q + 1)
      = 1 / (q * (k + r) ^ q) - 1 / (q * (k + 1 + r) ^ q) := by
  have hd : ∀ x ∈ Set.uIcc k (k + 1),
      HasDerivAt (fun y : ℝ => -(1 / (q * (y + r) ^ q))) (1 / (x + r) ^ (q + 1)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxr : 0 < x + r := by linarith [hx.1]
    have h1 : HasDerivAt (fun y : ℝ => y + r) 1 x := (hasDerivAt_id x).add_const r
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have h2 := ((h1.pow q).const_mul (q : ℝ)).inv (mul_ne_zero hq0 (pow_ne_zero _ hxr.ne'))
    have h3 := h2.neg
    convert h3 using 1
    · ext y; simp [one_div]
    · have : (x + r) ^ (q + 1) * (x + r) ^ (q - 1) = ((x + r) ^ q) ^ 2 := by
        rw [← pow_add, ← pow_mul]; congr 1; omega
      field_simp
      exact this.symm
  rw [integral_eq_sub_of_hasDerivAt hd]
  · ring
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hxr : 0 < x + r := by linarith [hx.1]
    exact ((continuousAt_const.div ((continuous_id.add continuous_const).pow _).continuousAt
      (pow_ne_zero _ hxr.ne'))).continuousWithinAt

end EMCore
