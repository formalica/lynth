import Mathlib

/-!
# Stirling expansion of `log Γ` with Bernoulli coefficients

General analytic result (independent of any coefficient table):
for `z > 0` and `N ≥ 1`,
`|log Γ(z) - [(z-1/2) log z - z + log √(2π) + Σ_{k=1}^{N-1} c_k / z^(2k-1)]| ≤ 2 |c_N| / z^(2N-1)`
with `c_k = B_{2k} / (2k (2k-1))`.
-/

open Real Filter Topology intervalIntegral

noncomputable section

namespace StirlingExpansion

/-- Bernoulli-based Stirling coefficient `B_{2k} / (2k (2k-1))`. -/
def bc (k : ℕ) : ℝ := (bernoulli (2 * k) : ℝ) / ((2 * (k : ℝ)) * (2 * (k : ℝ) - 1))

/-- `∫₀¹ B_m(t) / (x+t)^m dt`. -/
def J (m : ℕ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, bernoulliFun m t / (x + t) ^ m

/-- partial Stirling sum with `n` correction terms. -/
def P (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.range n, bc (k + 1) / x ^ (2 * k + 1)

/-- Stirling approximation with `n` correction terms. -/
def S (n : ℕ) (x : ℝ) : ℝ := (x - 1 / 2) * log x - x + log (sqrt (2 * π)) + P n x

/-- remainder of the Stirling approximation with `n` correction terms. -/
def E (n : ℕ) (x : ℝ) : ℝ := log (Gamma x) - S n x

lemma abs_bernoulliFun_le {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * k) x| ≤ |(bernoulli (2 * k) : ℝ)| := by
  have h1 := hasSum_one_div_nat_pow_mul_cos hk hx
  have h0 := hasSum_one_div_nat_pow_mul_cos hk (x := 0) (by simp)
  simp only [mul_zero, Real.cos_zero, mul_one] at h0
  set K : ℝ := (-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k).factorial
  have hK : K ≠ 0 := by
    simp only [K]; have := Real.pi_pos; positivity
  have e1 : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * k))).eval x =
      bernoulliFun (2 * k) x := rfl
  have e0 : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * k))).eval 0 =
      (bernoulli (2 * k) : ℝ) := bernoulliFun_eval_zero _
  rw [e1] at h1
  rw [e0] at h0
  have up : K * bernoulliFun (2 * k) x ≤ K * bernoulli (2 * k) :=
    hasSum_le (fun n => by
      have := Real.cos_le_one (2 * π * n * x)
      have : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * k) := by positivity
      nlinarith) h1 h0
  have lo : -(K * bernoulli (2 * k)) ≤ K * bernoulliFun (2 * k) x :=
    hasSum_le (fun n => by
      have := Real.neg_one_le_cos (2 * π * n * x)
      have : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * k) := by positivity
      show -(1 / (n : ℝ) ^ (2 * k)) ≤ _
      nlinarith) h0.neg h1
  have : |K * bernoulliFun (2 * k) x| ≤ |K * bernoulli (2 * k)| := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self (K * (bernoulli (2 * k) : ℝ))]
  rw [abs_mul, abs_mul] at this
  exact le_of_mul_le_mul_left this (abs_pos.mpr hK)

lemma J_succ {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 0 < x) :
    J m x = (bernoulli (m + 1) : ℝ) / (m + 1) * (1 / (x + 1) ^ m - 1 / x ^ m)
      + m / (m + 1) * J (m + 1) x := by
  have hpos : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < x + t := by
    intro t ht; rw [Set.uIcc_of_le zero_le_one] at ht; linarith [ht.1]
  have hu : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t => 1 / (x + t) ^ m)
      (-(m : ℝ) / (x + t) ^ (m + 1)) t := by
    intro t ht
    have h0 := hpos t ht
    have := (((hasDerivAt_id t).const_add x).pow m).inv (pow_ne_zero m h0.ne')
    convert this using 1
    · ext s; simp
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [id, Pi.pow_apply, mul_one, Nat.add_sub_cancel]
      field_simp
      ring
  have hv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t => bernoulliFun (m + 1) t / (m + 1))
      (bernoulliFun m t) t := fun t _ => by
    simpa using antideriv_bernoulliFun m t
  have hcont1 : ContinuousOn (fun t => -(m : ℝ) / (x + t) ^ (m + 1)) (Set.uIcc 0 1) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; exact (pow_pos (hpos t ht) _).ne'
  have key := integral_mul_deriv_eq_deriv_mul hu hv (hcont1.intervalIntegrable)
    ((continuous_bernoulliFun m).intervalIntegrable 0 1)
  have e1 : bernoulliFun (m + 1) 1 = bernoulli (m + 1) := by
    rw [bernoulliFun_endpoints_eq_of_ne_one (by omega), bernoulliFun_eval_zero]
  have e0 : bernoulliFun (m + 1) 0 = bernoulli (m + 1) := bernoulliFun_eval_zero _
  unfold J
  have lhs : (∫ t in (0 : ℝ)..1, bernoulliFun m t / (x + t) ^ m) =
      ∫ t in (0 : ℝ)..1, 1 / (x + t) ^ m * bernoulliFun m t := by
    congr 1; ext t; ring
  have rhs : (∫ t in (0 : ℝ)..1,
      -(m : ℝ) / (x + t) ^ (m + 1) * (bernoulliFun (m + 1) t / (m + 1))) =
      -(m / (m + 1)) * ∫ t in (0 : ℝ)..1, bernoulliFun (m + 1) t / (x + t) ^ (m + 1) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; ext t; field_simp
  rw [lhs, key, rhs, e1, e0]
  simp only [add_zero]
  ring

lemma integral_one_div_pow {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : 0 < x) :
    ∫ t in (0 : ℝ)..1, 1 / (x + t) ^ m = (1 / x ^ (m - 1) - 1 / (x + 1) ^ (m - 1)) / (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hpos : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < x + t := by
    intro t ht; rw [Set.uIcc_of_le zero_le_one] at ht; linarith [ht.1]
  have hF : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t => -(1 / ((k + 1 : ℝ) * (x + t) ^ (k + 1))))
      (1 / (x + t) ^ (k + 2)) t := by
    intro t ht
    have h0 := hpos t ht
    have h1 : (k + 1 : ℝ) * (x + t) ^ (k + 1) ≠ 0 := by positivity
    have := ((((hasDerivAt_id t).const_add x).pow (k + 1)).const_mul (k + 1 : ℝ)).inv
      (by simpa using h1)
    convert this.neg using 1
    · ext s; simp
    · simp only [id, mul_one, Nat.add_sub_cancel, Pi.pow_apply]
      push_cast
      field_simp
      ring
  have hcont : ContinuousOn (fun t => 1 / (x + t) ^ (k + 2)) (Set.uIcc 0 1) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; exact (pow_pos (hpos t ht) _).ne'
  rw [integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable]
  push_cast
  simp only [add_zero]
  have : (x + 1) ^ (k + 1) ≠ 0 := by positivity
  have : x ^ (k + 1) ≠ 0 := by positivity
  rw [show (k : ℝ) + 2 - 1 = k + 1 by ring]
  field_simp
  ring

lemma abs_J_le {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 < x) :
    |J (2 * N) x| ≤ |(bernoulli (2 * N) : ℝ)| *
      ((1 / x ^ (2 * N - 1) - 1 / (x + 1) ^ (2 * N - 1)) / (2 * N - 1)) := by
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < x + t := by
    intro t ht; linarith [ht.1]
  have hc : ContinuousOn (fun t => 1 / (x + t) ^ (2 * N)) (Set.Icc 0 1) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; exact (pow_pos (hpos t ht) _).ne'
  have hc2 : ContinuousOn (fun t => bernoulliFun (2 * N) t / (x + t) ^ (2 * N))
      (Set.Icc 0 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht; exact (pow_pos (hpos t ht) _).ne'
  unfold J
  refine (abs_integral_le_integral_abs zero_le_one).trans ?_
  have := integral_one_div_pow (m := 2 * N) (by omega) hx
  push_cast at this
  rw [← this, ← integral_const_mul]
  apply integral_mono_on zero_le_one
  · exact (hc2.abs).intervalIntegrable_of_Icc zero_le_one
  · exact (continuousOn_const.mul hc).intervalIntegrable_of_Icc zero_le_one
  · intro t ht
    have h1 := abs_bernoulliFun_le (k := N) (by omega) ht
    have h2 : 0 < (x + t) ^ (2 * N) := pow_pos (hpos t ht) _
    rw [abs_div, abs_of_pos h2, mul_one_div]
    exact div_le_div_of_nonneg_right h1 h2.le

lemma diff_S_zero {x : ℝ} (hx : 0 < x) : -log x + S 0 (x + 1) - S 0 x = -J 1 x := by
  have hpos : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < x + t := by
    intro t ht; rw [Set.uIcc_of_le zero_le_one] at ht; linarith [ht.1]
  have hF : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t => t - (x + 1 / 2) * log (x + t))
      (bernoulliFun 1 t / (x + t) ^ 1) t := by
    intro t ht
    have h0 := hpos t ht
    have := (hasDerivAt_id' t).sub
      ((((hasDerivAt_id' t).const_add x).log h0.ne').const_mul (x + 1 / 2))
    refine this.congr_deriv ?_
    simp only [bernoulliFun_one, pow_one]
    field_simp
    ring
  have hcont : ContinuousOn (fun t => bernoulliFun 1 t / (x + t) ^ 1) (Set.uIcc 0 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht; exact (pow_pos (hpos t ht) _).ne'
  unfold J
  rw [integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable]
  simp only [S, P, Finset.range_zero, Finset.sum_empty, add_zero]
  ring

lemma diff_S {x : ℝ} (hx : 0 < x) (n : ℕ) :
    -log x + S n (x + 1) - S n x = -J (2 * n + 1) x / (2 * n + 1) := by
  induction n with
  | zero => simpa using diff_S_zero hx
  | succ n ih =>
    have hS : ∀ y, S (n + 1) y = S n y + bc (n + 1) / y ^ (2 * n + 1) := by
      intro y; simp only [S, P, Finset.sum_range_succ]; ring
    have h1 := J_succ (m := 2 * n + 1) (by omega) hx
    have h2 := J_succ (m := 2 * n + 2) (by omega) hx
    rw [show 2 * n + 2 + 1 = 2 * n + 3 by ring,
      bernoulli_eq_zero_of_odd ⟨n + 1, by ring⟩ (by omega)] at h2
    rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring] at h1
    simp only [Rat.cast_zero, zero_div, zero_mul, zero_add] at h2
    rw [hS, hS, show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
    have e : -log x + (S n (x + 1) + bc (n + 1) / (x + 1) ^ (2 * n + 1)) -
        (S n x + bc (n + 1) / x ^ (2 * n + 1)) = (-log x + S n (x + 1) - S n x) +
        bc (n + 1) * (1 / (x + 1) ^ (2 * n + 1) - 1 / x ^ (2 * n + 1)) := by ring
    rw [e, ih, h1, h2]
    simp only [bc]
    push_cast
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]
    generalize (1 / (x + 1) ^ (2 * n + 1) - 1 / x ^ (2 * n + 1)) = a
    generalize J (2 * n + 3) x = j
    generalize ((bernoulli (2 * n + 2) : ℚ) : ℝ) = b
    rw [show (2 * ((n : ℝ) + 1) - 1) = 2 * n + 1 by ring,
      show (2 * ((n : ℝ) + 1)) = 2 * n + 2 by ring,
      show (2 * (n : ℝ) + 1 + 1) = 2 * n + 2 by ring,
      show (2 * (n : ℝ) + 2 + 1) = 2 * n + 3 by ring]
    have : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
    have : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring

lemma E_sub_E_succ {x : ℝ} (hx : 0 < x) (n : ℕ) :
    E n x - E n (x + 1) = -log x + S n (x + 1) - S n x := by
  unfold E
  rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  ring

lemma abs_E_diff_le {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 < x) :
    |E (N - 1) x - E (N - 1) (x + 1)| ≤
      2 * |bc N| * (1 / x ^ (2 * N - 1) - 1 / (x + 1) ^ (2 * N - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [E_sub_E_succ hx, diff_S hx, J_succ (m := 2 * n + 1) (by omega) hx]
  have hJ := abs_J_le (N := n + 1) (by omega) hx
  have hbc : |bc (n + 1)| =
      |(bernoulli (2 * n + 2) : ℝ)| / ((2 * n + 2) * (2 * n + 1)) := by
    simp only [bc]
    rw [abs_div, abs_of_pos
      (show (0 : ℝ) < 2 * (↑(n + 1) : ℝ) * (2 * ↑(n + 1) - 1) by push_cast; nlinarith)]
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]
    push_cast; ring_nf
  rw [hbc]
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, show 2 * (n + 1) = 2 * n + 2 by ring] at *
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring]
  have ha : 0 ≤ 1 / x ^ (2 * n + 1) - 1 / (x + 1) ^ (2 * n + 1) := by
    rw [sub_nonneg]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ hx.le (by linarith) _
  have e : 1 / (x + 1) ^ (2 * n + 1) - 1 / x ^ (2 * n + 1) =
      -(1 / x ^ (2 * n + 1) - 1 / (x + 1) ^ (2 * n + 1)) := by ring
  rw [e]
  generalize 1 / x ^ (2 * n + 1) - 1 / (x + 1) ^ (2 * n + 1) = a at *
  generalize J (2 * n + 2) x = j at *
  generalize ((bernoulli (2 * n + 2) : ℚ) : ℝ) = b at *
  push_cast at *
  rw [show (2 * ((n : ℝ) + 1) - 1) = 2 * n + 1 by ring] at hJ
  have h1 : (0 : ℝ) < 2 * n + 1 := by positivity
  have h2 : (0 : ℝ) < 2 * n + 2 := by positivity
  have eq : -(b / (2 * n + 1 + 1) * -a + (2 * n + 1) / (2 * n + 1 + 1) * j) / (2 * n + 1)
      = b * a / ((2 * n + 2) * (2 * n + 1)) - j / (2 * n + 2) := by
    field_simp; ring
  rw [eq]
  refine (abs_sub _ _).trans ?_
  rw [abs_div, abs_div, abs_mul, abs_of_nonneg ha, abs_of_pos h2,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * n + 2) * (2 * n + 1))]
  have : |j| / (2 * n + 2) ≤ |b| * (a / (2 * n + 1)) / (2 * n + 2) :=
    div_le_div_of_nonneg_right hJ h2.le
  have e2 : |b| * (a / (2 * n + 1)) / (2 * n + 2) = |b| * a / ((2 * n + 2) * (2 * n + 1)) := by
    field_simp
  have e3 : 2 * (|b| / ((2 * ↑n + 2) * (2 * ↑n + 1))) * a =
      2 * (|b| * a / ((2 * n + 2) * (2 * n + 1))) := by ring
  linarith

lemma tendsto_E_zero_nat : Tendsto (fun n : ℕ => E 0 n) atTop (𝓝 0) := by
  have h := (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).sub_const
    ((1 / 2) * log π)
  rw [Real.log_sqrt Real.pi_pos.le, show log π / 2 - 1 / 2 * log π = 0 by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Stirling.log_stirlingSeq_formula]
  simp only [E, S, P, Finset.range_zero, Finset.sum_empty, add_zero]
  push_cast
  rw [Real.Gamma_nat_eq_factorial, Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity) (by positivity)]
  have hm : (0 : ℝ) < m + 1 := by positivity
  rw [Real.log_mul (by norm_num) hm.ne', Real.log_div hm.ne' (by positivity), Real.log_exp,
    Real.log_sqrt (by positivity), Real.log_mul (by norm_num) Real.pi_pos.ne']
  push_cast
  ring

lemma tendsto_E_zero_nat_add {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Tendsto (fun n : ℕ => E 0 (n + x)) atTop (𝓝 0) := by
  have hE := tendsto_E_zero_nat
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog0 : Tendsto (fun n : ℕ => log (1 + x / n)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => 1 + x / (n : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat x).const_add 1
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp this
    rw [Real.log_one] at h
    exact h
  have hC : Tendsto (fun n : ℕ => (n + x - 1 / 2) * log (1 + x / n)) atTop (𝓝 x) := by
    have h1 := (tendsto_mul_log_one_add_div_atTop x).comp hnat
    have h2 := hlog0.const_mul (x - 1 / 2)
    have := h1.add h2
    simp only [mul_zero, add_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp]; ring
  set f : ℝ → ℝ := log ∘ Gamma
  have hconv : ConvexOn ℝ (Set.Ioi 0) f := convexOn_log_Gamma
  have hfeq : ∀ {y : ℝ}, 0 < y → f (y + 1) = f y + log y := by
    intro y hy
    simp only [f, Function.comp, Real.Gamma_add_one hy.ne']
    rw [Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']; ring
  have hA : Tendsto (fun n : ℕ => f (n + x) - f n - x * log n) atTop (𝓝 0) := by
    have hlow : Tendsto (fun n : ℕ => -(2 * x / n)) atTop (𝓝 0) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (2 * x)).neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have h1 := Real.BohrMollerup.f_add_nat_ge hconv hfeq hn hx
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hl : log n - log (n - 1) ≤ 1 / (n - 1) := by
        rw [← Real.log_div (by linarith) (by linarith)]
        have := Real.log_le_sub_one_of_pos (show 0 < (n : ℝ) / (n - 1) by
          apply div_pos <;> linarith)
        have : (n : ℝ) - 1 ≠ 0 := by linarith
        have e : (n : ℝ) / (n - 1) - 1 = 1 / (n - 1) := by field_simp; ring
        linarith
      have h3 : 1 / ((n : ℝ) - 1) ≤ 2 / n := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
      have : x * (log n - log (n - 1)) ≤ 2 * x / n := by
        calc x * (log n - log (n - 1)) ≤ x * (2 / n) :=
              mul_le_mul_of_nonneg_left (hl.trans h3) hx.le
          _ = 2 * x / n := by ring
      nlinarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have h1 := Real.BohrMollerup.f_add_nat_le hconv hfeq (by omega : n ≠ 0) hx hx1
      linarith
  have := ((hE.add hA).sub hC).add_const x
  simp only [add_zero, zero_sub, neg_add_cancel] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : log (1 + x / n) = log (n + x) - log n := by
    rw [← Real.log_div (by positivity) hn'.ne']; congr 1; field_simp
  rw [e]
  simp only [E, S, P, Finset.range_zero, Finset.sum_empty, add_zero, f, Function.comp]
  ring

lemma tendsto_E_add_nat (n : ℕ) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun M : ℕ => E n (z + M)) atTop (𝓝 0) := by
  have hzM : Tendsto (fun M : ℕ => z + (M : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hP : Tendsto (fun M : ℕ => P n (z + M)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range n) (fun k _ =>
      (tendsto_const_nhds (x := bc (k + 1))).div_atTop
        ((tendsto_pow_atTop (by omega : 2 * k + 1 ≠ 0)).comp hzM))
    simpa [P] using this
  set m : ℕ := ⌈z⌉₊ - 1
  have hc1 : 1 ≤ ⌈z⌉₊ := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hm : (m : ℝ) = ⌈z⌉₊ - 1 := by simp [m, Nat.cast_sub hc1]
  have hx0 : 0 < z - m := by rw [hm]; linarith [Nat.ceil_lt_add_one hz.le]
  have hx1 : z - m ≤ 1 := by rw [hm]; linarith [Nat.le_ceil z]
  have h0 := (tendsto_E_zero_nat_add hx0 hx1).comp (tendsto_add_atTop_nat m)
  have := h0.sub hP
  rw [sub_zero] at this
  refine this.congr fun M => ?_
  simp only [Function.comp, E, S, P, Finset.range_zero, Finset.sum_empty, add_zero]
  push_cast
  ring_nf

/-- Stirling expansion of `log Γ` with explicit remainder, Bernoulli form. -/
theorem abs_E_le {N : ℕ} (hN : 1 ≤ N) {z : ℝ} (hz : 0 < z) :
    |E (N - 1) z| ≤ 2 * |bc N| / z ^ (2 * N - 1) := by
  set g : ℝ → ℝ := fun y => 1 / y ^ (2 * N - 1)
  have key : ∀ M : ℕ, |E (N - 1) z| ≤ |E (N - 1) (z + M)| + 2 * |bc N| * g z := by
    intro M
    have tel := Finset.sum_range_sub' (fun j : ℕ => E (N - 1) (z + j)) M
    have tel2 := Finset.sum_range_sub' (fun j : ℕ => g (z + j)) M
    simp only [Nat.cast_zero, add_zero] at tel tel2
    have hb : |∑ j ∈ Finset.range M, (E (N - 1) (z + j) - E (N - 1) (z + (j + 1 : ℕ)))| ≤
        ∑ j ∈ Finset.range M, 2 * |bc N| * (g (z + j) - g (z + (j + 1 : ℕ))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      have := abs_E_diff_le hN (x := z + j) (by positivity)
      push_cast at this ⊢
      rw [show z + (j + 1 : ℝ) = z + j + 1 by ring]
      exact this
    rw [← Finset.mul_sum, tel2, tel] at hb
    have hg : 0 ≤ g (z + M) := by simp only [g]; positivity
    have := abs_sub_abs_le_abs_sub (E (N - 1) z) (E (N - 1) (z + M))
    nlinarith [abs_nonneg (bc N)]
  have h0 : Tendsto (fun M : ℕ => |E (N - 1) (z + M)|) atTop (𝓝 0) := by
    simpa using (tendsto_E_add_nat (N - 1) hz).abs
  have hlim := h0.add_const (2 * |bc N| * g z)
  have := ge_of_tendsto' hlim key
  rw [zero_add] at this
  simp only [g, mul_one_div] at this
  exact this

end StirlingExpansion

