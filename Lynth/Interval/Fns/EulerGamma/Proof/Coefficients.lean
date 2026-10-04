import Lynth.Interval.Fns.EulerGamma.Proof.Notation

/-!
# Coefficients `c_j`, half-integer Gamma values, and the Dixon-type identity
-/

open Real Finset Nat

namespace BM

lemma cc_pos (j : ℕ) : 0 < cc j := by
  unfold cc
  have : 0 < ((2 * j).choose j : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  positivity

lemma cc_zero : cc 0 = 1 := by simp [cc]

lemma cc_succ (j : ℕ) : cc (j + 1) = cc j * ((2 * j + 1) / (2 * j + 2)) := by
  unfold cc
  have h := Nat.succ_mul_centralBinom_succ j
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  have h' : ((j + 1 : ℕ) : ℝ) * ((2 * (j + 1)).choose (j + 1) : ℝ)
      = 2 * (2 * j + 1) * ((2 * j).choose j : ℝ) := by exact_mod_cast h
  push_cast at h'
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  rw [show ((2 * (j + 1)).choose (j + 1) : ℝ) = 2 * (2 * j + 1) * ((2 * j).choose j : ℝ) / (j + 1)
    by field_simp; linarith]
  rw [pow_succ]
  field_simp
  ring

lemma cc_le_one (j : ℕ) : cc j ≤ 1 := by
  induction j with
  | zero => simp [cc_zero]
  | succ j ih =>
    rw [cc_succ]
    have h1 : (2 * (j : ℝ) + 1) / (2 * j + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h0 : 0 ≤ (2 * (j : ℝ) + 1) / (2 * j + 2) := by positivity
    nlinarith [cc_pos j]

/-- `Γ(j + 1/2) = c_j · j! · √π`. -/
lemma Gamma_half (j : ℕ) : Real.Gamma (j + 1 / 2) = cc j * j ! * √π := by
  induction j with
  | zero => rw [Nat.cast_zero, zero_add, Real.Gamma_one_half_eq, cc_zero]; simp
  | succ j ih =>
    have : ((j + 1 : ℕ) : ℝ) + 1 / 2 = (j + 1 / 2) + 1 := by push_cast; ring
    rw [this, Real.Gamma_add_one (by positivity), ih, cc_succ, Nat.factorial_succ]
    push_cast
    field_simp

/-- `a_j = c_j² j!`, so that `Γ(j+1/2) c_j = √π a_j`. -/
noncomputable def aa (j : ℕ) : ℝ := cc j ^ 2 * j !

lemma aa_pos (j : ℕ) : 0 < aa j := by unfold aa; have := cc_pos j; positivity

lemma aa_succ (j : ℕ) : aa (j + 1) = aa j * ((2 * j + 1) ^ 2 / (4 * (j + 1))) := by
  unfold aa
  rw [cc_succ, Nat.factorial_succ]; push_cast
  field_simp
  ring

lemma pp_eq (n j : ℕ) : pp n j = √π * aa j / (n : ℝ) ^ j := by
  unfold pp aa; rw [Gamma_half]; ring

theorem pp_nonneg (n j : ℕ) : 0 ≤ pp n j := by
  rw [pp_eq]; have := aa_pos j; positivity

/-- The alternating convolution `T N = Σ_{j ≤ N} (-1)^j a_j a_{N-j}`. -/
noncomputable def TT (N : ℕ) : ℝ := ∑ j ∈ range (N + 1), (-1) ^ j * (aa j * aa (N - j))

/-- The (scaled) polynomial part `Ũ(j)` of the WZ certificate. -/
noncomputable def UU (n : ℝ) (j : ℝ) : ℝ :=
  j ^ 4 - (5 * n + 6) * j ^ 3 + (9 * n ^ 2 + 21 * n + 11) * j ^ 2
    - (28 * n ^ 3 + 96 * n ^ 2 + 97 * n + 28) / 4 * j
    + (32 * n ^ 4 + 144 * n ^ 3 + 212 * n ^ 2 + 120 * n + 23) / 16

/-- The certificate `G̃(n, j)`, for `j ≤ n`. -/
noncomputable def GG (n j : ℕ) : ℝ :=
  (-1) ^ j * aa j * aa (n - j) * j * UU n j / (((n - j : ℕ) : ℝ) + 1) / (((n - j : ℕ) : ℝ) + 2)

lemma wz_step (n j : ℕ) (hj : j < n) :
    (n + 2 : ℝ) * ((-1) ^ j * (aa j * aa (n + 2 - j)))
      - (n + 1 : ℝ) ^ 3 * ((-1) ^ j * (aa j * aa (n - j)))
      = GG n (j + 1) - GG n j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = j + m + 1 := ⟨n - j - 1, by omega⟩
  have e1 : j + m + 1 + 2 - j = m + 1 + 1 + 1 := by omega
  have e2 : j + m + 1 - j = m + 1 := by omega
  have e3 : j + m + 1 - (j + 1) = m := by omega
  unfold GG
  rw [e1, e2, e3, aa_succ (m + 1 + 1), aa_succ (m + 1), aa_succ m, aa_succ j, pow_succ]
  push_cast
  have := aa_pos j; have := aa_pos m
  unfold UU
  field_simp
  ring

lemma wz_last (n : ℕ) :
    (n + 2 : ℝ) * ((-1) ^ n * (aa n * aa (n + 2 - n)))
      - (n + 1 : ℝ) ^ 3 * ((-1) ^ n * (aa n * aa (n - n)))
      = -((n + 2 : ℝ) * ((-1) ^ (n + 1) * (aa (n + 1) * aa (n + 2 - (n + 1)))
          + (-1) ^ (n + 2) * (aa (n + 2) * aa (n + 2 - (n + 2))))) - GG n n := by
  have e1 : n + 2 - n = 0 + 1 + 1 := by omega
  have e2 : n + 2 - (n + 1) = 0 + 1 := by omega
  unfold GG
  simp only [e1, e2, Nat.sub_self]
  rw [aa_succ (0 + 1), aa_succ 0, aa_succ (n + 1), aa_succ n, pow_succ, pow_succ]
  push_cast
  have := aa_pos n
  unfold UU
  simp only [aa, cc_zero, Nat.factorial_zero]
  field_simp
  ring

/-- The Zeilberger recurrence `(N+2) T(N+2) = (N+1)³ T(N)`. -/
lemma TT_rec (n : ℕ) : (n + 2 : ℝ) * TT (n + 2) = (n + 1 : ℝ) ^ 3 * TT n := by
  unfold TT
  rw [show n + 2 + 1 = (n + 1) + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
  have hsum : ∑ j ∈ range (n + 1),
      ((n + 2 : ℝ) * ((-1) ^ j * (aa j * aa (n + 2 - j)))
        - (n + 1 : ℝ) ^ 3 * ((-1) ^ j * (aa j * aa (n - j))))
      = -((n + 2 : ℝ) * ((-1) ^ (n + 1) * (aa (n + 1) * aa (n + 2 - (n + 1)))
          + (-1) ^ (n + 2) * (aa (n + 2) * aa (n + 2 - (n + 2))))) - GG n 0 := by
    rw [Finset.sum_range_succ, wz_last]
    have : ∑ j ∈ range n, ((n + 2 : ℝ) * ((-1) ^ j * (aa j * aa (n + 2 - j)))
        - (n + 1 : ℝ) ^ 3 * ((-1) ^ j * (aa j * aa (n - j))))
        = ∑ j ∈ range n, (GG n (j + 1) - GG n j) :=
      Finset.sum_congr rfl (fun j hj => wz_step n j (Finset.mem_range.mp hj))
    rw [this, Finset.sum_range_sub]
    ring
  have hG0 : GG n 0 = 0 := by simp [GG]
  rw [hG0, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [mul_add, mul_add]
  linarith

lemma TT_zero : TT 0 = 1 := by simp [TT, aa, cc_zero]

lemma TT_one : TT 1 = 0 := by simp [TT, Finset.sum_range_succ]; ring

lemma TT_odd (k : ℕ) : TT (2 * k + 1) = 0 := by
  induction k with
  | zero => simpa using TT_one
  | succ k ih =>
    have h := TT_rec (2 * k + 1)
    rw [ih, mul_zero, show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring] at h
    have : (((2 * k + 1 : ℕ) : ℝ) + 2) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h).resolve_left this

lemma TT_even (k : ℕ) : TT (2 * k) = (2 * k) ! * cc k ^ 2 := by
  induction k with
  | zero => simp [TT_zero, cc_zero]
  | succ k ih =>
    have h := TT_rec (2 * k)
    rw [ih, show 2 * k + 2 = 2 * (k + 1) by ring] at h
    have hne : (((2 * k : ℕ) : ℝ) + 2) ≠ 0 := by positivity
    have : TT (2 * (k + 1)) = ((2 * k : ℕ) + 1 : ℝ) ^ 3 * ((2 * k) ! * cc k ^ 2)
        / (((2 * k : ℕ) : ℝ) + 2) := by
      rw [eq_div_iff hne]; linarith
    rw [this, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ, cc_succ]
    push_cast
    field_simp
    ring

end BM

namespace BM

lemma sum_range_two_mul (f : ℕ → ℝ) (M : ℕ) :
    ∑ N ∈ range (2 * M), f N = ∑ k ∈ range M, (f (2 * k) + f (2 * k + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

lemma cc_eq_factorial (k : ℕ) : cc k = (2 * k) ! / (4 ^ k * (k ! : ℝ) ^ 2) := by
  unfold cc
  have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
  rw [show 2 * k - k = k by omega] at h
  have h' : ((2 * k).choose k : ℝ) * k ! * k ! = (2 * k) ! := by exact_mod_cast h
  have hk : (k ! : ℝ) ≠ 0 := by positivity
  rw [← h']
  field_simp

lemma bmKterm_eq (m : ℕ) (k : ℕ) :
    bmKterm (m : ℝ) k = TT (2 * k) / ((4 * m : ℕ) : ℝ) ^ (2 * k) := by
  rw [TT_even, cc_eq_factorial, bmKterm]
  push_cast
  have hk : (k ! : ℝ) ≠ 0 := by positivity
  rw [show (16 * (m : ℝ)) ^ (2 * k) = 4 ^ (2 * k) * (4 * m) ^ (2 * k) by
    rw [← mul_pow]; congr 1; ring]
  rw [pow_mul (4:ℝ) 2 k, pow_mul (4 * (m:ℝ)) 2 k]
  field_simp
  ring_nf
  rw [show (4:ℝ) ^ (k * 2) = 16 ^ k by rw [mul_comm, pow_mul]; norm_num]

theorem bmK_eq (m : ℕ) (hm : 1 ≤ m) :
    bmK m = (1 / (4 * π * m)) * ∑ j ∈ range (4 * m), ∑ l ∈ range (4 * m - j),
      pp (4 * m) j * ((-1) ^ l * pp (4 * m) l) := by
  rw [← Finset.sum_range_diag_flip]
  have hinner : ∀ N : ℕ, ∑ k ∈ range (N + 1), pp (4 * m) k * ((-1) ^ (N - k) * pp (4 * m) (N - k))
      = π * ((-1) ^ N * TT N / ((4 * m : ℕ) : ℝ) ^ N) := by
    intro N
    unfold TT
    rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [pp_eq, pp_eq]
    have hsign : ((-1 : ℝ) ^ (N - k)) = (-1) ^ N * (-1) ^ k := by
      have : (-1 : ℝ) ^ N = (-1) ^ (N - k) * (-1) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hkN]
      rw [this, mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num
    rw [hsign]
    have hpow : ((4 * m : ℕ) : ℝ) ^ N = ((4 * m : ℕ) : ℝ) ^ k * ((4 * m : ℕ) : ℝ) ^ (N - k) := by
      rw [← pow_add, Nat.add_sub_cancel' hkN]
    rw [hpow]
    have hm' : ((4 * m : ℕ) : ℝ) ≠ 0 := by positivity
    have hpi : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
    conv_rhs => rw [← hpi]
    ring
  simp_rw [hinner]
  rw [← Finset.mul_sum, show 4 * m = 2 * (2 * m) by ring, sum_range_two_mul]
  unfold bmK
  rw [show 2 * (2 * m) = 4 * m by ring]
  simp_rw [TT_odd, bmKterm_eq]
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [mul_zero, zero_div, add_zero, pow_mul, neg_one_sq, one_pow, one_mul]
  field_simp

end BM
