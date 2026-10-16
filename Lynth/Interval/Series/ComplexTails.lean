import Mathlib

/-!
# Complex series tails: telescoping identities and geometric majorants.

Pure analysis over `ℂ` (no Lynth dependency). Consumed by the complex
series certificates (`ComplexCert.lean`), mirroring the real
telescoping/geometric tail arguments behind `SeriesSummabilityResult`.

Every bound is norm-based, so signs and arguments never matter. All
proofs are inline from Mathlib facts.
-/

namespace Lynth.Interval.Series

open BigOperators Filter Topology Nat

/-- geometric tail assembler: a real geometric majorant of the shifted terms
gives summability and a norm bound on the tail sum. -/
theorem Complex_geometric_tail {f : ℕ → ℂ} {M R : ℝ} (hM : 0 ≤ M) (hR0 : 0 ≤ R)
    (hR1 : R < 1) (N : ℕ) (h : ∀ j, ‖f (j + N)‖ ≤ M * R ^ j) :
    Summable (fun j => f (j + N)) ∧ ‖∑' j, f (j + N)‖ ≤ M / (1 - R) := by
  have hgs : Summable (fun j : ℕ => M * R ^ j) :=
    (summable_geometric_of_lt_one hR0 hR1).mul_left _
  have hs : Summable (fun j => f (j + N)) := Summable.of_norm_bounded hgs h
  refine ⟨hs, ?_⟩
  have h2 : ∑' j, ‖f (j + N)‖ ≤ ∑' _j : ℕ, M * R ^ _j :=
    hs.norm.tsum_le_tsum h hgs
  rw [tsum_mul_left, tsum_geometric_of_lt_one hR0 hR1] at h2
  calc ‖∑' j, f (j + N)‖ ≤ ∑' j, ‖f (j + N)‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ M * (1 - R)⁻¹ := h2
    _ = M / (1 - R) := by rw [div_eq_mul_inv]

/-- exact tail of `c / ((w + j) * (w + j + 1))` with `1 ≤ Re w`:
partial fractions telescope. -/
theorem Complex_tsum_telescoping {c w : ℂ} (hw : 1 ≤ w.re) :
    Summable (fun j => c / ((w + ((j : ℕ) : ℂ)) * (w + ((j : ℕ) : ℂ) + 1))) ∧
    (∑' j, c / ((w + ((j : ℕ) : ℂ)) * (w + ((j : ℕ) : ℂ) + 1))) = c / w := by
  have hpos : ∀ j : ℕ, 0 < w.re + (j : ℝ) := fun j => by
    have hnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hne : ∀ j : ℕ, (w + ((j : ℕ) : ℂ)) ≠ 0 ∧ (w + ((j : ℕ) : ℂ) + 1) ≠ 0 := by
    intro j
    have e1 : (w + ((j : ℕ) : ℂ)).re = w.re + (j : ℝ) := by
      simp only [Complex.add_re, Complex.natCast_re]
    have e2 : (w + ((j : ℕ) : ℂ) + 1).re = w.re + (j : ℝ) + 1 := by
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    constructor
    · intro h
      have hr := congrArg Complex.re h
      simp only [Complex.zero_re] at hr
      rw [e1] at hr
      linarith [hpos j]
    · intro h
      have hr := congrArg Complex.re h
      simp only [Complex.zero_re] at hr
      rw [e2] at hr
      have hnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
  have hpf : ∀ j : ℕ, c / ((w + ((j : ℕ) : ℂ)) * (w + ((j : ℕ) : ℂ) + 1))
      = c / (w + ((j : ℕ) : ℂ)) - c / (w + ((j : ℕ) : ℂ) + 1) := by
    intro j
    obtain ⟨h1, h2⟩ := hne j
    field_simp
    ring
  -- summability via a real `1/j²` majorant
  have hbase : Summable (fun n : ℕ => ‖c‖ * (1 / ((n : ℝ) ^ 2))) :=
    (Real.summable_one_div_nat_pow.2 (by omega)).mul_left _
  have hshift : Summable (fun j : ℕ => ‖c‖ * (1 / ((((j : ℝ)) + 1) ^ 2))) := by
    have h2 := (summable_nat_add_iff
      (f := fun n : ℕ => ‖c‖ * (1 / ((n : ℝ) ^ 2))) 1).2 hbase
    refine h2.congr (fun j => ?_)
    simp only [Nat.cast_add, Nat.cast_one]
  have hmaj : ∀ j : ℕ,
      ‖c / ((w + ((j : ℕ) : ℂ)) * (w + ((j : ℕ) : ℂ) + 1))‖
        ≤ ‖c‖ * (1 / ((((j : ℝ)) + 1) ^ 2)) := by
    intro j
    have hnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have h1p : (0 : ℝ) < (j : ℝ) + 1 := by linarith
    have g1 : (j : ℝ) + 1 ≤ ‖w + ((j : ℕ) : ℂ)‖ := by
      have h := Complex.re_le_norm (w + ((j : ℕ) : ℂ))
      simp only [Complex.add_re, Complex.natCast_re] at h
      linarith [hw]
    have g2 : (j : ℝ) + 1 ≤ ‖w + ((j : ℕ) : ℂ) + 1‖ := by
      have h := Complex.re_le_norm (w + ((j : ℕ) : ℂ) + 1)
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re] at h
      have hw0 : (0 : ℝ) ≤ w.re := by linarith [hw]
      linarith
    have hden : ((j : ℝ) + 1) ^ 2 ≤ ‖w + ((j : ℕ) : ℂ)‖ * ‖w + ((j : ℕ) : ℂ) + 1‖ := by
      calc (((j : ℝ) + 1) ^ 2) = ((j : ℝ) + 1) * ((j : ℝ) + 1) := by ring
        _ ≤ _ := mul_le_mul g1 g2 (by positivity) (by positivity)
    rw [norm_div, norm_mul, ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos h1p 2) hden
  have hs : Summable (fun j => c / ((w + ((j : ℕ) : ℂ)) * (w + ((j : ℕ) : ℂ) + 1))) := by
    apply Summable.of_norm_bounded
      (g := fun (j : ℕ) => ‖c‖ * (1 / ((((j : ℝ)) + 1) ^ 2)))
    · exact hshift
    · intro j
      exact hmaj j
  refine ⟨hs, ?_⟩
  -- value via partial sums
  have hsum : ∀ J, ∑ j ∈ Finset.range J,
      (c / ((w + ((j : ℕ) : ℂ)) * (w + ((j : ℕ) : ℂ) + 1)))
      = c / w - c / (w + (((J : ℕ)) : ℂ)) := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.sum_range_succ, ih, hpf J]
      have e : w + ((((J + 1 : ℕ))) : ℂ) = w + ((J : ℕ) : ℂ) + 1 := by
        push_cast
        ring
      rw [e]
      ring
  have hvan : Tendsto (fun J => c / (w + (((J : ℕ)) : ℂ))) atTop (𝓝 0) := by
    have hmaj2 : ∀ J : ℕ, ‖c / (w + (((J : ℕ)) : ℂ))‖ ≤ ‖c‖ * (1 / (((J : ℝ)) + 1)) := by
      intro J
      have h1p : (0 : ℝ) < (J : ℝ) + 1 := by
        have hnn : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
        linarith
      have g1 : (J : ℝ) + 1 ≤ ‖w + ((J : ℕ) : ℂ)‖ := by
        have h := Complex.re_le_norm (w + ((J : ℕ) : ℂ))
        simp only [Complex.add_re, Complex.natCast_re] at h
        linarith [hw]
      calc ‖c / (w + ((J : ℕ) : ℂ))‖ = ‖c‖ / ‖w + ((J : ℕ) : ℂ)‖ := by rw [norm_div]
        _ ≤ ‖c‖ / ((J : ℝ) + 1) :=
          div_le_div_of_nonneg_left (norm_nonneg _) h1p g1
        _ = ‖c‖ * (1 / ((J : ℝ) + 1)) := by rw [div_eq_mul_one_div]
    have hlim : Tendsto (fun J : ℕ => ‖c‖ * (1 / (((J : ℝ)) + 1))) atTop (𝓝 0) := by
      have h1 := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ‖c‖
      rwa [mul_zero] at h1
    exact squeeze_zero_norm hmaj2 hlim
  have hlim2 : Tendsto (fun J => ∑ j ∈ Finset.range J,
      (c / ((w + ((j : ℕ) : ℂ)) * (w + ((j : ℕ) : ℂ) + 1)))) atTop (𝓝 (c / w)) := by
    have h2 := tendsto_const_nhds (x := c / w) |>.sub hvan
    rw [sub_zero] at h2
    refine h2.congr (fun J => ?_)
    rw [hsum J]
  have h3 := hs.hasSum.tendsto_sum_nat
  rw [tendsto_nhds_unique h3 hlim2]

/-- exact tail of `c / ((2 * (w + j) + a) * (2 * (w + j) + a + 2))`:
step-2 partial fractions telescope. Covers `1 / (4k² - 1)`-type series. -/
theorem Complex_tsum_telescoping_step2 {c w a : ℂ} (hw : 0 ≤ w.re) (ha : 1 ≤ a.re) :
    Summable (fun j => c / ((2 * (w + ((j : ℕ) : ℂ)) + a)
        * (2 * (w + ((j : ℕ) : ℂ)) + a + 2))) ∧
    (∑' j, c / ((2 * (w + ((j : ℕ) : ℂ)) + a)
        * (2 * (w + ((j : ℕ) : ℂ)) + a + 2)))
      = (c / 2) * (1 / (2 * w + a)) := by
  have hne1 : ∀ j : ℕ, (2 * (w + ((j : ℕ) : ℂ)) + a) ≠ 0 := by
    intro j
    have e : (2 * (w + ((j : ℕ) : ℂ)) + a).re
        = 2 * w.re + 2 * (j : ℝ) + a.re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re,
        Complex.I_re, Complex.re_ofNat, Complex.im_ofNat, mul_zero, mul_one, zero_mul, one_mul,
        sub_zero]; ring
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.zero_re] at hr
    rw [e] at hr
    have hnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith [hw, ha]
  have hne2 : ∀ j : ℕ, (2 * (w + ((j : ℕ) : ℂ)) + a + 2) ≠ 0 := by
    intro j
    have e : (2 * (w + ((j : ℕ) : ℂ)) + a + 2).re
        = 2 * w.re + 2 * (j : ℝ) + a.re + 2 := by
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.one_re,
        Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, mul_zero, mul_one, zero_mul, one_mul,
        sub_zero]; ring
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.zero_re] at hr
    rw [e] at hr
    have hnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith [hw, ha]
  have hpf : ∀ j : ℕ, c / ((2 * (w + ((j : ℕ) : ℂ)) + a)
        * (2 * (w + ((j : ℕ) : ℂ)) + a + 2))
      = (c / 2) * (1 / (2 * (w + ((j : ℕ) : ℂ)) + a)
        - 1 / (2 * (w + ((j : ℕ) : ℂ)) + a + 2)) := by
    intro j
    have h1 := hne1 j
    have h2 := hne2 j
    field_simp
    ring
  have hbase : Summable (fun n : ℕ => ‖c‖ * (1 / ((n : ℝ) ^ 2))) :=
    (Real.summable_one_div_nat_pow.2 (by omega)).mul_left _
  have hshift : Summable (fun j : ℕ => ‖c‖ * (1 / ((((j : ℝ)) + 1) ^ 2))) := by
    have h2 := (summable_nat_add_iff
      (f := fun n : ℕ => ‖c‖ * (1 / ((n : ℝ) ^ 2))) 1).2 hbase
    refine h2.congr (fun j => ?_)
    simp only [Nat.cast_add, Nat.cast_one]
  have hmaj : ∀ j : ℕ,
      ‖c / ((2 * (w + ((j : ℕ) : ℂ)) + a)
        * (2 * (w + ((j : ℕ) : ℂ)) + a + 2))‖
        ≤ ‖c‖ * (1 / ((((j : ℝ)) + 1) ^ 2)) := by
    intro j
    have hnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have ha0 : (0 : ℝ) ≤ a.re := by linarith [ha]
    have h1p : (0 : ℝ) < (j : ℝ) + 1 := by linarith
    have g1 : (j : ℝ) + 1 ≤ ‖2 * (w + ((j : ℕ) : ℂ)) + a‖ := by
      have h := Complex.re_le_norm (2 * (w + ((j : ℕ) : ℂ)) + a)
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.one_re,
        Complex.I_re, Complex.re_ofNat, Complex.im_ofNat, mul_zero, mul_one, zero_mul, one_mul,
        sub_zero] at h
      linarith [hw]
    have g2 : (j : ℝ) + 1 ≤ ‖2 * (w + ((j : ℕ) : ℂ)) + a + 2‖ := by
      have h := Complex.re_le_norm (2 * (w + ((j : ℕ) : ℂ)) + a + 2)
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.one_re,
        Complex.re_ofNat, Complex.I_re, Complex.im_ofNat, mul_zero, mul_one, zero_mul, one_mul,
        sub_zero] at h
      have hw0 : (0 : ℝ) ≤ w.re := hw
      linarith
    have h1p2 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
    have hden : ((j : ℝ) + 1) ^ 2
        ≤ ‖2 * (w + ((j : ℕ) : ℂ)) + a‖
          * ‖2 * (w + ((j : ℕ) : ℂ)) + a + 2‖ := by
      calc (((j : ℝ) + 1) ^ 2) = ((j : ℝ) + 1) * ((j : ℝ) + 1) := by ring
        _ ≤ _ := mul_le_mul g1 g2 (by positivity) (by positivity)
    rw [norm_div, norm_mul, ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos h1p2 2) hden
  have hs : Summable (fun j => c / ((2 * (w + ((j : ℕ) : ℂ)) + a)
      * (2 * (w + ((j : ℕ) : ℂ)) + a + 2))) := by
    apply Summable.of_norm_bounded
      (g := fun (j : ℕ) => ‖c‖ * (1 / ((((j : ℝ)) + 1) ^ 2)))
    · exact hshift
    · intro j
      exact hmaj j
  refine ⟨hs, ?_⟩
  have hsum : ∀ J, ∑ j ∈ Finset.range J,
      (c / ((2 * (w + ((j : ℕ) : ℂ)) + a)
        * (2 * (w + ((j : ℕ) : ℂ)) + a + 2)))
      = (c / 2) * (1 / (2 * w + a))
        - (c / 2) * (1 / (2 * (w + (((J : ℕ)) : ℂ)) + a)) := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.sum_range_succ, ih, hpf J]
      have e : w + ((((J + 1 : ℕ))) : ℂ) = w + ((J : ℕ) : ℂ) + 1 := by
        push_cast
        ring
      rw [e]
      ring
  have hvan : Tendsto (fun J => (c / 2) * (1 / (2 * (w + (((J : ℕ)) : ℂ)) + a)))
      atTop (𝓝 0) := by
    have hbnd1 : ∀ J : ℕ, ‖(1 : ℂ) / (2 * (w + (((J : ℕ)) : ℂ)) + a)‖
        ≤ 1 * (1 / (((J : ℝ)) + 1)) := by
      intro J
      have g1 : (J : ℝ) + 1 ≤ ‖2 * (w + ((J : ℕ) : ℂ)) + a‖ := by
        have h := Complex.re_le_norm (2 * (w + ((J : ℕ) : ℂ)) + a)
        simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.one_re,
          Complex.I_re, Complex.re_ofNat, Complex.im_ofNat, mul_zero, mul_one, zero_mul,
          one_mul, sub_zero] at h
        linarith [hw]
      have h1p : (0 : ℝ) < (J : ℝ) + 1 := by
        have hnn : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
        linarith
      calc ‖(1 : ℂ) / (2 * (w + ((J : ℕ) : ℂ)) + a)‖
          = 1 / ‖2 * (w + ((J : ℕ) : ℂ)) + a‖ := by
            rw [norm_div, norm_one]
        _ ≤ 1 * (1 / ((J : ℝ) + 1)) := by
          rw [one_mul]
          exact div_le_div_of_nonneg_left zero_le_one h1p g1
        _ = 1 * (1 / ((J : ℝ) + 1)) := rfl
    have hlim1 : Tendsto (fun J : ℕ => 1 * (1 / ((((J : ℝ)) + 1)))) atTop (𝓝 0) := by
      have h1 := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 : ℝ)
      rwa [mul_zero] at h1
    have h1 : Tendsto (fun J : ℕ => (1 : ℂ) / (2 * (w + (((J : ℕ)) : ℂ)) + a))
        atTop (𝓝 0) :=
      squeeze_zero_norm hbnd1 hlim1
    have h2 := h1.const_mul (c / 2)
    rwa [mul_zero] at h2
  have hlim2 : Tendsto (fun J => ∑ j ∈ Finset.range J,
      (c / ((2 * (w + ((j : ℕ) : ℂ)) + a)
        * (2 * (w + ((j : ℕ) : ℂ)) + a + 2)))) atTop
      (𝓝 ((c / 2) * (1 / (2 * w + a)))) := by
    have h2 := tendsto_const_nhds (x := (c / 2) * (1 / (2 * w + a))) |>.sub hvan
    rw [sub_zero] at h2
    refine h2.congr (fun J => ?_)
    rw [hsum J]
  have h3 := hs.hasSum.tendsto_sum_nat
  rw [tendsto_nhds_unique h3 hlim2]

/-- exact sum of `c / ((2 * j + b) * (2 * j + b + 2))` with `1 ≤ b.re`:
the `w = 0` case of step-2 telescoping, in matcher-friendly doubled form.
Covers factored `1 / (4k² - 1)`-type series. -/
theorem Complex_tsum_telescoping_step2n {c b : ℂ} (hb : 1 ≤ b.re) :
    Summable (fun j => c / (((2 * ((j : ℕ) : ℂ)) + b) * ((2 * ((j : ℕ) : ℂ)) + b + 2))) ∧
    (∑' j, c / (((2 * ((j : ℕ) : ℂ)) + b) * ((2 * ((j : ℕ) : ℂ)) + b + 2)))
      = (c / 2) / b := by
  have h0 := Complex_tsum_telescoping_step2 (c := c) (w := 0) (a := b)
    (by simp) hb
  have hbridge : ∀ j : ℕ, c / ((2 * ((0 : ℂ) + ((j : ℕ) : ℂ)) + b)
        * (2 * ((0 : ℂ) + ((j : ℕ) : ℂ)) + b + 2))
      = c / (((2 * ((j : ℕ) : ℂ)) + b) * ((2 * ((j : ℕ) : ℂ)) + b + 2)) := by
    intro j
    have e1 : 2 * ((0 : ℂ) + ((j : ℕ) : ℂ)) + b = (2 * ((j : ℕ) : ℂ)) + b := by ring
    rw [e1]
  have heq : (fun j => c / ((2 * ((0 : ℂ) + ((j : ℕ) : ℂ)) + b)
      * (2 * ((0 : ℂ) + ((j : ℕ) : ℂ)) + b + 2)))
      = (fun j => c / (((2 * ((j : ℕ) : ℂ)) + b) * ((2 * ((j : ℕ) : ℂ)) + b + 2))) :=
    funext hbridge
  obtain ⟨hs, hv⟩ := h0
  rw [heq] at hs hv
  refine ⟨hs, ?_⟩
  rwa [show (c / 2) * (1 / (2 * (0 : ℂ) + b)) = (c / 2) / b from by ring_nf] at hv

/-- geometric majorant for `c / (N + j + a)!` (factorial): successive ratios are
`≤ 1 / (N + a + 1)`. -/
theorem Complex_factorial_majorant {c : ℂ} {a N : ℕ} (ha : 1 ≤ a) :
    ∀ j, ‖c / ((Nat.factorial (N + j + a) : ℕ) : ℂ)‖
      ≤ (‖c‖ / ((Nat.factorial (N + a) : ℕ) : ℝ)) * (1 / (((N : ℝ)) + a + 1)) ^ j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have e : N + (j + 1) + a = (N + j + a) + 1 := by omega
    have hpos : (0 : ℝ) < ((N : ℝ)) + a + 1 := by
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have ha0 : (0 : ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_nonneg a
      have h1a : (1 : ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast ha
      linarith
    have hstep : (1 : ℝ) / (((N : ℝ)) + (j : ℝ) + ((a : ℕ) : ℝ) + 1)
        ≤ 1 / (((N : ℝ)) + a + 1) := by
      apply one_div_le_one_div_of_le hpos
      have hnj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hne1 : ((Nat.factorial (N + j + a) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (N + j + a)
    have hne2 : (((N : ℝ)) + (j : ℝ) + ((a : ℕ) : ℝ) + 1) ≠ 0 := by
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have ha0 : (0 : ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_nonneg a
      have hnj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have h1a : (1 : ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast ha
      linarith
    have hnorm : ‖c / ((Nat.factorial (N + (j + 1) + a) : ℕ) : ℂ)‖
        = (‖c‖ / ((Nat.factorial (N + j + a) : ℕ) : ℝ))
          * (1 / ((((N : ℝ)) + (j : ℝ) + ((a : ℕ)) : ℝ) + 1)) := by
      rw [e, Nat.factorial_succ, Nat.cast_mul, norm_div, norm_mul,
        Complex.norm_natCast, Complex.norm_natCast]
      have hcast : ((((N + j + a + 1 : ℕ)) : ℝ))
          = ((N : ℝ)) + (j : ℝ) + ((a : ℕ) : ℝ) + 1 := by
        push_cast
        ring
      rw [hcast]
      field_simp
    rw [hnorm]
    have hcast : ((((N + j + a : ℕ)) : ℝ) + 1) = ((N : ℝ)) + (j : ℝ) + ((a : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    have hbridge : (‖c‖ / ((Nat.factorial (N + j + a) : ℕ) : ℝ))
        = ‖c / ((Nat.factorial (N + j + a) : ℕ) : ℂ)‖ := by
      rw [norm_div, Complex.norm_natCast]
    rw [hbridge]
    calc ‖c / ((Nat.factorial (N + j + a) : ℕ) : ℂ)‖ * (1 / ((((N : ℝ)) + (j : ℝ) + ((a : ℕ)) : ℝ) + 1))
        ≤ ((‖c‖ / ((Nat.factorial (N + a) : ℕ) : ℝ)) * (1 / (((N : ℝ)) + a + 1)) ^ j)
          * (1 / (((N : ℝ)) + a + 1)) :=
          mul_le_mul ih hstep (by positivity) (by positivity)
      _ = (‖c‖ / ((Nat.factorial (N + a) : ℕ) : ℝ)) * (1 / (((N : ℝ)) + a + 1)) ^ (j + 1) := by
          rw [pow_succ]; ring

/-- geometric majorant for `c / (N + j + a)^(N + j + a)`: successive ratios are
`≤ 1 / (N + a + 1)` (using `(m / (m+1))^m ≤ 1`). -/
theorem Complex_selfpow_majorant {c : ℂ} {a N : ℕ} (ha : 1 ≤ a) :
    ∀ j, ‖c / ((((N + j + a : ℕ)) : ℂ) ^ (N + j + a))‖
      ≤ (‖c‖ / ((((N + a : ℕ)) : ℝ) ^ (N + a))) * (1 / (((N : ℝ)) + a + 1)) ^ j := by
  have hbase : ∀ m : ℕ, 1 ≤ m → (((m : ℝ)) / (((m : ℝ)) + 1)) ^ m ≤ 1 := by
    intro m hm
    have hm0 : (0 : ℝ) ≤ ((m : ℝ)) := Nat.cast_nonneg m
    apply pow_le_one₀ (by positivity : (0:ℝ) ≤ (m : ℝ) / (((m : ℝ)) + 1)) _
    rw [div_le_one (by linarith : (0:ℝ) < (m : ℝ) + 1)]
    have : (1 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast hm
    linarith
  intro j
  induction j with
  | zero =>
    have e0 : N + 0 + a = N + a := by omega
    rw [e0]
    simp only [pow_zero, mul_one, norm_div, norm_pow, Complex.norm_natCast]
    exact le_rfl
  | succ j ih =>
    have e : N + (j + 1) + a = (N + j + a) + 1 := by omega
    have hpos : (0 : ℝ) < ((N : ℝ)) + a + 1 := by
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have h1a : (1 : ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast ha
      linarith
    have hm1 : 1 ≤ N + j + a := by omega
    have hstep : (1 : ℝ) / (((N : ℝ)) + (j : ℝ) + ((a : ℕ) : ℝ) + 1)
        ≤ 1 / (((N : ℝ)) + a + 1) := by
      apply one_div_le_one_div_of_le hpos
      have hnj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hratio : ((((N + j + a : ℕ)) : ℝ) ^ (N + j + a))
        / ((((N + j + a + 1 : ℕ)) : ℝ) ^ (N + j + a + 1))
        ≤ 1 / ((((N : ℝ)) + (j : ℝ) + ((a : ℕ)) : ℝ) + 1) := by
      have h1 : ((((N + j + a + 1 : ℕ)) : ℝ) ^ (N + j + a + 1))
          = ((((N + j + a : ℕ)) : ℝ) + 1)
            * (((((N + j + a : ℕ)) : ℝ) + 1) ^ (N + j + a)) := by
        have ee : N + j + a + 1 = (N + j + a) + 1 := by omega
        rw [ee, pow_succ, Nat.cast_add, Nat.cast_one]
        ring
      rw [h1]
      have hcast : ((((N + j + a : ℕ)) : ℝ)) = ((N : ℝ)) + (j : ℝ) + ((a : ℕ) : ℝ) := by
        push_cast
        ring
      have hbase2 := hbase (N + j + a) (by omega)
      have hx1 : ((((N + j + a : ℕ)) : ℝ)) + 1 ≠ 0 := by
        have hxnn : (0 : ℝ) ≤ ((((N + j + a : ℕ)) : ℝ)) := Nat.cast_nonneg _
        have : (0 : ℝ) < ((((N + j + a : ℕ)) : ℝ)) + 1 := by linarith
        exact ne_of_gt this
      have hpow : ((((N + j + a : ℕ)) : ℝ) + 1) ^ (N + j + a) ≠ 0 :=
        pow_ne_zero _ hx1
      have h3 : ((((N + j + a : ℕ)) : ℝ) ^ (N + j + a))
          / (((((N + j + a : ℕ)) : ℝ) + 1) * (((((N + j + a : ℕ)) : ℝ) + 1) ^ (N + j + a)))
          = (1 / (((((N + j + a : ℕ)) : ℝ) + 1)))
            * (((((N + j + a : ℕ)) : ℝ) / ((((N + j + a : ℕ)) : ℝ) + 1)) ^ (N + j + a)) := by
        rw [div_pow]
        field_simp
      rw [h3]
      have hfin : (1 / (((((N + j + a : ℕ)) : ℝ) + 1)))
            * (((((N + j + a : ℕ)) : ℝ) / ((((N + j + a : ℕ)) : ℝ) + 1)) ^ (N + j + a))
          ≤ 1 / (((((N + j + a : ℕ)) : ℝ) + 1)) := by
        calc (1 / (((((N + j + a : ℕ)) : ℝ) + 1)))
              * (((((N + j + a : ℕ)) : ℝ) / ((((N + j + a : ℕ)) : ℝ) + 1)) ^ (N + j + a))
            ≤ (1 / (((((N + j + a : ℕ)) : ℝ) + 1))) * 1 :=
              mul_le_mul_of_nonneg_left hbase2 (by positivity)
          _ = 1 / (((((N + j + a : ℕ)) : ℝ) + 1)) := by ring
      rw [← hcast]
      exact hfin
    have e2 : N + j + a + 1 = (N + j + a) + 1 := by omega
    have hYpos : (0 : ℝ) < ((((N + j + a : ℕ)) : ℝ)) := by
      exact_mod_cast (by omega : 0 < N + j + a)
    have hne1 : ((((N + j + a : ℕ)) : ℝ) ^ (N + j + a)) ≠ 0 :=
      pow_ne_zero _ (ne_of_gt hYpos)
    have hY1pos : (0 : ℝ) < ((((N + j + a + 1 : ℕ)) : ℝ)) := by
      exact_mod_cast (by omega : 0 < N + j + a + 1)
    have hne2 : ((((N + j + a + 1 : ℕ)) : ℝ) ^ (N + j + a + 1)) ≠ 0 :=
      pow_ne_zero _ (ne_of_gt hY1pos)
    have hnorm : ‖c / ((((N + (j + 1) + a : ℕ)) : ℂ) ^ (N + (j + 1) + a))‖
        = (‖c‖ / ((((N + j + a : ℕ)) : ℝ) ^ (N + j + a)))
          * (((((N + j + a : ℕ)) : ℝ) ^ (N + j + a))
            / ((((N + j + a + 1 : ℕ)) : ℝ) ^ (N + j + a + 1))) := by
      rw [e, e2, norm_div, norm_pow, Complex.norm_natCast]
      field_simp
    rw [hnorm]
    have hbridge : (‖c‖ / ((((N + j + a : ℕ)) : ℝ) ^ (N + j + a)))
        = ‖c / ((((N + j + a : ℕ)) : ℂ) ^ (N + j + a))‖ := by
      rw [norm_div, norm_pow, Complex.norm_natCast]
    rw [hbridge]
    calc ‖c / ((((N + j + a : ℕ)) : ℂ) ^ (N + j + a))‖
          * (((((N + j + a : ℕ)) : ℝ) ^ (N + j + a))
            / ((((N + j + a + 1 : ℕ)) : ℝ) ^ (N + j + a + 1)))
        ≤ ((‖c‖ / ((((N + a : ℕ)) : ℝ) ^ (N + a))) * (1 / (((N : ℝ)) + a + 1)) ^ j)
          * (1 / ((((N : ℝ)) + (j : ℝ) + ((a : ℕ)) : ℝ) + 1)) :=
          mul_le_mul ih hratio (by positivity) (by positivity)
      _ ≤ ((‖c‖ / ((((N + a : ℕ)) : ℝ) ^ (N + a))) * (1 / (((N : ℝ)) + a + 1)) ^ j)
          * (1 / (((N : ℝ)) + a + 1)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (‖c‖ / ((((N + a : ℕ)) : ℝ) ^ (N + a))) * (1 / (((N : ℝ)) + a + 1)) ^ (j + 1) := by
          rw [pow_succ]; ring


/-- geometric majorant for `c / (b^(N+j+a) - 1)` with `2 ≤ b`: the denominator
is at least half of `b^(N+j+a)`. -/
theorem Complex_mersenne_majorant {c : ℂ} {b : ℝ} {N a : ℕ} (hb : 2 ≤ b) (ha : 1 ≤ a) :
    ∀ j, ‖c / (((((b : ℝ)) : ℂ) ^ (N + j + a)) - 1)‖
      ≤ (2 * ‖c‖ / (((b : ℝ) ^ (N + a)))) * ((1 / 2) ^ j) := by
  have hb2 : (2 : ℝ) ≤ b := hb
  have hBpos : (0 : ℝ) < b := by linarith [hb]
  intro j
  have hmn : 1 ≤ N + j + a := by omega
  have hge : (2 : ℝ) ≤ ((b : ℝ) ^ (N + j + a)) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (N + j + a) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ ((b : ℝ) ^ (N + j + a)) := pow_le_pow_left₀ (by norm_num) hb2 _
  have hXpos : (0 : ℝ) < ((b : ℝ) ^ (N + j + a)) := pow_pos hBpos _
  have hden : ((b : ℝ) ^ (N + j + a)) / 2 ≤ ‖(((b : ℂ) ^ (N + j + a)) - 1)‖ := by
    have h1 : ((b : ℝ) ^ (N + j + a)) - 1 ≤ ‖(((((b : ℝ)) : ℂ) ^ (N + j + a)) - 1)‖ := by
      have h := norm_sub_norm_le (((((b : ℝ)) : ℂ) ^ (N + j + a))) 1
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_one] at h
      have hbab : |b| = b := abs_of_nonneg (by linarith [hb])
      rw [hbab] at h
      linarith [h]
    linarith
  have hpow : ((b : ℝ) ^ (N + j + a)) = ((b : ℝ) ^ (N + a)) * ((b : ℝ) ^ j) := by
    have e : N + j + a = (N + a) + j := by omega
    rw [e, pow_add]
  have hB1 : b ^ (N + a) ≠ 0 := pow_ne_zero _ (ne_of_gt hBpos)
  have hB2 : b ^ j ≠ 0 := pow_ne_zero _ (ne_of_gt hBpos)
  have h12 : (1 : ℝ) / (((b : ℝ) ^ j)) ≤ ((1 / 2) ^ j) := by
    have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hBj : (2 : ℝ) ^ j ≤ ((b : ℝ) ^ j) := pow_le_pow_left₀ (by norm_num) hb2 j
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le h2j hBj
  calc ‖c / (((((b : ℝ)) : ℂ) ^ (N + j + a)) - 1)‖
      = ‖c‖ / ‖(((((b : ℝ)) : ℂ) ^ (N + j + a)) - 1)‖ := by rw [norm_div]
    _ ≤ ‖c‖ / ((((b : ℝ) ^ (N + j + a))) / 2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by linarith [hXpos]) hden
    _ = (2 * ‖c‖ / (((b : ℝ) ^ (N + a)))) * (1 / (((b : ℝ) ^ j))) := by
        rw [hpow]
        field_simp
    _ ≤ (2 * ‖c‖ / (((b : ℝ) ^ (N + a)))) * ((1 / 2) ^ j) :=
        mul_le_mul_of_nonneg_left h12 (by positivity)

/-- paired Fibonacci ratio bounds: `F_{m+1} ≥ 3/2 · F_m` and `≤ 2 · F_m`. -/
theorem Complex_fib_ratio (m : ℕ) (hm : 2 ≤ m) :
    (3 / 2) * (((Nat.fib m : ℕ)) : ℝ) ≤ (((Nat.fib (m + 1) : ℕ)) : ℝ)
    ∧ (((Nat.fib (m + 1) : ℕ)) : ℝ) ≤ 2 * (((Nat.fib m : ℕ)) : ℝ) := by
  suffices h : ∀ k : ℕ, (3 / 2) * (((Nat.fib (k + 2) : ℕ)) : ℝ)
      ≤ (((Nat.fib (k + 3) : ℕ)) : ℝ)
      ∧ (((Nat.fib (k + 3) : ℕ)) : ℝ) ≤ 2 * (((Nat.fib (k + 2) : ℕ)) : ℝ) by
    have e : m = (m - 2) + 2 := by omega
    rw [e]
    exact h (m - 2)
  intro k
  induction k with
  | zero =>
    have e2 : Nat.fib 2 = 1 := by decide
    have e3 : Nat.fib 3 = 2 := by decide
    simp only [Nat.zero_add]
    rw [e2, e3]
    norm_num
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have r3 : k + 1 + 2 = k + 3 := by omega
    have r4 : k + 1 + 3 = k + 4 := by omega
    rw [r3, r4]
    have e4a : k + 4 = (k + 2) + 2 := by omega
    have e4b : (k + 2) + 1 = k + 3 := by omega
    have f4 : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) := by
      rw [e4a, Nat.fib_add_two, e4b]
    have hnn2 : (0 : ℝ) ≤ (((Nat.fib (k + 2) : ℕ)) : ℝ) := Nat.cast_nonneg _
    refine ⟨?_, ?_⟩
    · rw [f4, Nat.cast_add]
      linarith [ih2]
    · rw [f4, Nat.cast_add]
      linarith [ih1, hnn2]

/-- geometric majorant for `c / F_{N+j+1}` via the Fibonacci ratio bound. -/
theorem Complex_fib_majorant {c : ℂ} {N : ℕ} (hN : 1 ≤ N) :
    ∀ j, ‖c / ((((Nat.fib (N + j + 1) : ℕ))) : ℂ)‖
      ≤ (‖c‖ / ((((Nat.fib (N + 1) : ℕ))) : ℝ)) * ((2 / 3) ^ j) := by
  have hfib2 : ∀ M : ℕ, 0 < Nat.fib (M + 2) := by
    intro M
    induction M with
    | zero => decide
    | succ M ih =>
      have e : M + 1 + 2 = M + 3 := by omega
      have f : Nat.fib (M + 3) = Nat.fib (M + 1) + Nat.fib (M + 2) := by
        have e1 : M + 3 = (M + 1) + 2 := by omega
        have e2 : (M + 1) + 1 = M + 2 := by omega
        rw [e1, Nat.fib_add_two, e2]
      rw [e, f]
      omega
  have hF1pos : (0 : ℝ) < ((((Nat.fib (N + 1) : ℕ))) : ℝ) := by
    have eN : N + 1 = (N - 1) + 2 := by omega
    rw [eN]
    exact_mod_cast hfib2 (N - 1)
  have hgrow : ∀ j : ℕ, (((Nat.fib (N + 1) : ℕ)) : ℝ) * ((3 / 2) ^ j)
      ≤ (((Nat.fib (N + j + 1) : ℕ)) : ℝ) := by
    intro j
    induction j with
    | zero =>
      have e : N + 0 + 1 = N + 1 := by omega
      rw [e, pow_zero, mul_one]
    | succ j ih =>
      have hm : 2 ≤ N + j + 1 := by omega
      have hratio := (Complex_fib_ratio (N + j + 1) hm).1
      have e : N + (j + 1) + 1 = (N + j + 1) + 1 := by omega
      rw [e]
      calc (((Nat.fib (N + 1) : ℕ)) : ℝ) * (3 / 2) ^ (j + 1)
          = ((((Nat.fib (N + 1) : ℕ)) : ℝ) * (3 / 2) ^ j) * (3 / 2) := by ring
        _ ≤ (((Nat.fib (N + j + 1) : ℕ)) : ℝ) * (3 / 2) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ ≤ (((Nat.fib (N + j + 1 + 1) : ℕ)) : ℝ) := by
          have e2 : N + j + 1 + 1 = (N + j + 1) + 1 := by omega
          rw [e2]
          linarith [hratio]
  intro j
  have hFpos : (0 : ℝ) < (((Nat.fib (N + j + 1) : ℕ)) : ℝ) := by
    have h2 := hgrow j
    have h3 : (0 : ℝ) < (((Nat.fib (N + 1) : ℕ)) : ℝ) * (3 / 2) ^ j :=
      mul_pos hF1pos (by positivity)
    linarith
  rw [norm_div, Complex.norm_natCast]
  have hprod : (0 : ℝ) < (((Nat.fib (N + 1) : ℕ)) : ℝ) * (3 / 2) ^ j :=
    mul_pos hF1pos (by positivity)
  have hstep : (1 : ℝ) / (((Nat.fib (N + j + 1) : ℕ)) : ℝ)
      ≤ 1 / ((((Nat.fib (N + 1) : ℕ)) : ℝ) * (3 / 2) ^ j) :=
    one_div_le_one_div_of_le hprod (hgrow j)
  have hF1ne : ((((Nat.fib (N + 1) : ℕ))) : ℝ) ≠ 0 := ne_of_gt hF1pos
  have h32ne : ((3 / 2 : ℝ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsplit : (1 / (((Nat.fib (N + 1) : ℕ)) : ℝ)) * ((2 / 3 : ℝ) ^ j)
      = 1 / ((((Nat.fib (N + 1) : ℕ)) : ℝ) * (3 / 2) ^ j) := by
    field_simp
    rw [← mul_pow]
    norm_num
  have hbase : (1 : ℝ) / (((Nat.fib (N + j + 1) : ℕ)) : ℝ)
      ≤ (1 / (((Nat.fib (N + 1) : ℕ)) : ℝ)) * ((2 / 3) ^ j) := by
    rw [hsplit]
    exact hstep
  calc ‖c‖ / (((Nat.fib (N + j + 1) : ℕ)) : ℝ)
      = ‖c‖ * (1 / (((Nat.fib (N + j + 1) : ℕ)) : ℝ)) := by rw [div_eq_mul_one_div]
    _ ≤ ‖c‖ * ((1 / (((Nat.fib (N + 1) : ℕ)) : ℝ)) * ((2 / 3) ^ j)) :=
        mul_le_mul_of_nonneg_left hbase (norm_nonneg _)
    _ = (‖c‖ / (((Nat.fib (N + 1) : ℕ)) : ℝ)) * ((2 / 3) ^ j) := by
        rw [div_eq_mul_one_div]; ring

/-- divergence from a positive lower bound on norms: terms do not vanish. -/
theorem Complex_not_summable_of_lower_bound {f : ℕ → ℂ} {c : ℝ} (hc : 0 < c) (N : ℕ)
    (h : ∀ k, N ≤ k → c ≤ ‖f k‖) : ¬ Summable f := by
  intro hs
  have hv := hs.tendsto_atTop_zero
  rw [tendsto_zero_iff_norm_tendsto_zero] at hv
  have hev : ∀ᶠ k in atTop, ‖f k‖ < c := hv.eventually (gt_mem_nhds hc)
  obtain ⟨k, hklt, hkN⟩ := (hev.and (eventually_ge_atTop N)).exists
  have hkle := h k hkN
  linarith

/-- divergence from a harmonic lower bound on norms: comparison with the
shifted harmonic series (which diverges). Covers alternating-harmonic-type
series over `ℂ`. -/
theorem Complex_not_summable_of_harmonic_lower {f : ℕ → ℂ} {N a : ℕ}
    (h : ∀ j : ℕ, 1 * (1 / (((j : ℝ)) + ((N + a : ℕ) : ℝ))) ≤ ‖f (j + N)‖) :
    ¬ Summable f := by
  intro hs
  have h1 := ((summable_nat_add_iff (f := f) N).2 hs).norm
  have hnn : ∀ j : ℕ, (0 : ℝ) ≤ 1 * (1 / (((j : ℝ)) + ((N + a : ℕ) : ℝ))) := by
    intro j
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hna : (0 : ℝ) ≤ ((N + a : ℕ) : ℝ) := Nat.cast_nonneg _
    positivity
  have h2 : Summable (fun j : ℕ => 1 * (1 / (((j : ℝ)) + ((N + a : ℕ) : ℝ)))) :=
    Summable.of_nonneg_of_le hnn h h1
  have hs' : Summable (fun j : ℕ => 1 / ((((j + (N + a) : ℕ))) : ℝ)) := by
    refine h2.congr (fun j => ?_)
    simp only [Nat.cast_add, one_mul]
  have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) (N + a)).1 hs'
  exact Real.not_summable_one_div_natCast this

/-- summability reflects through `Complex.re`: a real-cast series is summable
only if the underlying real series is. -/
theorem Complex_summable_ofReal {a : ℕ → ℝ} {c : ℕ → ℂ} (h : ∀ k, c k = ((a k : ℝ) : ℂ))
    (hs : Summable c) : Summable a := by
  have h2 := hs.map Complex.reCLM Complex.reCLM.continuous
  refine h2.congr (fun k => ?_)
  change Complex.re (c k) = a k
  rw [h k, Complex.ofReal_re]
