module

import all Lynth.Interval.Integral.Math.IntgrlDefs

/-!
P0: roots, weights and exactness. Send with IntgrlDefs.lean.
Every sorrry is an unproved obligation, not a claimed completed proof.
Mathlib's Polynomial.shiftedLegendre can be used to prove these results;
its convention must be transformed to the normalization in IntgrlDefs.
-/

noncomputable section

open scoped BigOperators
open Polynomial MeasureTheory

namespace Intgrl

/-! ### Basic identities for the Legendre recurrence -/

@[simp] lemma legendre_zero' : legendre 0 = 1 := by simp [legendre]
@[simp] lemma legendre_one' : legendre 1 = X := by simp [legendre]

lemma legendre_succ_succ (n : ℕ) : legendre (n + 2) =
    C ((2 * (n : ℝ) + 3) / ((n : ℝ) + 2)) * X * legendre (n + 1) -
      C (((n : ℝ) + 1) / ((n : ℝ) + 2)) * legendre n := by
  rw [legendre]

lemma legendre_eval_rec (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * (legendre (n + 2)).eval x =
      (2 * (n : ℝ) + 3) * x * (legendre (n + 1)).eval x - ((n : ℝ) + 1) * (legendre n).eval x := by
  rw [legendre_succ_succ]
  simp only [eval_sub, eval_mul, eval_C, eval_X]
  have : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp

lemma legendre_deriv_rec (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * (legendre (n + 2)).derivative.eval x =
      (2 * (n : ℝ) + 3) * ((legendre (n + 1)).eval x + x * (legendre (n + 1)).derivative.eval x)
        - ((n : ℝ) + 1) * (legendre n).derivative.eval x := by
  rw [legendre_succ_succ]
  simp only [derivative_sub, derivative_mul, derivative_C, derivative_X, zero_mul, zero_add,
    mul_one, eval_sub, eval_mul, eval_C, eval_X, eval_add]
  have : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp

/-- `D1`: `P'_{n+2} - P'_n = (2n+3) P_{n+1}`, assuming `D2` at `n`. -/
lemma legendre_d1_of_d2 (n : ℕ) (x : ℝ)
    (h : x * (legendre (n + 1)).derivative.eval x - (legendre n).derivative.eval x =
      ((n : ℝ) + 1) * (legendre (n + 1)).eval x) :
    (legendre (n + 2)).derivative.eval x - (legendre n).derivative.eval x =
      (2 * (n : ℝ) + 3) * (legendre (n + 1)).eval x := by
  have hr := legendre_deriv_rec n x
  have : (n : ℝ) + 2 ≠ 0 := by positivity
  apply mul_left_cancel₀ this
  linear_combination hr + (2 * (n : ℝ) + 3) * h

/-- `D2`: `x P'_{n+1} - P'_n = (n+1) P_{n+1}`. -/
lemma legendre_d2 (n : ℕ) (x : ℝ) :
    x * (legendre (n + 1)).derivative.eval x - (legendre n).derivative.eval x =
      ((n : ℝ) + 1) * (legendre (n + 1)).eval x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ =>
      rw [legendre_succ_succ]
      simp [derivative_mul]
      ring
    | m + 2, ih =>
      have h1 := legendre_d1_of_d2 (m + 1) x (ih (m + 1) (by omega))
      have h0 := legendre_d1_of_d2 m x (ih m (by omega))
      have h2 := ih m (by omega)
      have hr := legendre_eval_rec (m + 1) x
      rw [show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring] at h1 hr
      rw [show m + 2 + 1 = m + 3 by ring]
      push_cast at h1 h0 h2 hr ⊢
      linear_combination x * h1 + h2 - h0 - hr

lemma legendre_d1 (n : ℕ) (x : ℝ) :
    (legendre (n + 2)).derivative.eval x - (legendre n).derivative.eval x =
      (2 * (n : ℝ) + 3) * (legendre (n + 1)).eval x :=
  legendre_d1_of_d2 n x (legendre_d2 n x)

/-- `D3`: `P'_{n+1} - x P'_n = (n+1) P_n`. -/
lemma legendre_d3 (n : ℕ) (x : ℝ) :
    (legendre (n + 1)).derivative.eval x - x * (legendre n).derivative.eval x =
      ((n : ℝ) + 1) * (legendre n).eval x := by
  match n with
  | 0 => simp
  | m + 1 =>
    have h1 := legendre_d1 m x
    have h2 := legendre_d2 m x
    push_cast
    linear_combination h1 - h2

lemma legendre_d4 (n : ℕ) (x : ℝ) :
    (1 - x ^ 2) * (legendre (n + 1)).derivative.eval x =
      ((n : ℝ) + 1) * ((legendre n).eval x - x * (legendre (n + 1)).eval x) := by
  have h2 := legendre_d2 n x
  have h3 := legendre_d3 n x
  linear_combination h3 - x * h2

lemma legendre_d4_poly (n : ℕ) :
    (1 - X ^ 2) * derivative (legendre (n + 1)) =
      C ((n : ℝ) + 1) * (legendre n - X * legendre (n + 1)) := by
  apply Polynomial.funext
  intro x
  simpa using legendre_d4 n x

/-- Legendre differential equation. -/
lemma legendre_ode (n : ℕ) (x : ℝ) :
    (1 - x ^ 2) * (legendre n).derivative.derivative.eval x
      - 2 * x * (legendre n).derivative.eval x
      + (n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval x = 0 := by
  match n with
  | 0 => simp
  | m + 1 =>
    have h := congrArg (fun p => (derivative p).eval x) (legendre_d4_poly m)
    simp only [derivative_mul, derivative_sub, derivative_one, derivative_X_pow,
      derivative_C, derivative_X, eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_pow,
      eval_one, zero_mul, zero_add, one_mul, zero_sub, eval_neg] at h
    have h2 := legendre_d2 m x
    push_cast at h ⊢
    linear_combination h - ((m : ℝ) + 1) * h2

lemma legendre_eval_one (n : ℕ) : (legendre n).eval 1 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp
    | m + 2, ih =>
      have hr := legendre_eval_rec m 1
      rw [ih m (by omega), ih (m + 1) (by omega)] at hr
      have : (m : ℝ) + 2 ≠ 0 := by positivity
      apply mul_left_cancel₀ this
      linear_combination hr

lemma legendre_parity' (n : ℕ) (x : ℝ) :
    (legendre n).eval (-x) = (-1 : ℝ) ^ n * (legendre n).eval x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp
    | m + 2, ih =>
      have hr := legendre_eval_rec m (-x)
      have hr' := legendre_eval_rec m x
      rw [ih m (by omega), ih (m + 1) (by omega)] at hr
      have : (m : ℝ) + 2 ≠ 0 := by positivity
      apply mul_left_cancel₀ this
      rw [hr]
      linear_combination -((-1 : ℝ) ^ m) * hr'

lemma legendre_natDegree_and_lc (n : ℕ) :
    (legendre n).natDegree = n ∧ 0 < (legendre n).leadingCoeff := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp
    | m + 2, ih =>
      obtain ⟨d1, l1⟩ := ih (m + 1) (by omega)
      obtain ⟨d0, l0⟩ := ih m (by omega)
      have ha : (0 : ℝ) < (2 * (m : ℝ) + 3) / ((m : ℝ) + 2) := by positivity
      have hA : (C ((2 * (m : ℝ) + 3) / ((m : ℝ) + 2)) * X * legendre (m + 1)).natDegree = m + 2 := by
        rw [natDegree_mul (by simp [ha.ne']) (by intro h; simp [h] at l1), natDegree_C_mul_X _ ha.ne', d1]
        ring
      have hlA : (C ((2 * (m : ℝ) + 3) / ((m : ℝ) + 2)) * X * legendre (m + 1)).leadingCoeff =
          (2 * (m : ℝ) + 3) / ((m : ℝ) + 2) * (legendre (m + 1)).leadingCoeff := by
        rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, mul_one]
      have hB : (C (((m : ℝ) + 1) / ((m : ℝ) + 2)) * legendre m).natDegree ≤ m :=
        (natDegree_C_mul_le _ _).trans d0.le
      have hlt : (C (((m : ℝ) + 1) / ((m : ℝ) + 2)) * legendre m).degree <
          (C ((2 * (m : ℝ) + 3) / ((m : ℝ) + 2)) * X * legendre (m + 1)).degree := by
        have hne : C ((2 * (m : ℝ) + 3) / ((m : ℝ) + 2)) * X * legendre (m + 1) ≠ 0 := by
          intro h; rw [h] at hA; simp at hA
        rw [degree_eq_natDegree hne, hA]
        refine lt_of_le_of_lt (degree_le_natDegree) ?_
        exact_mod_cast (by omega : (C (((m : ℝ) + 1) / ((m : ℝ) + 2)) * legendre m).natDegree < m + 2)
      rw [legendre_succ_succ]
      refine ⟨?_, ?_⟩
      · rw [natDegree_sub_eq_left_of_natDegree_lt (by omega), hA]
      · rw [leadingCoeff_sub_of_degree_lt hlt, hlA]
        positivity


/-! ### Orthogonality -/

lemma legendre_ne_zero (n : ℕ) : legendre n ≠ 0 := by
  intro h
  have := (legendre_natDegree_and_lc n).2
  simp [h] at this

/-- `((1 - X^2) P_n')' = -n(n+1) P_n` as polynomials. -/
lemma legendre_sturm_poly (n : ℕ) :
    derivative ((1 - X ^ 2) * derivative (legendre n)) =
      C (-((n : ℝ) * ((n : ℝ) + 1))) * legendre n := by
  apply Polynomial.funext
  intro x
  have h := legendre_ode n x
  simp only [derivative_mul, derivative_sub, derivative_one, derivative_X_pow, eval_add,
    eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_C, zero_sub, eval_neg]
  push_cast
  linear_combination h

lemma integral_poly_eval_derivative (p : ℝ[X]) (a b : ℝ) :
    ∫ t in a..b, (derivative p).eval t = p.eval b - p.eval a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _; exact p.hasDerivAt x
  · exact (Polynomial.continuous _).intervalIntegrable _ _

lemma legendre_orth_pair {n m : ℕ} (hnm : n ≠ m) :
    ∫ t in (-1 : ℝ)..1, (legendre n).eval t * (legendre m).eval t = 0 := by
  set G : ℝ[X] := (1 - X ^ 2) * derivative (legendre n) * legendre m -
    (1 - X ^ 2) * derivative (legendre m) * legendre n
  have hG : derivative G =
      C ((m : ℝ) * ((m : ℝ) + 1) - (n : ℝ) * ((n : ℝ) + 1)) * (legendre n * legendre m) := by
    apply Polynomial.funext
    intro x
    have hn := legendre_ode n x
    have hm := legendre_ode m x
    simp only [G, derivative_mul, derivative_sub, derivative_one, derivative_X_pow, eval_add,
      eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_C, zero_sub, eval_neg]
    push_cast
    linear_combination (legendre m).eval x * hn - (legendre n).eval x * hm
  have h1 := integral_poly_eval_derivative G (-1) 1
  have hGe : ∀ x : ℝ, x ^ 2 = 1 → G.eval x = 0 := by
    intro x hx
    simp [G, hx]
  rw [hGe 1 (by norm_num), hGe (-1) (by norm_num), hG] at h1
  simp only [eval_mul, eval_C, sub_self] at h1
  rw [intervalIntegral.integral_const_mul] at h1
  have hc : (m : ℝ) * ((m : ℝ) + 1) - (n : ℝ) * ((n : ℝ) + 1) ≠ 0 := by
    intro h
    have : ((m : ℝ) - n) * ((m : ℝ) + n + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact hnm (by exact_mod_cast (sub_eq_zero.1 h').symm)
    · have : (0 : ℝ) < m + n + 1 := by positivity
      linarith
  exact (mul_eq_zero.1 h1).resolve_left hc

/-- Every polynomial of degree `< n` is a combination of `P_0, …, P_{n-1}`. -/
lemma exists_legendre_combination (n : ℕ) (p : ℝ[X]) (hp : p.degree < n) :
    ∃ c : ℕ → ℝ, p = ∑ k ∈ Finset.range n, C (c k) * legendre k := by
  induction n generalizing p with
  | zero =>
    refine ⟨0, ?_⟩
    simp only [CharP.cast_eq_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot] at hp
    simp [hp]
  | succ n ih =>
    obtain ⟨dn, ln⟩ := legendre_natDegree_and_lc n
    set a := p.coeff n / (legendre n).leadingCoeff
    have hq : (p - C a * legendre n).degree < n := by
      rw [degree_lt_iff_coeff_zero]
      intro m hm
      rw [coeff_sub, coeff_C_mul]
      rcases lt_or_eq_of_le hm with hm | rfl
      · have h1 : p.coeff m = 0 := by
          apply coeff_eq_zero_of_degree_lt
          refine lt_of_lt_of_le hp ?_
          exact_mod_cast hm
        have h2 : (legendre n).coeff m = 0 := by
          apply coeff_eq_zero_of_natDegree_lt; omega
        simp [h1, h2]
      · have : (legendre n).coeff n = (legendre n).leadingCoeff := by
          rw [leadingCoeff, dn]
        rw [this]
        simp only [a]
        field_simp
        ring
    obtain ⟨c, hc⟩ := ih _ hq
    refine ⟨Function.update c n a, ?_⟩
    rw [Finset.sum_range_succ, Function.update_self]
    have : ∑ k ∈ Finset.range n, C (Function.update c n a k) * legendre k =
        ∑ k ∈ Finset.range n, C (c k) * legendre k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Function.update_of_ne (Finset.mem_range.1 hk).ne]
    rw [this, ← hc]
    ring

lemma legendre_orthogonal_aux (n : ℕ) (p : Polynomial ℝ)
    (hp : p.degree < n) :
    (∫ t in (-1 : ℝ)..1, (legendre n).eval t * p.eval t) = 0 := by
  obtain ⟨c, rfl⟩ := exists_legendre_combination n p hp
  simp only [eval_finset_sum, eval_mul, eval_C, Finset.mul_sum]
  rw [intervalIntegral.integral_finset_sum]
  · refine Finset.sum_eq_zero fun k hk => ?_
    have := legendre_orth_pair (n := n) (m := k) (Finset.mem_range.1 hk).ne'
    simp_rw [mul_left_comm _ (c k)]
    rw [intervalIntegral.integral_const_mul, this, mul_zero]
  · intro k _
    exact (by fun_prop : Continuous fun t => (legendre n).eval t * (c k * (legendre k).eval t)).intervalIntegrable _ _


/-! ### Christoffel–Darboux identities -/

/-- Christoffel–Darboux identity. -/
lemma legendre_cd (n : ℕ) (x y : ℝ) :
    ((n : ℝ) + 1) * ((legendre (n + 1)).eval x * (legendre n).eval y -
      (legendre n).eval x * (legendre (n + 1)).eval y) =
      (x - y) * ∑ k ∈ Finset.range (n + 1),
        (2 * (k : ℝ) + 1) * (legendre k).eval x * (legendre k).eval y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ← ih]
    have hx := legendre_eval_rec n x
    have hy := legendre_eval_rec n y
    push_cast
    linear_combination (legendre (n + 1)).eval y * hx - (legendre (n + 1)).eval x * hy

/-- Confluent Christoffel–Darboux identity. -/
lemma legendre_cd_confluent (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 1) * ((legendre (n + 1)).derivative.eval x * (legendre n).eval x -
      (legendre n).derivative.eval x * (legendre (n + 1)).eval x) =
      ∑ k ∈ Finset.range (n + 1), (2 * (k : ℝ) + 1) * (legendre k).eval x ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hx := legendre_eval_rec n x
    have hd := legendre_deriv_rec n x
    push_cast
    linear_combination (legendre (n + 1)).eval x * hd -
      (legendre (n + 1)).derivative.eval x * hx

lemma legendre_cd_sum_pos (n : ℕ) (x : ℝ) :
    0 < ∑ k ∈ Finset.range (n + 1), (2 * (k : ℝ) + 1) * (legendre k).eval x ^ 2 := by
  rw [Finset.sum_range_succ']
  have : 0 ≤ ∑ k ∈ Finset.range n, (2 * ((k + 1 : ℕ) : ℝ) + 1) * (legendre (k + 1)).eval x ^ 2 :=
    Finset.sum_nonneg fun k _ => by positivity
  simp only [legendre_zero', eval_one, CharP.cast_eq_zero] at *
  linarith

/-- At a root of `P_{n+1}` the derivative and `P_n` have the same (nonzero) sign. -/
lemma legendre_deriv_mul_prev_pos {n : ℕ} {x : ℝ} (hx : (legendre (n + 1)).eval x = 0) :
    0 < (legendre (n + 1)).derivative.eval x * (legendre n).eval x := by
  have h := legendre_cd_confluent n x
  rw [hx, mul_zero, sub_zero] at h
  have hp := legendre_cd_sum_pos n x
  rw [← h] at hp
  have : (0 : ℝ) < n + 1 := by positivity
  exact pos_of_mul_pos_right hp this.le

lemma legendre_deriv_ne_zero_of_root {n : ℕ} {x : ℝ} (hx : (legendre n).eval x = 0) :
    (legendre n).derivative.eval x ≠ 0 := by
  match n with
  | 0 => simp at hx
  | m + 1 =>
    intro h
    have := legendre_deriv_mul_prev_pos hx
    rw [h, zero_mul] at this
    exact lt_irrefl _ this


/-! ### Existence of the roots -/

/-- A polynomial that is nonnegative on `(-1,1)` and nonzero has positive integral. -/
lemma poly_integral_pos {g : ℝ[X]} (hg : g ≠ 0) (hnn : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 ≤ g.eval x) :
    0 < ∫ t in (-1 : ℝ)..1, g.eval t := by
  have hcl : Set.Icc (-1 : ℝ) 1 ⊆ {x | 0 ≤ g.eval x} := by
    rw [← closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact (isClosed_le continuous_const g.continuous).closure_subset_iff.2 hnn
  have hex : ∃ c ∈ Set.Ioo (-1 : ℝ) 1, g.eval c ≠ 0 := by
    by_contra H
    push_neg at H
    apply hg
    apply eq_zero_of_infinite_isRoot
    exact Set.Infinite.mono (fun c hc => H c hc) (Set.Ioo_infinite (by norm_num))
  obtain ⟨c, hc, hc0⟩ := hex
  refine intervalIntegral.integral_pos (by norm_num) g.continuous.continuousOn
    (fun x hx => hcl ⟨hx.1.le, hx.2⟩) ⟨c, Set.Ioo_subset_Icc_self hc, ?_⟩
  exact lt_of_le_of_ne (hnn c hc) (Ne.symm hc0)

lemma legendre_exists_root_finset (n : ℕ) :
    ∃ T : Finset ℝ, T.card = n ∧
      ∀ y ∈ T, y ∈ Set.Ioo (-1 : ℝ) 1 ∧ (legendre n).eval y = 0 := by
  classical
  set p := legendre n with hpdef
  have hp0 : p ≠ 0 := legendre_ne_zero n
  set s : Multiset ℝ := p.roots.filter (fun y => y ∈ Set.Ioo (-1 : ℝ) 1) with hs
  set T := s.toFinset with hT
  set O := T.filter (fun y => Odd (s.count y)) with hO
  set q : ℝ[X] := ∏ y ∈ O, (X - C y) with hq
  set Q : ℝ[X] := (s.map (fun a => X - C a)).prod with hQ
  have hQdvd : Q ∣ p := (Multiset.prod_X_sub_C_dvd_iff_le_roots hp0 s).2 (Multiset.filter_le _ _)
  obtain ⟨h, hph⟩ := hQdvd
  have hh : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, h.eval y ≠ 0 := by
    intro y hy hy0
    obtain ⟨h', rfl⟩ := (dvd_iff_isRoot).2 hy0
    have hd : ((y ::ₘ s).map (fun a => X - C a)).prod ∣ p :=
      ⟨h', by rw [hph, Multiset.map_cons, Multiset.prod_cons]; ring⟩
    have hle := (Multiset.prod_X_sub_C_dvd_iff_le_roots hp0 _).1 hd
    have h1 := Multiset.count_le_of_le y hle
    rw [Multiset.count_cons_self] at h1
    have h2 : s.count y = p.roots.count y := Multiset.count_filter_of_pos hy
    omega
  have h00 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have hsign : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 < h.eval x * h.eval 0 := by
    intro x hx
    by_contra hneg
    push_neg at hneg
    have hmem : (0 : ℝ) ∈ Set.uIcc (h.eval x) (h.eval 0) := by
      rw [Set.mem_uIcc]
      rcases le_total 0 (h.eval x) with h1 | h1
      · right
        refine ⟨?_, h1⟩
        by_contra h2; push_neg at h2
        have : 0 < h.eval x := lt_of_le_of_ne h1 (Ne.symm (hh x hx))
        nlinarith
      · left
        refine ⟨h1, ?_⟩
        by_contra h2; push_neg at h2
        have : h.eval x < 0 := lt_of_le_of_ne h1 (hh x hx)
        nlinarith
    obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc h.continuous.continuousOn hmem
    exact hh z (Set.ordConnected_Ioo.uIcc_subset hx h00 hz) hz0
  have hQq : ∀ x : ℝ, 0 ≤ Q.eval x * q.eval x := by
    intro x
    have e1 : Q.eval x = ∏ y ∈ T, (x - y) ^ (s.count y) := by
      rw [hQ, eval_multiset_prod, Multiset.map_map]
      rw [Finset.prod_multiset_map_count]
      exact Finset.prod_congr rfl fun y _ => by simp
    have e2 : q.eval x = ∏ y ∈ T, (if Odd (s.count y) then (x - y) else 1) := by
      rw [hq, eval_prod, hO, Finset.prod_filter]
      simp
    rw [e1, e2, ← Finset.prod_mul_distrib]
    refine Finset.prod_nonneg fun y _ => ?_
    split_ifs with hodd
    · rw [← pow_succ]
      exact (hodd.add_one).pow_nonneg _
    · rw [mul_one]
      exact (Nat.not_odd_iff_even.1 hodd).pow_nonneg _
  set g : ℝ[X] := C (h.eval 0) * p * q with hg
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.2 fun y _ => X_sub_C_ne_zero y
  have hg0 : g ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ hp0) hq0
    exact C_ne_zero.2 (hh 0 h00)
  have hgnn : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 ≤ g.eval x := by
    intro x hx
    have := mul_nonneg (hsign x hx).le (hQq x)
    rw [hg, hph]
    simp only [eval_mul, eval_C]
    nlinarith [this]
  have hpos := poly_integral_pos hg0 hgnn
  have hOcard : n ≤ O.card := by
    by_contra hlt
    push_neg at hlt
    have hdeg : q.degree < n := by
      rw [hq, degree_prod]
      simp only [degree_X_sub_C, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hlt
    have h0 := legendre_orthogonal_aux n q hdeg
    have : ∫ t in (-1 : ℝ)..1, g.eval t =
        h.eval 0 * ∫ t in (-1 : ℝ)..1, (legendre n).eval t * q.eval t := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext t
      simp only [hg, eval_mul, eval_C, hpdef]; ring
    rw [this, h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have hTle : T.card ≤ n := by
    calc T.card ≤ Multiset.card s := Multiset.toFinset_card_le _
      _ ≤ Multiset.card p.roots := Multiset.card_le_card (Multiset.filter_le _ _)
      _ ≤ p.natDegree := card_roots' p
      _ = n := (legendre_natDegree_and_lc n).1
  have hOT : O.card ≤ T.card := Finset.card_filter_le _ _
  refine ⟨T, by omega, fun y hy => ?_⟩
  rw [hT, Multiset.mem_toFinset, hs, Multiset.mem_filter, mem_roots hp0] at hy
  exact ⟨hy.2, hy.1⟩


/-! ### Quadrature weights and exactness -/

lemma integral_legendre (k : ℕ) :
    ∫ t in (-1 : ℝ)..1, (legendre k).eval t = if k = 0 then 2 else 0 := by
  split_ifs with hk
  · subst hk; norm_num
  · have := legendre_orthogonal_aux k 1 (by
      rw [degree_one]; exact_mod_cast Nat.pos_of_ne_zero hk)
    simpa using this

/-- Quotient of `P_{m+1}` by a root factor, scaled, is an explicit Legendre combination. -/
lemma legendre_quotient_eq {m : ℕ} {a : ℝ} (ha : (legendre (m + 1)).eval a = 0) :
    C (((m : ℝ) + 1) * (legendre m).eval a) * (legendre (m + 1) /ₘ (X - C a)) =
      ∑ k ∈ Finset.range (m + 1), C ((2 * (k : ℝ) + 1) * (legendre k).eval a) * legendre k := by
  have hfac : (X - C a) * (legendre (m + 1) /ₘ (X - C a)) = legendre (m + 1) :=
    mul_divByMonic_eq_iff_isRoot.2 ha
  have key : (X - C a) * (C (((m : ℝ) + 1) * (legendre m).eval a) *
      (legendre (m + 1) /ₘ (X - C a)) - ∑ k ∈ Finset.range (m + 1),
        C ((2 * (k : ℝ) + 1) * (legendre k).eval a) * legendre k) = 0 := by
    apply Polynomial.funext
    intro t
    have hcd := legendre_cd m t a
    have hf := congrArg (eval t) hfac
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hf
    rw [ha, mul_zero, sub_zero] at hcd
    simp only [eval_mul, eval_sub, eval_X, eval_C, eval_finset_sum, eval_zero]
    rw [← hf] at hcd
    have : ∑ k ∈ Finset.range (m + 1), (2 * (k : ℝ) + 1) * (legendre k).eval a * (legendre k).eval t
        = ∑ k ∈ Finset.range (m + 1), (2 * (k : ℝ) + 1) * (legendre k).eval t * (legendre k).eval a :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    linear_combination hcd
  rcases mul_eq_zero.1 key with h | h
  · exact absurd h (X_sub_C_ne_zero a)
  · exact sub_eq_zero.1 h

lemma integral_legendre_quotient {m : ℕ} {a : ℝ} (ha : (legendre (m + 1)).eval a = 0) :
    ((m : ℝ) + 1) * (legendre m).eval a *
      ∫ t in (-1 : ℝ)..1, (legendre (m + 1) /ₘ (X - C a)).eval t = 2 := by
  have h := congrArg (fun p : ℝ[X] => ∫ t in (-1 : ℝ)..1, p.eval t) (legendre_quotient_eq ha)
  simp only [eval_mul, eval_C, eval_finset_sum] at h
  rw [intervalIntegral.integral_const_mul] at h
  rw [h, intervalIntegral.integral_finset_sum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_legendre]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; simp at h
  · intro k _
    exact (by fun_prop : Continuous fun t => (2 * (k : ℝ) + 1) * (legendre k).eval a *
      (legendre k).eval t).intervalIntegrable _ _

/-- Exactness of the rule for polynomials of degree `< n`. -/
lemma gauss_exact_low {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ}
    (hx : IsGaussNodes x) (r : Polynomial ℝ) (hr : r.degree < n) :
    (∫ t in (-1 : ℝ)..1, r.eval t) = gaussSum x r.eval := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set P := legendre (m + 1)
  have hroot : ∀ i, P.eval (x i) = 0 := fun i => (hx.2 i).2
  have hd : ∀ i, P.derivative.eval (x i) ≠ 0 := fun i => legendre_deriv_ne_zero_of_root (hroot i)
  set Q : Fin (m + 1) → ℝ[X] := fun i => P /ₘ (X - C (x i))
  have hfac : ∀ i, (X - C (x i)) * Q i = P := fun i => mul_divByMonic_eq_iff_isRoot.2 (hroot i)
  have hQdeg : ∀ i, (Q i).degree < (m + 1 : ℕ) := by
    intro i
    have h1 : (Q i).natDegree = m := by
      simp only [Q, P]
      rw [natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C,
        (legendre_natDegree_and_lc _).1]
      rfl
    exact lt_of_le_of_lt degree_le_natDegree (by rw [h1]; exact_mod_cast Nat.lt_succ_self m)
  have hQeval : ∀ i j, (Q i).eval (x j) = if i = j then P.derivative.eval (x i) else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      have := congrArg (fun p => (derivative p).eval (x i)) (hfac i)
      simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
        eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at this
      exact this
    · have := congrArg (eval (x j)) (hfac i)
      simp only [eval_mul, eval_sub, eval_X, eval_C] at this
      rw [hroot j] at this
      have hne : x j - x i ≠ 0 := sub_ne_zero.2 (fun h => hij (hx.1 h).symm)
      exact (mul_eq_zero.1 this).resolve_left hne
  -- interpolation
  have hinterp : r = ∑ i, C (r.eval (x i) / P.derivative.eval (x i)) * Q i := by
    apply Polynomial.eq_of_degree_sub_lt_of_eval_index_eq (s := Finset.univ) (v := x)
    · exact hx.1.injOn
    · rw [Finset.card_univ, Fintype.card_fin]
      rw [← mem_degreeLT]
      refine Submodule.sub_mem _ (mem_degreeLT.2 hr) (Submodule.sum_mem _ fun i _ => ?_)
      rw [← smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (mem_degreeLT.2 (hQdeg i))
    · intro j _
      rw [eval_finset_sum]
      simp only [eval_mul, eval_C, hQeval]
      rw [Finset.sum_eq_single j]
      · simp only [if_true]; field_simp [hd j]
      · intro i _ hij; simp [hij]
      · intro h; simp at h
  -- integral of each quotient
  have hQint : ∀ i, ∫ t in (-1 : ℝ)..1, (Q i).eval t =
      2 / (((m : ℝ) + 1) * (legendre m).eval (x i)) := by
    intro i
    have h := integral_legendre_quotient (m := m) (hroot i)
    have hne : ((m : ℝ) + 1) * (legendre m).eval (x i) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h; norm_num at h
    rw [eq_div_iff hne, ← h]; ring
  have hw : ∀ i, gaussWeight (m + 1) (x i) =
      2 / (P.derivative.eval (x i) * (((m : ℝ) + 1) * (legendre m).eval (x i))) := by
    intro i
    have h4 := legendre_d4 m (x i)
    rw [hroot i, mul_zero, sub_zero] at h4
    unfold gaussWeight
    rw [← h4]
    congr 1; ring
  conv_lhs => rw [hinterp]
  simp only [eval_finset_sum, eval_mul, eval_C]
  rw [intervalIntegral.integral_finset_sum]
  · unfold gaussSum
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, hQint, hw]
    field_simp
  · intro i _
    exact (by fun_prop : Continuous fun t => r.eval (x i) / P.derivative.eval (x i) *
      (Q i).eval t).intervalIntegrable _ _

theorem legendre_natDegree (n : ℕ) :
    (legendre n).natDegree = n :=
  (legendre_natDegree_and_lc n).1

theorem legendre_orthogonal (n : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree < n) :
    (∫ t in (-1 : ℝ)..1, (legendre n).eval t * p.eval t) = 0 :=
  legendre_orthogonal_aux n p (lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hp))

theorem legendre_roots (n : ℕ) :
    ∃ x : Fin n → ℝ, IsGaussNodes x ∧
      ∀ i, (legendre n).derivative.eval (x i) ≠ 0 := by
  obtain ⟨T, hT, hmem⟩ := legendre_exists_root_finset n
  let x : Fin n → ℝ := fun i => (T.equivFin.symm (Fin.cast hT.symm i) : ℝ)
  have hxmem : ∀ i, x i ∈ T := fun i => (T.equivFin.symm (Fin.cast hT.symm i)).2
  refine ⟨x, ⟨?_, fun i => hmem _ (hxmem i)⟩, fun i =>
    legendre_deriv_ne_zero_of_root (hmem _ (hxmem i)).2⟩
  intro i j hij
  have := T.equivFin.symm.injective (Subtype.ext hij)
  exact Fin.cast_injective _ this

theorem gaussWeight_pos {n : ℕ} {x : Fin n → ℝ}
    (hx : IsGaussNodes x) (i : Fin n) :
    0 < gaussWeight n (x i) := by
  obtain ⟨h1, h2⟩ := hx.2 i
  have hd := legendre_deriv_ne_zero_of_root h2
  have : 0 < 1 - x i ^ 2 := by nlinarith [h1.1, h1.2]
  unfold gaussWeight
  positivity

theorem gauss_exact {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ}
    (hx : IsGaussNodes x) (p : Polynomial ℝ)
    (hp : p.natDegree < 2 * n) :
    (∫ t in (-1 : ℝ)..1, p.eval t) = gaussSum x p.eval := by
  set P := legendre n
  obtain ⟨dP, lP⟩ := legendre_natDegree_and_lc n
  set M : ℝ[X] := C (P.leadingCoeff⁻¹) * P
  have hM : M.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ lP.ne')
  have hMdeg : M.natDegree = n := by
    simp only [M]; rw [natDegree_C_mul (inv_ne_zero lP.ne'), dP]
  have hdecomp := modByMonic_add_div p M
  set R := p %ₘ M
  set D := p /ₘ M
  have hR : R.degree < n := by
    have := degree_modByMonic_lt p hM
    rwa [degree_eq_natDegree hM.ne_zero, hMdeg] at this
  have hD : D.degree < n := by
    refine lt_of_le_of_lt degree_le_natDegree ?_
    simp only [D]; rw [natDegree_divByMonic _ hM, hMdeg]
    exact_mod_cast (by omega : p.natDegree - n < n)
  have hMroot : ∀ i, M.eval (x i) = 0 := by
    intro i; simp [M, (hx.2 i).2, P]
  have hint : ∫ t in (-1 : ℝ)..1, (M * D).eval t = 0 := by
    simp only [M, eval_mul, eval_C]
    have := legendre_orthogonal_aux n D hD
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul, this, mul_zero]
  rw [← hdecomp]
  simp only [eval_add]
  rw [intervalIntegral.integral_add ((Polynomial.continuous _).intervalIntegrable _ _)
    ((Polynomial.continuous _).intervalIntegrable _ _), hint, add_zero,
    gauss_exact_low hn hx R hR]
  unfold gaussSum
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [hMroot i]


theorem gaussWeight_sum {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ}
    (hx : IsGaussNodes x) :
    (∑ i, gaussWeight n (x i)) = 2 := by
  have h := gauss_exact hn hx 1 (by simp; omega)
  simp only [eval_one, intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
  unfold gaussSum at h
  simp only [mul_one] at h
  linarith

end Intgrl
