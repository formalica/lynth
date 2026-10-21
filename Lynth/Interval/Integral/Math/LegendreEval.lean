import Lynth.Interval.Integral.Math.Legendre
import Lynth.Interval.Integral.Math.LegendreAsymp

/-!
P1: fast evaluation and small roundoff bounds. Send with IntgrlDefs.lean.
References: Johansson--Mezzarobba, arXiv:1802.03948, Propositions 3, 5,
and the expansions at zero, one, and large degree.

These contracts allow fixed-point evaluation, delayed scalar divisions,
and rectangular splitting. They do not mandate interval recurrence.
Series here evaluate a known polynomial; the integration rule is Gauss.
-/

noncomputable section

open scoped BigOperators
open Polynomial Finset

namespace Intgrl

/-! ### Auxiliary bounds and identities -/

lemma legendre_eval_neg_one (n : ℕ) : (legendre n).eval (-1) = (-1 : ℝ) ^ n := by
  rw [legendre_parity', legendre_eval_one, mul_one]

/-- `|P_n(x)| ≤ 1` on `[-1, 1]`. -/
lemma legendre_abs_le_one (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(legendre n).eval x| ≤ 1 := by
  match n with
  | 0 => simp
  | m + 1 =>
    set P := legendre (m + 1)
    set N : ℝ := ((m : ℝ) + 1) * ((m : ℝ) + 2)
    have hN : 0 < N := by positivity
    set F : ℝ[X] := P ^ 2 + C N⁻¹ * (1 - X ^ 2) * (derivative P) ^ 2
    have hF' : ∀ y, (derivative F).eval y = 2 * y * (derivative P).eval y ^ 2 / N := by
      intro y
      have h := legendre_ode (m + 1) y
      simp only [F, P, derivative_add, derivative_mul, derivative_pow, derivative_C, derivative_sub,
        derivative_one, derivative_X, eval_add, eval_mul, eval_pow, eval_C, eval_sub,
        eval_one, eval_X, zero_mul, zero_add, zero_sub, eval_neg]
      simp only [N]
      push_cast at h ⊢
      field_simp
      linear_combination ((derivative (legendre (m + 1))).eval y) * h
    have hcont : Continuous fun y => F.eval y := F.continuous
    have hderiv : ∀ y, deriv (fun y => F.eval y) y = 2 * y * (derivative P).eval y ^ 2 / N :=
      fun y => by rw [Polynomial.deriv, hF']
    have hdiff : ∀ s, DifferentiableOn ℝ (fun y => F.eval y) s :=
      fun s => F.differentiable.differentiableOn
    have hF1 : F.eval 1 = 1 := by simp [F, P, legendre_eval_one]
    have hFm1 : F.eval (-1) = 1 := by
      simp [F, P, legendre_eval_neg_one]
      exact neg_one_pow_eq_or ℝ (m + 1)
    have hFx : F.eval x ≤ 1 := by
      rcases le_total 0 x with h0 | h0
      · have hmono : MonotoneOn (fun y => F.eval y) (Set.Icc 0 1) := by
          apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hcont.continuousOn (hdiff _)
          intro y hy
          rw [interior_Icc] at hy
          rw [hderiv]
          have := hy.1
          positivity
        have := hmono ⟨h0, hx.2⟩ ⟨zero_le_one, le_rfl⟩ hx.2
        simpa [hF1] using this
      · have hanti : AntitoneOn (fun y => F.eval y) (Set.Icc (-1) 0) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc (-1) 0) hcont.continuousOn (hdiff _)
          intro y hy
          rw [interior_Icc] at hy
          rw [hderiv]
          have h1 : 2 * y * (derivative P).eval y ^ 2 ≤ 0 := by
            have := hy.2
            have : 0 ≤ (derivative P).eval y ^ 2 := sq_nonneg _
            nlinarith
          exact div_nonpos_of_nonpos_of_nonneg h1 hN.le
        have := hanti ⟨le_rfl, by linarith [hx.1]⟩ ⟨hx.1, h0⟩ hx.1
        simpa [hFm1] using this
    have hPF : P.eval x ^ 2 ≤ F.eval x := by
      have h1 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
      have : 0 ≤ N⁻¹ * (1 - x ^ 2) * (derivative P).eval x ^ 2 := by positivity
      simp only [F, eval_add, eval_mul, eval_pow, eval_C, eval_sub, eval_one, eval_X]
      linarith
    have : P.eval x ^ 2 ≤ 1 := hPF.trans hFx
    exact (sq_le_one_iff_abs_le_one _).1 this

lemma legendre_d1_poly (n : ℕ) :
    derivative (legendre (n + 2)) - derivative (legendre n) =
      C (2 * (n : ℝ) + 3) * legendre (n + 1) := by
  apply Polynomial.funext; intro x
  simpa using legendre_d1 n x

lemma legendre_d1_second (n : ℕ) (x : ℝ) :
    (legendre (n + 2)).derivative.derivative.eval x - (legendre n).derivative.derivative.eval x =
      (2 * (n : ℝ) + 3) * (legendre (n + 1)).derivative.eval x := by
  have := congrArg (fun p => (derivative p).eval x) (legendre_d1_poly n)
  simpa using this

/-- `P_n(1 + 2y)` as a polynomial in `y`. -/
def legendreShift (n : ℕ) : ℝ[X] := (legendre n).comp (C 2 * X + C 1)

lemma legendreShift_eval (n : ℕ) (y : ℝ) :
    (legendreShift n).eval y = (legendre n).eval (2 * y + 1) := by
  simp [legendreShift]

lemma legendreShift_ode (n : ℕ) :
    X * (1 + X) * derivative (derivative (legendreShift n)) +
      (1 + C 2 * X) * derivative (legendreShift n) =
      C ((n : ℝ) * ((n : ℝ) + 1)) * legendreShift n := by
  apply Polynomial.funext
  intro y
  have h := legendre_ode n (2 * y + 1)
  simp only [legendreShift, derivative_comp, derivative_add, derivative_mul, derivative_C,
    derivative_X, zero_mul, zero_add, mul_one, add_zero, eval_add, eval_mul, eval_X, eval_C,
    eval_one, eval_comp]
  linear_combination (-1 : ℝ) * h

lemma legendreShift_coeff_rec (n k : ℕ) :
    ((k : ℝ) + 1) ^ 2 * (legendreShift n).coeff (k + 1) =
      ((n : ℝ) - k) * ((n : ℝ) + k + 1) * (legendreShift n).coeff k := by
  have h := congrArg (fun p => p.coeff k) (legendreShift_ode n)
  set Y := legendreShift n
  have e : X * (1 + X) * derivative (derivative Y) + (1 + C 2 * X) * derivative Y =
      X * derivative (derivative Y) + X * (X * derivative (derivative Y)) + derivative Y +
        C 2 * (X * derivative Y) := by ring
  rw [e] at h
  rcases k with _ | _ | j
  · simp only [coeff_add, coeff_X_mul_zero, coeff_C_mul, coeff_derivative] at h
    push_cast at h ⊢
    linear_combination h
  · simp only [coeff_add, coeff_X_mul, coeff_X_mul_zero, coeff_C_mul, coeff_derivative] at h
    push_cast at h ⊢
    linear_combination h
  · simp only [coeff_add, coeff_X_mul, coeff_C_mul, coeff_derivative] at h
    push_cast at h ⊢
    linear_combination h

/-- Coefficient of the expansion at one. -/
def atOneCoeff (n k : ℕ) : ℝ := (n.choose k : ℝ) * ((n + k).choose k : ℝ)

lemma atOneCoeff_rec (n k : ℕ) :
    ((k : ℝ) + 1) ^ 2 * atOneCoeff n (k + 1) =
      ((n : ℝ) - k) * ((n : ℝ) + k + 1) * atOneCoeff n k := by
  unfold atOneCoeff
  have h1 : (n.choose (k + 1) : ℝ) * ((k : ℝ) + 1) = (n.choose k : ℝ) * ((n - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  have h2 : ((n + (k + 1)).choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
      ((n + k).choose k : ℝ) * ((n : ℝ) + k + 1) := by
    have := Nat.add_one_mul_choose_eq (n + k) k
    rw [show n + (k + 1) = n + k + 1 by ring]
    have h := congrArg (fun m : ℕ => (m : ℝ)) this
    push_cast at h
    linear_combination -h
  rcases le_or_gt k n with hk | hk
  · rw [Nat.cast_sub hk] at h1
    linear_combination ((n + (k + 1)).choose (k + 1) : ℝ) * ((k : ℝ) + 1) * h1 +
      (n.choose k : ℝ) * ((n : ℝ) - k) * h2
  · have h0 : n.choose k = 0 := Nat.choose_eq_zero_of_lt hk
    have h0' : n.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0, h0']

lemma legendreShift_coeff (n k : ℕ) : (legendreShift n).coeff k = atOneCoeff n k := by
  induction k with
  | zero =>
    rw [coeff_zero_eq_eval_zero, legendreShift_eval]
    simp [atOneCoeff, legendre_eval_one]
  | succ k ih =>
    have h1 := legendreShift_coeff_rec n k
    have h2 := atOneCoeff_rec n k
    rw [ih] at h1
    have : ((k : ℝ) + 1) ^ 2 ≠ 0 := by positivity
    apply mul_left_cancel₀ this
    rw [h1, h2]

lemma legendre_ode_poly (n : ℕ) :
    derivative (derivative (legendre n)) - X * (X * derivative (derivative (legendre n)))
      - C 2 * (X * derivative (legendre n)) + C ((n : ℝ) * ((n : ℝ) + 1)) * legendre n = 0 := by
  apply Polynomial.funext
  intro x
  have h := legendre_ode n x
  simp only [eval_add, eval_sub, eval_mul, eval_X, eval_C, eval_zero]
  linear_combination h

lemma legendre_coeff_rec (n j : ℕ) :
    ((j : ℝ) + 2) * ((j : ℝ) + 1) * (legendre n).coeff (j + 2) =
      ((j : ℝ) - n) * ((j : ℝ) + n + 1) * (legendre n).coeff j := by
  have h := congrArg (fun p => p.coeff j) (legendre_ode_poly n)
  simp only [coeff_zero] at h
  rcases j with _ | _ | j
  · simp only [coeff_add, coeff_sub, coeff_X_mul_zero, coeff_C_mul, coeff_derivative] at h
    push_cast at h ⊢
    linear_combination h
  · simp only [coeff_add, coeff_sub, coeff_X_mul, coeff_X_mul_zero, coeff_C_mul,
      coeff_derivative] at h
    push_cast at h ⊢
    linear_combination h
  · simp only [coeff_add, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_derivative] at h
    push_cast at h ⊢
    linear_combination h

lemma legendre_coeff_top (n : ℕ) :
    (legendre n).coeff n = ((2 * n).choose n : ℝ) / 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp
    | m + 2, ih =>
      rw [legendre_succ_succ, coeff_sub, mul_assoc, coeff_C_mul, coeff_C_mul,
        show m + 2 = (m + 1) + 1 from rfl, coeff_X_mul, ih (m + 1) (by omega),
        coeff_eq_zero_of_natDegree_lt (by rw [(legendre_natDegree_and_lc m).1]; omega)]
      have hc := Nat.succ_mul_centralBinom_succ (m + 1)
      rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hc
      have hc' : ((m : ℝ) + 2) * ((2 * (m + 2)).choose (m + 2) : ℝ) =
          2 * (2 * (m : ℝ) + 3) * ((2 * (m + 1)).choose (m + 1) : ℝ) := by
        have := congrArg (fun k : ℕ => (k : ℝ)) hc
        push_cast at this
        linear_combination this
      have : (m : ℝ) + 2 ≠ 0 := by positivity
      rw [show m + 1 + 1 = m + 2 from rfl]
      field_simp
      linear_combination (-2 * (2 : ℝ) ^ m) * hc'

/-- Coefficient of the expansion at zero. -/
def atZeroCoeff (n k : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ n * ((-1 : ℝ) ^ k * (n.choose k : ℝ) * ((2 * n - 2 * k).choose n : ℝ))

lemma atZeroCoeff_rec (j k : ℕ) :
    ((j : ℝ) + 2) * ((j : ℝ) + 1) * atZeroCoeff (j + 2 * k + 2) k =
      ((j : ℝ) - ((j + 2 * k + 2 : ℕ) : ℝ)) * ((j : ℝ) + ((j + 2 * k + 2 : ℕ) : ℝ) + 1) *
        atZeroCoeff (j + 2 * k + 2) (k + 1) := by
  have ha := Nat.choose_succ_right_eq (j + 2 * k + 2) k
  rw [show j + 2 * k + 2 - k = j + k + 2 by omega] at ha
  have hb1 := Nat.choose_mul_succ_eq (2 * j + 2 * k + 2) (j + 2 * k + 2)
  rw [show 2 * j + 2 * k + 2 + 1 - (j + 2 * k + 2) = j + 1 by omega,
    show 2 * j + 2 * k + 2 + 1 = 2 * j + 2 * k + 3 by ring] at hb1
  have hb2 := Nat.choose_mul_succ_eq (2 * j + 2 * k + 3) (j + 2 * k + 2)
  rw [show 2 * j + 2 * k + 3 + 1 - (j + 2 * k + 2) = j + 2 by omega,
    show 2 * j + 2 * k + 3 + 1 = 2 * j + 2 * k + 4 by ring] at hb2
  have ha' := congrArg (fun t : ℕ => (t : ℝ)) ha
  have hb1' := congrArg (fun t : ℕ => (t : ℝ)) hb1
  have hb2' := congrArg (fun t : ℕ => (t : ℝ)) hb2
  push_cast at ha' hb1' hb2'
  unfold atZeroCoeff
  rw [show 2 * (j + 2 * k + 2) - 2 * k = 2 * j + 2 * k + 4 by omega,
    show 2 * (j + 2 * k + 2) - 2 * (k + 1) = 2 * j + 2 * k + 2 by omega]
  push_cast
  linear_combination (2 : ℝ)⁻¹ ^ (j + 2 * k + 2) * (-1 : ℝ) ^ k *
    (-((j : ℝ) + 1) * ((j + 2 * k + 2).choose k : ℝ) * hb2'
      - (2 * (j : ℝ) + 2 * k + 4) * ((j + 2 * k + 2).choose k : ℝ) * hb1'
      - 2 * (2 * (j : ℝ) + 2 * k + 3) * ((2 * j + 2 * k + 2).choose (j + 2 * k + 2) : ℝ) * ha')

lemma legendre_coeff_formula (n k : ℕ) (hk : 2 * k ≤ n) :
    (legendre n).coeff (n - 2 * k) = atZeroCoeff n k := by
  induction k with
  | zero => simp [legendre_coeff_top, atZeroCoeff, div_eq_mul_inv, mul_comm]
  | succ k ih =>
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 * k + 2 := ⟨n - 2 * k - 2, by omega⟩
    have h1 := ih (by omega)
    rw [show j + 2 * k + 2 - 2 * k = j + 2 by omega] at h1
    have hrec := legendre_coeff_rec (j + 2 * k + 2) j
    have hz := atZeroCoeff_rec j k
    rw [h1] at hrec
    rw [show j + 2 * k + 2 - 2 * (k + 1) = j by omega]
    have hne : ((j : ℝ) - ((j + 2 * k + 2 : ℕ) : ℝ)) * ((j : ℝ) + ((j + 2 * k + 2 : ℕ) : ℝ) + 1) ≠ 0 := by
      push_cast
      apply mul_ne_zero <;> nlinarith
    apply mul_left_cancel₀ hne
    rw [← hrec, hz]

lemma legendre_coeff_odd (n k : ℕ) (hk : 2 * k + 1 ≤ n) :
    (legendre n).coeff (n - 2 * k - 1) = 0 := by
  induction k with
  | zero =>
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have hrec := legendre_coeff_rec (j + 1) j
    rw [coeff_eq_zero_of_natDegree_lt (p := legendre (j + 1)) (n := j + 2)
      (by rw [(legendre_natDegree_and_lc _).1]; omega), mul_zero] at hrec
    simp only [mul_zero, Nat.sub_zero, add_tsub_cancel_right]
    have hne : ((j : ℝ) - ((j + 1 : ℕ) : ℝ)) * ((j : ℝ) + ((j + 1 : ℕ) : ℝ) + 1) ≠ 0 := by
      push_cast; apply mul_ne_zero <;> nlinarith
    exact (mul_eq_zero.1 hrec.symm).resolve_left hne
  | succ k ih =>
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 * k + 3 := ⟨n - 2 * k - 3, by omega⟩
    have h1 := ih (by omega)
    rw [show j + 2 * k + 3 - 2 * k - 1 = j + 2 by omega] at h1
    have hrec := legendre_coeff_rec (j + 2 * k + 3) j
    rw [h1, mul_zero] at hrec
    rw [show j + 2 * k + 3 - 2 * (k + 1) - 1 = j by omega]
    have hne : ((j : ℝ) - ((j + 2 * k + 3 : ℕ) : ℝ)) * ((j : ℝ) + ((j + 2 * k + 3 : ℕ) : ℝ) + 1) ≠ 0 := by
      push_cast; apply mul_ne_zero <;> nlinarith
    exact (mul_eq_zero.1 hrec.symm).resolve_left hne

lemma legendre_eval_rec' (x : ℝ) (j : ℕ) :
    ((j : ℝ) + 1) * (legendre (j + 1)).eval x =
      (2 * (j : ℝ) + 1) * x * (legendre j).eval x - (j : ℝ) * (legendre (j - 1)).eval x := by
  rcases j with _ | j
  · simp
  · have := legendre_eval_rec j x
    simp only [Nat.add_sub_cancel]
    push_cast at this ⊢
    linear_combination this

/-- Convolution square of the Legendre values. -/
def legConv (x : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ antidiagonal N, (legendre q.1).eval x * (legendre q.2).eval x

lemma legConv_weighted (x : ℝ) (N : ℕ) :
    2 * ∑ q ∈ antidiagonal N, (q.2 : ℝ) * ((legendre q.1).eval x * (legendre q.2).eval x) =
      (N : ℝ) * legConv x N := by
  have hswap : ∑ q ∈ antidiagonal N, (q.1 : ℝ) * ((legendre q.1).eval x * (legendre q.2).eval x) =
      ∑ q ∈ antidiagonal N, (q.2 : ℝ) * ((legendre q.1).eval x * (legendre q.2).eval x) := by
    rw [← Nat.sum_antidiagonal_swap]
    refine sum_congr rfl fun q _ => ?_
    simp only [Prod.fst_swap, Prod.snd_swap]; ring
  have hsum : ∑ q ∈ antidiagonal N, ((q.1 : ℝ) + q.2) *
      ((legendre q.1).eval x * (legendre q.2).eval x) = (N : ℝ) * legConv x N := by
    unfold legConv
    rw [mul_sum]
    refine sum_congr rfl fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    rw [← hq]; push_cast; ring
  rw [← hsum, two_mul]
  conv_lhs => arg 1; rw [← hswap]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun q _ => by ring

lemma legConv_rec (x : ℝ) (N : ℕ) :
    legConv x (N + 2) = 2 * x * legConv x (N + 1) - legConv x N := by
  set p : ℕ → ℝ := fun j => (legendre j).eval x with hp
  have hR : ∀ j : ℕ, ((j : ℝ) + 1) * p (j + 1) = (2 * (j : ℝ) + 1) * x * p j - (j : ℝ) * p (j - 1) :=
    fun j => legendre_eval_rec' x j
  have hW := legConv_weighted x (N + 2)
  have hW1 := legConv_weighted x (N + 1)
  have hW0 := legConv_weighted x N
  -- shift the weighted sum at `N + 2`
  have h1 : ∑ q ∈ antidiagonal (N + 2), (q.2 : ℝ) * (p q.1 * p q.2) =
      x * ∑ q ∈ antidiagonal (N + 1), (2 * (q.2 : ℝ) + 1) * (p q.1 * p q.2) -
        ∑ q ∈ antidiagonal (N + 1), (q.2 : ℝ) * (p q.1 * p (q.2 - 1)) := by
    rw [Nat.sum_antidiagonal_succ']
    simp only [CharP.cast_eq_zero, zero_mul, zero_add, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun q _ => ?_
    have := hR q.2
    push_cast
    linear_combination p q.1 * this
  have h2 : ∑ q ∈ antidiagonal (N + 1), (q.2 : ℝ) * (p q.1 * p (q.2 - 1)) =
      ∑ q ∈ antidiagonal N, (q.2 : ℝ) * (p q.1 * p q.2) + legConv x N := by
    rw [Nat.sum_antidiagonal_succ']
    simp only [CharP.cast_eq_zero, zero_mul, zero_add, Nat.add_sub_cancel]
    unfold legConv
    rw [← sum_add_distrib]
    refine sum_congr rfl fun q _ => ?_
    push_cast; ring
  have h3 : ∑ q ∈ antidiagonal (N + 1), (2 * (q.2 : ℝ) + 1) * (p q.1 * p q.2) =
      2 * ∑ q ∈ antidiagonal (N + 1), (q.2 : ℝ) * (p q.1 * p q.2) + legConv x (N + 1) := by
    unfold legConv
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun q _ => by ring
  simp only [hp] at h1 h2 h3
  rw [h1, h3, h2] at hW
  have hN : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hN
  push_cast at hW hW1 hW0 ⊢
  linear_combination -hW + 2 * x * hW1 - hW0

/-- Weighted convolution used for the Green's function of the recurrence. -/
def legGreenAux (x : ℝ) (m N : ℕ) : ℝ :=
  ∑ q ∈ antidiagonal N, (legendre q.1).eval x * (legendre q.2).eval x / ((m : ℝ) + q.1)

lemma legGreenAux_rec (x : ℝ) {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ((m : ℝ) + N + 2) * legGreenAux x m (N + 2) =
      (2 * (m : ℝ) + 2 * N + 3) * x * legGreenAux x m (N + 1) -
        ((m : ℝ) + N + 1) * legGreenAux x m N := by
  set p : ℕ → ℝ := fun j => (legendre j).eval x with hp
  have hR : ∀ j : ℕ, ((j : ℝ) + 1) * p (j + 1) = (2 * (j : ℝ) + 1) * x * p j - (j : ℝ) * p (j - 1) :=
    fun j => legendre_eval_rec' x j
  have hpos : ∀ i : ℕ, (m : ℝ) + i ≠ 0 := fun i => by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    positivity
  have hc := legConv_rec x N
  -- three expansions
  have e2 : ((m : ℝ) + N + 2) * legGreenAux x m (N + 2) =
      ∑ q ∈ antidiagonal (N + 2), p q.1 * ((q.2 : ℝ) * p q.2) / ((m : ℝ) + q.1) +
        legConv x (N + 2) := by
    unfold legGreenAux legConv
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have h' : ((m : ℝ) + N + 2) = ((m : ℝ) + q.1) + q.2 := by
      rw [← Nat.cast_ofNat, show ((m : ℝ) + N + ((2 : ℕ) : ℝ)) = (m : ℝ) + ((N + 2 : ℕ) : ℝ) by
        push_cast; ring, ← hq]; push_cast; ring
    rw [h']
    field_simp [hpos q.1]
    ring
  have e2' : ∑ q ∈ antidiagonal (N + 2), p q.1 * ((q.2 : ℝ) * p q.2) / ((m : ℝ) + q.1) =
      ∑ q ∈ antidiagonal (N + 1), p q.1 * ((2 * (q.2 : ℝ) + 1) * x * p q.2 -
        (q.2 : ℝ) * p (q.2 - 1)) / ((m : ℝ) + q.1) := by
    rw [Nat.sum_antidiagonal_succ']
    simp only [CharP.cast_eq_zero, zero_mul, mul_zero, zero_div, zero_add]
    refine sum_congr rfl fun q _ => ?_
    rw [← hR q.2]; push_cast; ring
  have e1 : (2 * (m : ℝ) + 2 * N + 3) * x * legGreenAux x m (N + 1) =
      x * ∑ q ∈ antidiagonal (N + 1), p q.1 * ((2 * (q.2 : ℝ) + 1) * p q.2) / ((m : ℝ) + q.1) +
        2 * x * legConv x (N + 1) := by
    unfold legGreenAux legConv
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have h' : (2 * (m : ℝ) + 2 * N + 3) = 2 * ((m : ℝ) + q.1) + 2 * q.2 + 1 := by
      have : ((q.1 : ℝ) + q.2) = (N : ℝ) + 1 := by exact_mod_cast hq
      linarith
    rw [h']
    field_simp [hpos q.1]
    ring
  have e0 : ((m : ℝ) + N + 1) * legGreenAux x m N =
      ∑ q ∈ antidiagonal N, p q.1 * (((q.2 : ℝ) + 1) * p q.2) / ((m : ℝ) + q.1) +
        legConv x N := by
    unfold legGreenAux legConv
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have h' : ((m : ℝ) + N + 1) = ((m : ℝ) + q.1) + q.2 + 1 := by
      have : ((q.1 : ℝ) + q.2) = (N : ℝ) := by exact_mod_cast hq
      linarith
    rw [h']
    field_simp [hpos q.1]
    ring
  have e0' : ∑ q ∈ antidiagonal (N + 1), p q.1 * ((q.2 : ℝ) * p (q.2 - 1)) / ((m : ℝ) + q.1) =
      ∑ q ∈ antidiagonal N, p q.1 * (((q.2 : ℝ) + 1) * p q.2) / ((m : ℝ) + q.1) := by
    rw [Nat.sum_antidiagonal_succ']
    simp only [CharP.cast_eq_zero, zero_mul, mul_zero, zero_div, zero_add, Nat.add_sub_cancel]
    refine sum_congr rfl fun q _ => ?_
    push_cast; ring
  have split : ∑ q ∈ antidiagonal (N + 1), p q.1 * ((2 * (q.2 : ℝ) + 1) * x * p q.2 -
        (q.2 : ℝ) * p (q.2 - 1)) / ((m : ℝ) + q.1) =
      x * ∑ q ∈ antidiagonal (N + 1), p q.1 * ((2 * (q.2 : ℝ) + 1) * p q.2) / ((m : ℝ) + q.1) -
      ∑ q ∈ antidiagonal (N + 1), p q.1 * ((q.2 : ℝ) * p (q.2 - 1)) / ((m : ℝ) + q.1) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun q _ => by ring
  simp only [hp] at e2 e2' e1 e0 e0' split
  rw [e2, e1, e0, e2', split, e0', hc]
  ring

lemma legGreenAux_zero (x : ℝ) (m : ℕ) : legGreenAux x m 0 = 1 / (m : ℝ) := by
  simp [legGreenAux]

lemma legGreenAux_one (x : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ((m : ℝ) + 1) * legGreenAux x m 1 = (2 * (m : ℝ) + 1) * x * legGreenAux x m 0 := by
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold legGreenAux
  rw [Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, sum_singleton, sum_singleton]
  simp only [legendre_zero', legendre_one', eval_one, eval_X, zero_add, CharP.cast_eq_zero,
    add_zero, Nat.cast_one, mul_one, one_mul]
  field_simp
  ring

lemma legGreenAux_abs_le (x : ℝ) (hx : |x| ≤ 1) {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    |legGreenAux x m N| ≤ ∑ i ∈ range (N + 1), 1 / ((m : ℝ) + i) := by
  have hP : ∀ j, |(legendre j).eval x| ≤ 1 := fun j =>
    legendre_abs_le_one j ⟨by linarith [neg_abs_le x], le_trans (le_abs_self x) hx⟩
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold legGreenAux
  rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (legendre i).eval x *
    (legendre j).eval x / ((m : ℝ) + i))]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < m + i)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc _ ≤ 1 * 1 := mul_le_mul (hP _) (hP _) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Green's function of the Legendre recurrence: response at index `n` to a unit
perturbation injected at index `k`. -/
def legGreen (x : ℝ) (k n : ℕ) : ℝ :=
  if k ≤ n then (k : ℝ) * legGreenAux x k (n - k) else 0

lemma legGreen_self (x : ℝ) {k : ℕ} (hk : 1 ≤ k) : legGreen x k k = 1 := by
  have : (k : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ k := by exact_mod_cast hk
                           positivity
  simp [legGreen, legGreenAux_zero, this]

lemma legGreen_below (x : ℝ) {k n : ℕ} (h : n < k) : legGreen x k n = 0 := by
  simp [legGreen, show ¬ k ≤ n by omega]

lemma legGreen_rec (x : ℝ) {M j : ℕ} (hM : 1 ≤ M) (hMj : M ≤ j + 1) :
    ((j : ℝ) + 2) * legGreen x M (j + 2) =
      (2 * (j : ℝ) + 3) * x * legGreen x M (j + 1) - ((j : ℝ) + 1) * legGreen x M j := by
  rcases Nat.lt_or_ge j M with h | h
  · have hMe : M = j + 1 := by omega
    subst hMe
    rw [legGreen_below x (by omega : j < j + 1)]
    simp only [legGreen, show j + 1 ≤ j + 2 by omega, show j + 1 ≤ j + 1 from le_rfl, if_true,
      show j + 2 - (j + 1) = 1 by omega, Nat.sub_self]
    have h1 := legGreenAux_one x (m := j + 1) (by omega)
    push_cast at h1 ⊢
    linear_combination ((j : ℝ) + 1) * h1
  · obtain ⟨N, rfl⟩ : ∃ N, j = M + N := ⟨j - M, by omega⟩
    have hrec := legGreenAux_rec x hM N
    simp only [legGreen, show M ≤ M + N + 2 by omega, show M ≤ M + N + 1 by omega,
      show M ≤ M + N by omega, if_true, show M + N + 2 - M = N + 2 by omega,
      show M + N + 1 - M = N + 1 by omega, show M + N - M = N by omega]
    push_cast
    linear_combination (M : ℝ) * hrec

lemma legGreen_abs_le (x : ℝ) (hx : |x| ≤ 1) {M n : ℕ} (hM : 1 ≤ M) :
    |legGreen x M n| ≤
      if M ≤ n then (M : ℝ) * ∑ i ∈ range (n - M + 1), 1 / ((M : ℝ) + i) else 0 := by
  unfold legGreen
  split_ifs with h
  · rw [abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (legGreenAux_abs_le x hx hM _) (Nat.cast_nonneg _)
  · simp

lemma legGreen_bound_sum (n : ℕ) :
    ∑ m ∈ range n, (if m + 1 ≤ n then ((m + 1 : ℕ) : ℝ) *
      ∑ i ∈ range (n - (m + 1) + 1), 1 / (((m + 1 : ℕ) : ℝ) + i) else 0) =
      (n : ℝ) * ((n : ℝ) + 3) / 4 := by
  have htri : ∀ n : ℕ, ∑ m ∈ range n, ((m : ℝ) + 1) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hstep : ∀ m ∈ range n, (if m + 1 ≤ n + 1 then ((m + 1 : ℕ) : ℝ) *
        ∑ i ∈ range (n + 1 - (m + 1) + 1), 1 / (((m + 1 : ℕ) : ℝ) + i) else 0) =
        (if m + 1 ≤ n then ((m + 1 : ℕ) : ℝ) *
        ∑ i ∈ range (n - (m + 1) + 1), 1 / (((m + 1 : ℕ) : ℝ) + i) else 0) +
          ((m : ℝ) + 1) / ((n : ℝ) + 1) := by
      intro m hm
      rw [mem_range] at hm
      rw [if_pos (by omega), if_pos (by omega), show n + 1 - (m + 1) + 1 = (n - (m + 1) + 1) + 1 by omega,
        sum_range_succ, mul_add]
      congr 1
      have : (((m + 1 : ℕ) : ℝ) + ((n - (m + 1) + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
        rw [← Nat.cast_add, show m + 1 + (n - (m + 1) + 1) = n + 1 by omega]; push_cast; ring
      rw [this]; push_cast; ring
    rw [sum_congr rfl hstep, sum_add_distrib, ih, ← sum_div, htri,
      if_pos le_rfl, Nat.sub_self, zero_add, sum_range_one]
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma Gamma_nat_add_half_mul (n : ℕ) :
    Real.Gamma ((n : ℝ) + 1 / 2) * 4 ^ n * (n.factorial : ℝ) =
      ((2 * n).factorial : ℝ) * Real.sqrt Real.pi := by
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_add, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one,
      mul_zero]
    rw [Real.Gamma_one_half_eq, one_mul]
  | succ n ih =>
    have h : ((n + 1 : ℕ) : ℝ) + 1 / 2 = ((n : ℝ) + 1 / 2) + 1 := by push_cast; ring
    rw [h, Real.Gamma_add_one (by positivity), show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    linear_combination (2 * (n : ℝ) + 1) * (2 * n + 2) * ih

theorem legendre_parity (n : ℕ) (x : ℝ) :
    (legendre n).eval (-x) = (-1 : ℝ) ^ n * (legendre n).eval x := by
  exact legendre_parity' n x

theorem legendre_deriv_identity (n : ℕ) (x : ℝ) :
    (1 - x ^ 2) * (legendre (n + 1)).derivative.eval x =
      ((n : ℝ) + 1) * ((legendre n).eval x - x * (legendre (n + 1)).eval x) := by
  exact legendre_d4 n x

/-- A priori residual bound: rounding error grows quadratically in n. -/
theorem legendre_recurrence_stability {x ε : ℝ} {u e : ℕ → ℝ}
    (hx : |x| ≤ 1) (hε : 0 ≤ ε)
    (hu0 : u 0 = 1) (hu1 : u 1 = x + e 0)
    (hu : ∀ k : ℕ, u (k + 2) =
      ((2 * (k : ℝ) + 3) * x * u (k + 1) -
        ((k : ℝ) + 1) * u k) / ((k : ℝ) + 2) + e (k + 1))
    (he : ∀ k, |e k| ≤ ε) (n : ℕ) :
    |u n - (legendre n).eval x| ≤
      (((n : ℝ) + 1) * ((n : ℝ) + 2) / 4) * ε := by
  set d : ℕ → ℝ := fun n => u n - (legendre n).eval x with hd
  have hrep : ∀ n, d n = ∑ m ∈ range n, e m * legGreen x (m + 1) n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n, ih with
      | 0, _ => simp [hd, hu0]
      | 1, _ => simp [hd, hu1, legGreen_self]
      | k + 2, ih =>
        have h1 := ih (k + 1) (by omega)
        have h0 := ih k (by omega)
        have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
        have hdk : ((k : ℝ) + 2) * d (k + 2) = (2 * (k : ℝ) + 3) * x * d (k + 1) -
            ((k : ℝ) + 1) * d k + ((k : ℝ) + 2) * e (k + 1) := by
          simp only [hd]
          rw [hu k]
          have := legendre_eval_rec k x
          field_simp
          linear_combination -this
        have hsum : ((k : ℝ) + 2) * ∑ m ∈ range (k + 1), e m * legGreen x (m + 1) (k + 2) =
            (2 * (k : ℝ) + 3) * x * ∑ m ∈ range (k + 1), e m * legGreen x (m + 1) (k + 1) -
              ((k : ℝ) + 1) * ∑ m ∈ range k, e m * legGreen x (m + 1) k := by
          have hk : ∑ m ∈ range (k + 1), e m * legGreen x (m + 1) k =
              ∑ m ∈ range k, e m * legGreen x (m + 1) k := by
            rw [sum_range_succ, legGreen_below x (by omega : k < k + 1), mul_zero, add_zero]
          rw [← hk, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
          refine sum_congr rfl fun m hm => ?_
          rw [mem_range] at hm
          have := legGreen_rec x (M := m + 1) (j := k) (by omega) (by omega)
          linear_combination e m * this
        apply mul_left_cancel₀ hk2
        rw [hdk, h1, h0, sum_range_succ (fun m => e m * legGreen x (m + 1) (k + 2)) (k + 1),
          legGreen_self x (by omega : 1 ≤ k + 1 + 1), mul_add, hsum]
        ring
  show |d n| ≤ _
  rw [hrep n]
  calc |∑ m ∈ range n, e m * legGreen x (m + 1) n|
      ≤ ∑ m ∈ range n, |e m * legGreen x (m + 1) n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ range n, ε * (if m + 1 ≤ n then ((m + 1 : ℕ) : ℝ) *
          ∑ i ∈ range (n - (m + 1) + 1), 1 / (((m + 1 : ℕ) : ℝ) + i) else 0) := by
        refine sum_le_sum fun m _ => ?_
        rw [abs_mul]
        exact mul_le_mul (he m) (legGreen_abs_le x hx (by omega)) (abs_nonneg _) hε
    _ = ε * ((n : ℝ) * ((n : ℝ) + 3) / 4) := by rw [← mul_sum, legGreen_bound_sum]
    _ ≤ _ := by
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_right _ hε
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith

theorem legendre_deriv_bounds (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(legendre n).derivative.eval x| ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 ∧
      |(legendre n).derivative.derivative.eval x| ≤
        ((n : ℝ) - 1) * (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 8 := by
  have h1 : ∀ n, |(legendre n).derivative.eval x| ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n, ih with
      | 0, _ => simp
      | 1, _ => simp
      | m + 2, ih =>
        have hd := legendre_d1 m x
        have h0 := ih m (by omega)
        have hp := legendre_abs_le_one (m + 1) hx
        have : (legendre (m + 2)).derivative.eval x =
            (legendre m).derivative.eval x + (2 * (m : ℝ) + 3) * (legendre (m + 1)).eval x := by
          linarith
        rw [this]
        calc _ ≤ |(legendre m).derivative.eval x| + |(2 * (m : ℝ) + 3) * (legendre (m + 1)).eval x| :=
              abs_add_le _ _
          _ ≤ (m : ℝ) * ((m : ℝ) + 1) / 2 + (2 * (m : ℝ) + 3) * 1 := by
              rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * m + 3)]
              gcongr
          _ = _ := by push_cast; ring
  refine ⟨h1 n, ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp
    | m + 2, ih =>
      have hd := legendre_d1_second m x
      have h0 := ih m (by omega)
      have hp := h1 (m + 1)
      have : (legendre (m + 2)).derivative.derivative.eval x =
          (legendre m).derivative.derivative.eval x +
            (2 * (m : ℝ) + 3) * (legendre (m + 1)).derivative.eval x := by
        linarith
      rw [this]
      calc _ ≤ |(legendre m).derivative.derivative.eval x| +
            |(2 * (m : ℝ) + 3) * (legendre (m + 1)).derivative.eval x| := abs_add_le _ _
        _ ≤ ((m : ℝ) - 1) * (m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 2) / 8 +
              (2 * (m : ℝ) + 3) * (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) + 1) / 2) := by
            rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * m + 3)]
            gcongr
        _ = _ := by push_cast; ring

open scoped Real

/-! ### Sonin-type bounds for the interior derivative estimates -/

lemma legendre_zero_odd (m : ℕ) : (legendre (2 * m + 1)).eval 0 = 0 := by
  have h := legendre_parity' (2 * m + 1) 0
  rw [neg_zero, pow_succ, pow_mul] at h
  norm_num at h
  linarith

lemma legendre_deriv_zero (n : ℕ) :
    (legendre (n + 1)).derivative.eval 0 = ((n : ℝ) + 1) * (legendre n).eval 0 := by
  have h := legendre_d4 n 0
  simpa using h

lemma legendre_zero_even_rec (m : ℕ) :
    (legendre (2 * (m + 1))).eval 0 = -((2 * (m : ℝ) + 1) / (2 * m + 2)) * (legendre (2 * m)).eval 0 := by
  have h := legendre_eval_rec (2 * m) 0
  rw [show 2 * m + 2 = 2 * (m + 1) by ring] at h
  push_cast at h
  have : (2 * (m : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  linarith

lemma legendre_zero_even_wallis (m : ℕ) :
    (legendre (2 * m)).eval 0 ^ 2 * (2 * m + 1) * Real.Wallis.W m = 1 := by
  induction m with
  | zero => simp [Real.Wallis.W]
  | succ m ih =>
    rw [legendre_zero_even_rec, Real.Wallis.W_succ]
    push_cast
    have h1 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (2 * (m : ℝ) + 2) ≠ 0 := by positivity
    have h3 : (2 * (m : ℝ) + 3) ≠ 0 := by positivity
    have e : (-((2 * (m : ℝ) + 1) / (2 * m + 2)) * (legendre (2 * m)).eval 0) ^ 2 *
        (2 * ((m : ℝ) + 1) + 1) * (Real.Wallis.W m * ((2 * m + 2) / (2 * m + 1) *
          ((2 * m + 2) / (2 * m + 3)))) =
        (legendre (2 * m)).eval 0 ^ 2 * (2 * m + 1) * Real.Wallis.W m := by
      field_simp
      ring
    rw [e, ih]

lemma legendre_zero_even_sq_le (m : ℕ) :
    (legendre (2 * m)).eval 0 ^ 2 * (4 * m + 1) ≤ 4 / π := by
  set b : ℕ → ℝ := fun k => (legendre (2 * k)).eval 0 ^ 2 * (4 * k + 1) with hb
  have hmono : Monotone b := by
    apply monotone_nat_of_le_succ
    intro k
    simp only [hb]
    rw [legendre_zero_even_rec]
    push_cast
    have h2 : (0 : ℝ) < 2 * k + 2 := by positivity
    rw [mul_pow, neg_sq, div_pow]
    have hp : 0 ≤ (legendre (2 * k)).eval 0 ^ 2 := sq_nonneg _
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : (2 * (k : ℝ) + 2) ^ 2 * (4 * k + 1) ≤ (2 * k + 1) ^ 2 * (4 * (k + 1) + 1) := by nlinarith
    nlinarith
  by_contra hcon
  push_neg at hcon
  set β := b m * π / 4 with hβ
  have hβ1 : 1 < β := by
    rw [hβ, lt_div_iff₀ (by norm_num), one_mul, ← div_lt_iff₀ Real.pi_pos]
    simpa [hb] using hcon
  obtain ⟨k, hk⟩ := exists_nat_gt (max (m : ℝ) (1 / (β - 1)))
  have hkm : m ≤ k := by exact_mod_cast (le_max_left _ _).trans hk.le
  have hk2 : 1 / (β - 1) < k := (le_max_right _ _).trans_lt hk
  have hbk : b m ≤ b k := hmono hkm
  have hW := Real.Wallis.le_W k
  have hid := legendre_zero_even_wallis k
  -- b k * (2k+1) * W k = 4k+1
  have hbk' : b k * (2 * k + 1) * Real.Wallis.W k = 4 * k + 1 := by
    simp only [hb]; linear_combination (4 * (k : ℝ) + 1) * hid
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (le_of_lt (one_div_pos.2 (by linarith))) hk2
  have hβk : 1 < (β - 1) * k := by
    rwa [div_lt_iff₀ (by linarith), mul_comm] at hk2
  have hbpos : 0 ≤ b m := by simp only [hb]; positivity
  have h4 : b m * ((2 * k + 1) * ((2 * k + 1) / (2 * k + 2) * (π / 2))) ≤ 4 * k + 1 := by
    rw [← hbk']
    have := Real.Wallis.W_pos k
    calc b m * ((2 * k + 1) * ((2 * k + 1) / (2 * k + 2) * (π / 2)))
        ≤ b k * ((2 * k + 1) * Real.Wallis.W k) := by
          apply mul_le_mul hbk _ (by positivity) (by simp only [hb]; positivity)
          exact mul_le_mul_of_nonneg_left hW (by positivity)
      _ = _ := by ring
  have hbm : b m = 4 * β / π := by rw [hβ]; field_simp
  rw [hbm] at h4
  have hpi := Real.pi_pos
  have h5 : 4 * β * ((2 * k + 1) * ((2 * k + 1) / (2 * k + 2) * (1 / 2))) ≤ 4 * k + 1 := by
    convert h4 using 1; field_simp
  rw [show 4 * β * ((2 * k + 1) * ((2 * k + 1) / (2 * k + 2) * (1 / 2))) =
    β * (2 * (2 * k + 1) ^ 2 / (2 * k + 2)) by ring, mul_div_assoc', div_le_iff₀ (by positivity)] at h5
  nlinarith

/-- Value at `0` of the Sonin-type function used for the Bernstein inequality. -/
def soninZero (n : ℕ) : ℝ :=
  (legendre n).eval 0 ^ 2 + 4 * (legendre n).derivative.eval 0 ^ 2 / ((2 * (n : ℝ) + 1) ^ 2 + 1)

lemma soninZero_le (n : ℕ) (hn : 0 < n) : soninZero n ≤ 2 / (π * n) := by
  have hpi := Real.pi_pos
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hd : (legendre (2 * (k + 1))).derivative.eval 0 = 0 := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, legendre_deriv_zero, legendre_zero_odd,
        mul_zero]
    have hb := legendre_zero_even_sq_le (k + 1)
    unfold soninZero
    rw [hd]
    push_cast at hb ⊢
    rw [le_div_iff₀ (by positivity)] at hb
    rw [le_div_iff₀ (by positivity)]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
      add_zero]
    nlinarith [mul_nonneg (sq_nonneg ((legendre (2 * (k + 1))).eval 0)) hpi.le]
  · have hd : (legendre (2 * m + 1)).derivative.eval 0 = (2 * m + 1) * (legendre (2 * m)).eval 0 := by
      rw [legendre_deriv_zero]; push_cast; ring
    have hb := legendre_zero_even_sq_le m
    unfold soninZero
    rw [hd, legendre_zero_odd]
    push_cast
    set a := (legendre (2 * m)).eval 0 ^ 2 with ha
    have ha0 : 0 ≤ a := sq_nonneg _
    rw [le_div_iff₀ (by positivity)] at hb
    rw [mul_pow, ← ha]
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_add, div_le_div_iff₀ (by positivity) (by positivity)]
    have hm : (0 : ℝ) ≤ m := by positivity
    have key : 16 * (2 * (m : ℝ) + 1) ^ 3 ≤ 2 * ((2 * (2 * m + 1) + 1) ^ 2 + 1) * (4 * m + 1) := by
      nlinarith
    have h1 := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 4 * (2 * m + 1) ^ 3)
    have h2 : 4 * (2 * (m : ℝ) + 1) ^ 2 * a * (π * (2 * m + 1)) * (4 * m + 1) ≤
        2 * ((2 * (2 * m + 1) + 1) ^ 2 + 1) * (4 * m + 1) := by nlinarith
    have h3 := le_of_mul_le_mul_right h2 (by positivity : (0 : ℝ) < 4 * m + 1)
    linarith

/-- Auxiliary polynomial `x P_n - 2 (1 - x^2) P_n'`. -/
def soninZ (n : ℕ) : ℝ[X] := X * legendre n - C 2 * (1 - X ^ 2) * (legendre n).derivative

/-- Auxiliary polynomial `(2n+1)^2 (1 - x^2) + 1`. -/
def soninD (n : ℕ) : ℝ[X] := C ((2 * (n : ℝ) + 1) ^ 2) * (1 - X ^ 2) + 1

def soninW (n : ℕ) (x : ℝ) : ℝ :=
  (legendre n).eval x ^ 2 + (soninZ n).eval x ^ 2 / (soninD n).eval x

lemma soninD_eval (n : ℕ) (x : ℝ) :
    (soninD n).eval x = (2 * (n : ℝ) + 1) ^ 2 * (1 - x ^ 2) + 1 := by
  simp [soninD]

lemma soninZ_eval (n : ℕ) (x : ℝ) :
    (soninZ n).eval x = x * (legendre n).eval x - 2 * (1 - x ^ 2) * (legendre n).derivative.eval x := by
  simp [soninZ]

lemma soninD_pos (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : 0 < (soninD n).eval x := by
  rw [soninD_eval]
  have : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  positivity

lemma soninPhi_hasDerivAt (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x => (1 - x ^ 2) * soninW n x ^ 2)
      (-4 * x * soninW n x * (soninZ n).eval x ^ 2 / (soninD n).eval x ^ 2) x := by
  have hD := soninD_pos n ⟨hx.1.le, hx.2.le⟩
  have hy := (legendre n).hasDerivAt x
  have hz := (soninZ n).hasDerivAt x
  have hd := (soninD n).hasDerivAt x
  have h1 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_id x).pow 2).const_sub 1
  have hW : HasDerivAt (soninW n) _ x := (hy.pow 2).add ((hz.pow 2).div hd hD.ne')
  have := h1.mul (hW.pow 2)
  convert this using 1
  have hs : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hode := legendre_ode n x
  have hy2 : (legendre n).derivative.derivative.eval x =
      (2 * x * (legendre n).derivative.eval x - n * (n + 1) * (legendre n).eval x) / (1 - x ^ 2) := by
    field_simp; linarith
  simp only [soninW, soninZ, soninD, derivative_mul, derivative_sub, derivative_X, derivative_C,
    derivative_one, derivative_X_pow, derivative_add, eval_add, eval_mul, eval_sub, eval_X, eval_C,
    eval_one, eval_pow, zero_mul, zero_add, one_mul, zero_sub, eval_neg,
    Nat.cast_ofNat, add_zero, neg_mul, Pi.pow_apply] at hD ⊢
  rw [hy2]
  generalize (legendre n).eval x = y at *
  generalize (legendre n).derivative.eval x = y1 at *
  simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  field_simp
  ring

lemma soninW_nonneg (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : 0 ≤ soninW n x := by
  have := soninD_pos n hx
  unfold soninW; positivity

lemma soninW_zero (n : ℕ) : soninW n 0 = soninZero n := by
  simp only [soninW, soninZero, soninZ_eval, soninD_eval]
  ring_nf

lemma sonin_bernstein (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 - x ^ 2) * soninW n x ^ 2 ≤ soninZero n ^ 2 := by
  set φ : ℝ → ℝ := fun x => (1 - x ^ 2) * soninW n x ^ 2 with hφ
  have hd : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt φ
      (-4 * x * soninW n x * (soninZ n).eval x ^ 2 / (soninD n).eval x ^ 2) x :=
    fun x hx => soninPhi_hasDerivAt n hx
  have h0 : φ 0 = soninZero n ^ 2 := by simp [hφ, soninW_zero]
  rw [← h0]
  have hsign : ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      0 ≤ soninW n y * (soninZ n).eval y ^ 2 / (soninD n).eval y ^ 2 := by
    intro y hy
    have := soninW_nonneg n ⟨hy.1.le, hy.2.le⟩
    positivity
  rcases le_total 0 x with hx0 | hx0
  · have hanti : AntitoneOn φ (Set.Ico 0 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ico 0 1)
      · intro y hy
        exact (hd y ⟨by linarith [hy.1], hy.2⟩).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Ico] at hy
        exact (hd y ⟨by linarith [hy.1], hy.2⟩).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Ico] at hy
        rw [(hd y ⟨by linarith [hy.1], hy.2⟩).deriv]
        have := hsign y ⟨by linarith [hy.1], hy.2⟩
        have : -4 * y * soninW n y * (soninZ n).eval y ^ 2 / (soninD n).eval y ^ 2 =
          -4 * y * (soninW n y * (soninZ n).eval y ^ 2 / (soninD n).eval y ^ 2) := by ring
        rw [this]
        nlinarith [hy.1]
    exact hanti ⟨le_refl 0, by norm_num⟩ ⟨hx0, hx.2⟩ hx0
  · have hmono : MonotoneOn φ (Set.Ioc (-1) 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ioc (-1) 0)
      · intro y hy
        exact (hd y ⟨hy.1, by linarith [hy.2]⟩).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Ioc] at hy
        exact (hd y ⟨hy.1, by linarith [hy.2]⟩).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Ioc] at hy
        rw [(hd y ⟨hy.1, by linarith [hy.2]⟩).deriv]
        have := hsign y ⟨hy.1, by linarith [hy.2]⟩
        have : -4 * y * soninW n y * (soninZ n).eval y ^ 2 / (soninD n).eval y ^ 2 =
          -4 * y * (soninW n y * (soninZ n).eval y ^ 2 / (soninD n).eval y ^ 2) := by ring
        rw [this]
        nlinarith [hy.2]
    exact hmono ⟨hx.1, hx0⟩ ⟨by norm_num, le_refl 0⟩ hx0

/-- A generic Sonin-type bound for a polynomial solution of
`(1 - x^2) p'' - c x p' + μ p = 0` with `c ≥ 2`. -/
lemma sonin_simple (p : ℝ[X]) {c μ B : ℝ} (hc : 2 ≤ c) (hμ : 0 < μ)
    (hode : ∀ x, (1 - x ^ 2) * p.derivative.derivative.eval x - c * x * p.derivative.eval x +
      μ * p.eval x = 0)
    (h1 : p.eval 1 ^ 2 ≤ B) (hm1 : p.eval (-1) ^ 2 ≤ B) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (1 - x ^ 2) * p.derivative.eval x ^ 2 ≤ μ * B := by
  set g : ℝ → ℝ := fun x => p.eval x ^ 2 + (1 - x ^ 2) * p.derivative.eval x ^ 2 / μ with hg
  have hd : ∀ x, HasDerivAt g (2 * (c - 1) * x * p.derivative.eval x ^ 2 / μ) x := by
    intro x
    have hy := p.hasDerivAt x
    have hy1 := p.derivative.hasDerivAt x
    have h1 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * x)) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_sub 1
    have := (hy.pow 2).add ((h1.mul (hy1.pow 2)).div_const μ)
    convert this using 1
    have := hode x
    simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat, Pi.pow_apply]
    field_simp
    linear_combination (-1) * p.derivative.eval x * this
  have hsign : ∀ y, 0 ≤ (c - 1) * p.derivative.eval y ^ 2 / μ := fun y => by
    have : 0 ≤ c - 1 := by linarith
    positivity
  have hgx : g x ≤ B := by
    rcases le_total 0 x with hx0 | hx0
    · have hmono : MonotoneOn g (Set.Icc 0 1) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
        · exact fun y _ => (hd y).continuousAt.continuousWithinAt
        · exact fun y _ => (hd y).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [interior_Icc] at hy
          rw [(hd y).deriv]
          have := hsign y
          have e : 2 * (c - 1) * y * p.derivative.eval y ^ 2 / μ =
            2 * y * ((c - 1) * p.derivative.eval y ^ 2 / μ) := by ring
          rw [e]; nlinarith [hy.1]
      have := hmono ⟨hx0, hx.2⟩ ⟨by norm_num, le_refl 1⟩ hx.2
      simp only [hg] at this
      norm_num at this
      linarith
    · have hanti : AntitoneOn g (Set.Icc (-1) 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc (-1) 0)
        · exact fun y _ => (hd y).continuousAt.continuousWithinAt
        · exact fun y _ => (hd y).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [interior_Icc] at hy
          rw [(hd y).deriv]
          have := hsign y
          have e : 2 * (c - 1) * y * p.derivative.eval y ^ 2 / μ =
            2 * y * ((c - 1) * p.derivative.eval y ^ 2 / μ) := by ring
          rw [e]; nlinarith [hy.2]
      have := hanti ⟨le_refl (-1 : ℝ), by norm_num⟩ ⟨hx.1, hx0⟩ hx.1
      simp only [hg] at this
      norm_num at this
      linarith
  simp only [hg] at hgx
  have : (1 - x ^ 2) * p.derivative.eval x ^ 2 / μ ≤ B := by nlinarith [sq_nonneg (p.eval x)]
  rwa [div_le_iff₀ hμ, mul_comm B] at this

lemma legendre_deriv_ode (n : ℕ) (x : ℝ) :
    (1 - x ^ 2) * (legendre n).derivative.derivative.derivative.eval x
      - 4 * x * (legendre n).derivative.derivative.eval x
      + ((n : ℝ) * ((n : ℝ) + 1) - 2) * (legendre n).derivative.eval x = 0 := by
  have h := congrArg (fun p => (derivative p).eval x) (legendre_ode_poly n)
  simp only [derivative_mul, derivative_sub, derivative_add, derivative_X, derivative_C,
    eval_add, eval_sub, eval_mul, eval_X, eval_C, zero_mul, zero_add, one_mul,
    derivative_zero, eval_zero] at h
  linear_combination h

lemma legendre_deriv_eval_one (n : ℕ) :
    (legendre n).derivative.eval 1 = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  have h := legendre_ode n 1
  rw [legendre_eval_one] at h
  linarith

lemma legendre_deriv_eval_neg_one_sq (n : ℕ) :
    (legendre n).derivative.eval (-1) ^ 2 = ((n : ℝ) * ((n : ℝ) + 1) / 2) ^ 2 := by
  have h := legendre_ode n (-1)
  rw [legendre_eval_neg_one] at h
  have : (legendre n).derivative.eval (-1) = -((n : ℝ) * ((n : ℝ) + 1) / 2) * (-1) ^ n := by
    linarith
  rw [this, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
  norm_num

lemma sonin_A (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (1 - x ^ 2) * (legendre n).derivative.eval x ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 1) := by
  have h := sonin_simple (legendre n) (c := 2) (μ := (n : ℝ) * ((n : ℝ) + 1)) (B := 1)
    le_rfl (by positivity) (fun x => by linear_combination legendre_ode n x)
    (by rw [legendre_eval_one]; norm_num)
    (by rw [legendre_eval_neg_one, ← pow_mul, mul_comm n 2, pow_mul]; norm_num) hx
  linarith

lemma sonin_C (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (1 - x ^ 2) * (legendre n).derivative.derivative.eval x ^ 2 ≤
      ((n : ℝ) * ((n : ℝ) + 1) - 2) * ((n : ℝ) * ((n : ℝ) + 1) / 2) ^ 2 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact sonin_simple (legendre n).derivative (c := 4) (by norm_num) (by nlinarith)
    (fun x => by linear_combination legendre_deriv_ode n x)
    (by rw [legendre_deriv_eval_one]) (by rw [legendre_deriv_eval_neg_one_sq]) hx


/-- Consequence of the Sonin–Bernstein bound: `√(1-x²) * W(x) ≤ S₀`. -/
lemma sqrt_mul_soninW_le (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.sqrt (1 - x ^ 2) * soninW n x ≤ soninZero n := by
  have h := sonin_bernstein n hx
  have hW := soninW_nonneg n ⟨hx.1.le, hx.2.le⟩
  have hS : 0 ≤ soninZero n := by rw [← soninW_zero]; exact soninW_nonneg n ⟨by norm_num, by norm_num⟩
  have hw : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  rw [← pow_le_pow_iff_left₀ (by positivity) hS two_ne_zero, mul_pow, Real.sq_sqrt hw]
  exact h


lemma legendre_deriv_sq_bound (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 - x ^ 2) * Real.sqrt (1 - x ^ 2) * (legendre n).derivative.eval x ^ 2 ≤ 8 * n / π := by
  have hw : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  set s := Real.sqrt (1 - x ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hw
  have hs2 : s ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hw.le
  have hs1 : s ≤ 1 := by nlinarith
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  rw [← hs2]
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    simp only [legendre_one', derivative_X, eval_one, one_pow, mul_one, Nat.cast_one]
    rw [le_div_iff₀ hpi]
    have : s ^ 2 * s ≤ 1 := by nlinarith [pow_le_one₀ hs0.le hs1 (n := 2)]
    nlinarith
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
  have hSW := sqrt_mul_soninW_le n hx
  rw [← hs] at hSW
  clear_value s
  set y := (legendre n).eval x with hy
  set y1 := (legendre n).derivative.eval x with hy1
  by_cases hcase : 1 ≤ 2 * s ^ 2 * (3 * (n : ℝ) ^ 2 - n - 1 / 4)
  · have hS0 := soninZero_le n hn
    set D := (soninD n).eval x with hD
    have hDpos : 0 < D := soninD_pos n ⟨hx.1.le, hx.2.le⟩
    have hDe : D = (2 * (n : ℝ) + 1) ^ 2 * s ^ 2 + 1 := by rw [hD, soninD_eval, hs2]
    set z := (soninZ n).eval x with hz
    have hze : z = x * y - 2 * s ^ 2 * y1 := by rw [hz, soninZ_eval, hs2]
    set W := soninW n x with hWdef
    have hWe : W = y ^ 2 + z ^ 2 / D := rfl
    have hW0 : 0 ≤ W := soninW_nonneg n ⟨hx.1.le, hx.2.le⟩
    -- 4 s^4 y1^2 ≤ (1 + D) W
    have key1 : 4 * s ^ 4 * y1 ^ 2 * D ≤ (x ^ 2 + D) * (D * y ^ 2 + z ^ 2) := by
      have e : 2 * s ^ 2 * y1 = x * y - z := by rw [hze]; ring
      have : 4 * s ^ 4 * y1 ^ 2 = (x * y - z) ^ 2 := by rw [← e]; ring
      rw [this]
      nlinarith [sq_nonneg (x * z + D * y)]
    have key2 : 4 * s ^ 4 * y1 ^ 2 ≤ (1 + D) * W := by
      have hDW : D * W = D * y ^ 2 + z ^ 2 := by rw [hWe]; field_simp
      have : 4 * s ^ 4 * y1 ^ 2 * D ≤ (1 + D) * W * D := by
        calc 4 * s ^ 4 * y1 ^ 2 * D ≤ (x ^ 2 + D) * (D * y ^ 2 + z ^ 2) := key1
          _ ≤ (1 + D) * (D * y ^ 2 + z ^ 2) := by
            apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = (1 + D) * W * D := by rw [← hDW]; ring
      exact le_of_mul_le_mul_right this hDpos
    have key3 : 4 * s ^ 5 * y1 ^ 2 ≤ (1 + D) * (2 / (π * n)) := by
      have h5 := mul_le_mul_of_nonneg_left key2 hs0.le
      calc _ = s * (4 * s ^ 4 * y1 ^ 2) := by ring
        _ ≤ s * ((1 + D) * W) := h5
        _ = (1 + D) * (s * W) := by ring
        _ ≤ (1 + D) * (2 / (π * n)) := by
          apply mul_le_mul_of_nonneg_left (hSW.trans hS0) (by positivity)
    have key4 : (1 + D) * (2 / (π * n)) ≤ 4 * s ^ 2 * (8 * n / π) := by
      rw [hDe]
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have : 2 + (2 * (n : ℝ) + 1) ^ 2 * s ^ 2 ≤ 16 * n ^ 2 * s ^ 2 := by nlinarith
      have e : 4 * s ^ 2 * (8 * n / π) * (π * n) = 32 * n ^ 2 * s ^ 2 := by field_simp; ring
      rw [e]; linarith
    have : 4 * s ^ 2 * (s ^ 2 * s * y1 ^ 2) ≤ 4 * s ^ 2 * (8 * n / π) := by
      have e2 : 4 * s ^ 2 * (s ^ 2 * s * y1 ^ 2) = 4 * s ^ 5 * y1 ^ 2 := by ring
      rw [e2]; exact key3.trans key4
    exact le_of_mul_le_mul_left this (by positivity)
  · push_neg at hcase
    have hA := sonin_A n hn ⟨hx.1.le, hx.2.le⟩
    rw [← hs2] at hA
    have hsn : s * ((n : ℝ) + 1) * π ≤ 8 := by
      have hq : (s * ((n : ℝ) + 1) * π) ^ 2 ≤ 64 := by
        have h10 : π ^ 2 ≤ 10 := by
          have := pow_le_pow_left₀ hpi.le hpi4.le 2
          norm_num at this; linarith
        set K := 2 * (3 * (n : ℝ) ^ 2 - n - 1 / 4) with hK
        have hsK : s ^ 2 * K < 1 := by rw [hK]; linarith
        have hpoly : 10 * ((n : ℝ) + 1) ^ 2 ≤ 64 * K := by rw [hK]; nlinarith
        have h3 : ((n : ℝ) + 1) ^ 2 * π ^ 2 ≤ 64 * K := by
          have := mul_le_mul_of_nonneg_left h10 (sq_nonneg ((n : ℝ) + 1))
          linarith
        calc (s * ((n : ℝ) + 1) * π) ^ 2 = s ^ 2 * (((n : ℝ) + 1) ^ 2 * π ^ 2) := by ring
          _ ≤ s ^ 2 * (64 * K) := mul_le_mul_of_nonneg_left h3 (sq_nonneg s)
          _ = 64 * (s ^ 2 * K) := by ring
          _ ≤ 64 := by linarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1
        (by norm_num; linarith)
    rw [le_div_iff₀ hpi]
    calc s ^ 2 * s * y1 ^ 2 * π = s * π * (s ^ 2 * y1 ^ 2) := by ring
      _ ≤ s * π * (n * (n + 1)) := by
          apply mul_le_mul_of_nonneg_left hA (by positivity)
      _ = n * (s * (n + 1) * π) := by ring
      _ ≤ n * 8 := by apply mul_le_mul_of_nonneg_left hsn (by positivity)
      _ = 8 * n := by ring


lemma legendre_deriv2_sq_bound (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 - x ^ 2) ^ 2 * Real.sqrt (1 - x ^ 2) * (legendre n).derivative.derivative.eval x ^ 2 ≤
      32 * (n : ℝ) ^ 3 / π := by
  have hw : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d2
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    simp only [legendre_one', derivative_X, derivative_one, eval_zero]
    norm_num
    positivity
  have hF1 := legendre_deriv_sq_bound n hn hx
  have hSW := sqrt_mul_soninW_le n hx
  have hS0 := soninZero_le n hn
  have hC := sonin_C n h2 ⟨hx.1.le, hx.2.le⟩
  have hode := legendre_ode n x
  have hW0 : 0 ≤ (soninZ n).eval x ^ 2 / (soninD n).eval x := by
    have := soninD_pos n ⟨hx.1.le, hx.2.le⟩
    positivity
  set s := Real.sqrt (1 - x ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hw
  have hs2 : s ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hw.le
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  rw [← hs2] at hF1 hC hode ⊢
  clear_value s
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
  set y := (legendre n).eval x with hy
  set y1 := (legendre n).derivative.eval x with hy1
  set y2 := (legendre n).derivative.derivative.eval x with hy2
  have hF2 : s * y ^ 2 ≤ 2 / (π * n) := by
    simp only [soninW] at hSW
    have : s * y ^ 2 ≤ s * (y ^ 2 + (soninZ n).eval x ^ 2 / (soninD n).eval x) := by
      apply mul_le_mul_of_nonneg_left (by linarith) hs0.le
    linarith
  clear_value y y1 y2
  clear hy hy1 hy2 hs hSW hW0
  by_cases hcase : 4 ≤ s * (3 * n - 1)
  · obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ((n : ℝ) + 1) * s / 4 := ⟨_, rfl⟩
    have ht0 : 0 < t := by rw [ht]; positivity
    obtain ⟨b, hb⟩ : ∃ b : ℝ, b = -((n : ℝ) * (n + 1) * y) := ⟨_, rfl⟩
    have hab : s ^ 2 * y2 = 2 * x * y1 + b := by rw [hb]; linarith
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * x * y1 := ⟨_, rfl⟩
    rw [← ha] at hab
    have hCS : t * (a + b) ^ 2 ≤ t * (1 + t) * a ^ 2 + (1 + t) * b ^ 2 := by
      nlinarith [sq_nonneg (t * a - b)]
    have ha2 : a ^ 2 ≤ 4 * y1 ^ 2 := by
      have : a ^ 2 = 4 * x ^ 2 * y1 ^ 2 := by rw [ha]; ring
      rw [this]; nlinarith [sq_nonneg y1]
    have hb2 : b ^ 2 = ((n : ℝ) * (n + 1)) ^ 2 * y ^ 2 := by rw [hb]; ring
    -- multiply by s^3
    have step : t * s ^ 7 * y2 ^ 2 ≤
        4 * t * (1 + t) * (8 * n / π) + (1 + t) * ((n : ℝ) * (n + 1)) ^ 2 * s ^ 2 * (2 / (π * n)) := by
      have e1 : t * s ^ 7 * y2 ^ 2 = s ^ 3 * (t * (a + b) ^ 2) := by rw [← hab]; ring
      have h3 : 0 ≤ s ^ 3 := by positivity
      calc t * s ^ 7 * y2 ^ 2 = s ^ 3 * (t * (a + b) ^ 2) := e1
        _ ≤ s ^ 3 * (t * (1 + t) * a ^ 2 + (1 + t) * b ^ 2) := mul_le_mul_of_nonneg_left hCS h3
        _ ≤ s ^ 3 * (t * (1 + t) * (4 * y1 ^ 2) + (1 + t) * b ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ h3
            have : 0 ≤ t * (1 + t) := by positivity
            have := mul_le_mul_of_nonneg_left ha2 this
            linarith
        _ = 4 * t * (1 + t) * (s ^ 2 * s * y1 ^ 2) +
              (1 + t) * ((n : ℝ) * (n + 1)) ^ 2 * s ^ 2 * (s * y ^ 2) := by rw [hb2]; ring
        _ ≤ _ := by
            have hp1 : 0 ≤ 4 * t * (1 + t) := by positivity
            have hp2 : 0 ≤ (1 + t) * ((n : ℝ) * (n + 1)) ^ 2 * s ^ 2 := by positivity
            exact add_le_add (mul_le_mul_of_nonneg_left hF1 hp1) (mul_le_mul_of_nonneg_left hF2 hp2)
    have hRHS : 4 * t * (1 + t) * (8 * n / π) + (1 + t) * ((n : ℝ) * (n + 1)) ^ 2 * s ^ 2 * (2 / (π * n))
        = t * (2 * n / π * (4 + (n + 1) * s) ^ 2) := by
      rw [ht]; field_simp; ring
    rw [hRHS] at step
    have step2 : s ^ 7 * y2 ^ 2 ≤ 2 * n / π * (4 + (n + 1) * s) ^ 2 := by
      have : t * (s ^ 7 * y2 ^ 2) ≤ t * (2 * n / π * (4 + (n + 1) * s) ^ 2) := by linarith
      exact le_of_mul_le_mul_left this ht0
    have step3 : 2 * n / π * (4 + (n + 1) * s) ^ 2 ≤ s ^ 2 * (32 * (n : ℝ) ^ 3 / π) := by
      have h4 : 4 + (n + 1) * s ≤ 4 * n * s := by linarith
      have h5 : (4 + (n + 1) * s) ^ 2 ≤ (4 * n * s) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
      have e : s ^ 2 * (32 * (n : ℝ) ^ 3 / π) = 2 * n / π * (4 * n * s) ^ 2 := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    have : s ^ 2 * ((s ^ 2) ^ 2 * s * y2 ^ 2) ≤ s ^ 2 * (32 * (n : ℝ) ^ 3 / π) := by
      have e : s ^ 2 * ((s ^ 2) ^ 2 * s * y2 ^ 2) = s ^ 7 * y2 ^ 2 := by ring
      rw [e]; exact step2.trans step3
    exact le_of_mul_le_mul_left this (by positivity)
  · push_neg at hcase
    clear hF1 hF2 hS0 hode
    have hμ : (0 : ℝ) ≤ (n : ℝ) * (n + 1) - 2 := by nlinarith
    obtain ⟨m, hm⟩ : ∃ m : ℝ, 0 ≤ m ∧ (n : ℝ) = m + 2 := ⟨n - 2, by linarith, by ring⟩
    have hs3 : (s * (3 * n - 1)) ^ 3 ≤ 64 := by
      have := pow_le_pow_left₀ (mul_pos hs0 (by linarith)).le hcase.le 3
      norm_num at this; linarith
    have hpoly : π * (((n : ℝ) * (n + 1) - 2) * ((n : ℝ) * (n + 1) / 2) ^ 2) * 64 ≤
        32 * (n : ℝ) ^ 3 * (3 * n - 1) ^ 3 := by
      have hq : 0 ≤ ((n : ℝ) * (n + 1) - 2) * ((n : ℝ) * (n + 1) / 2) ^ 2 :=
        mul_nonneg hμ (sq_nonneg _)
      have h1 : π * (((n : ℝ) * (n + 1) - 2) * ((n : ℝ) * (n + 1) / 2) ^ 2) * 64 ≤
          4 * (((n : ℝ) * (n + 1) - 2) * ((n : ℝ) * (n + 1) / 2) ^ 2) * 64 := by
        have : π ≤ 4 := by linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hq) (by norm_num)
      have h2 : 4 * (((n : ℝ) * (n + 1) - 2) * ((n : ℝ) * (n + 1) / 2) ^ 2) * 64 ≤
          32 * (n : ℝ) ^ 3 * (3 * n - 1) ^ 3 := by
        rw [hm.2]
        have hm0 := hm.1
        have e : 32 * (m + 2) ^ 3 * (3 * (m + 2) - 1) ^ 3 -
            4 * (((m + 2) * (m + 2 + 1) - 2) * ((m + 2) * (m + 2 + 1) / 2) ^ 2) * 64 =
            32 * (m + 2) ^ 2 * (178 + 437 * m + 409 * m ^ 2 + 167 * m ^ 3 + 25 * m ^ 4) := by ring
        have : 0 ≤ 32 * (m + 2) ^ 2 * (178 + 437 * m + 409 * m ^ 2 + 167 * m ^ 3 + 25 * m ^ 4) := by
          positivity
        linarith
      exact h1.trans h2
    have hpos : 0 < (3 * (n : ℝ) - 1) ^ 3 := by
      have : 0 < 3 * (n : ℝ) - 1 := by linarith
      positivity
    have key : ((s ^ 2) ^ 2 * s * y2 ^ 2 * π) * (3 * n - 1) ^ 3 ≤
        (32 * (n : ℝ) ^ 3) * (3 * n - 1) ^ 3 := by
      have hQ : 0 ≤ ((n : ℝ) * (n + 1) - 2) * ((n : ℝ) * (n + 1) / 2) ^ 2 :=
        mul_nonneg hμ (sq_nonneg _)
      calc ((s ^ 2) ^ 2 * s * y2 ^ 2 * π) * (3 * n - 1) ^ 3
          = π * (s * (3 * n - 1)) ^ 3 * (s ^ 2 * y2 ^ 2) := by ring
        _ ≤ π * 64 * (((n : ℝ) * (n + 1) - 2) * ((n : ℝ) * (n + 1) / 2) ^ 2) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hs3 hpi.le) hC (by positivity)
              (by positivity)
        _ ≤ _ := by linarith
    exact (le_div_iff₀ hpi).2 (le_of_mul_le_mul_right key hpos)


theorem legendre_deriv_interior_bounds (n : ℕ) (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    |(legendre n).derivative.eval x| ≤
      2 * Real.sqrt 2 / Real.sqrt Real.pi * Real.sqrt (n : ℝ) /
        (1 - x ^ 2) ^ (3 / 4 : ℝ) ∧
      |(legendre n).derivative.derivative.eval x| ≤
        4 * Real.sqrt 2 / Real.sqrt Real.pi * (n : ℝ) ^ (3 / 2 : ℝ) /
          (1 - x ^ 2) ^ (5 / 4 : ℝ) := by
  have hw : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have h1 := legendre_deriv_sq_bound n hn hx
  have h2 := legendre_deriv2_sq_bound n hn hx
  have hpi := Real.pi_pos
  set r := (1 - x ^ 2) ^ (1 / 4 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hw _
  have hpow : ∀ k : ℕ, (1 - x ^ 2) ^ ((1 / 4 : ℝ) * k) = r ^ k := fun k =>
    Real.rpow_mul_natCast hw.le _ k
  have h34 : (1 - x ^ 2) ^ (3 / 4 : ℝ) = r ^ 3 := by
    rw [← hpow 3]; norm_num
  have h54 : (1 - x ^ 2) ^ (5 / 4 : ℝ) = r ^ 5 := by
    rw [← hpow 5]; norm_num
  have hsq : Real.sqrt (1 - x ^ 2) = r ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← hpow 2]; norm_num
  have hw4 : 1 - x ^ 2 = r ^ 4 := by
    rw [← hpow 4]; norm_num
  rw [hsq, hw4] at h1 h2
  rw [h34, h54]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspi : Real.sqrt π ^ 2 = π := Real.sq_sqrt hpi.le
  have hspi0 : 0 < Real.sqrt π := Real.sqrt_pos.2 hpi
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · rw [le_div_iff₀ (by positivity)]
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero]
    rw [mul_pow, sq_abs, mul_pow, div_pow, mul_pow, hs2, hspi, Real.sq_sqrt hn0]
    calc (legendre n).derivative.eval x ^ 2 * (r ^ 3) ^ 2
        = r ^ 4 * r ^ 2 * (legendre n).derivative.eval x ^ 2 := by ring
      _ ≤ 8 * n / π := h1
      _ = 2 ^ 2 * 2 / π * n := by ring
  · rw [le_div_iff₀ (by positivity)]
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero]
    have hn3 : ((n : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (n : ℝ) ^ 3 := by
      rw [← Real.rpow_mul_natCast hn0]; norm_num
    rw [mul_pow, sq_abs, mul_pow, div_pow, mul_pow, hs2, hspi, hn3]
    calc (legendre n).derivative.derivative.eval x ^ 2 * (r ^ 5) ^ 2
        = (r ^ 4) ^ 2 * r ^ 2 * (legendre n).derivative.derivative.eval x ^ 2 := by ring
      _ ≤ 32 * (n : ℝ) ^ 3 / π := h2
      _ = 4 ^ 2 * 2 / π * (n : ℝ) ^ 3 := by ring

theorem legendre_at_one (n : ℕ) (x : ℝ) :
    (legendre n).eval x =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * ((n + k).choose k : ℝ) * ((x - 1) / 2) ^ k := by
  have hdeg : (legendreShift n).natDegree < n + 1 := by
    have := natDegree_comp_le (p := legendre n) (q := C 2 * X + C 1)
    have h2 : (C (2 : ℝ) * X + C 1).natDegree ≤ 1 := natDegree_linear_le
    rw [(legendre_natDegree_and_lc n).1] at this
    unfold legendreShift
    nlinarith
  have := eval_eq_sum_range' hdeg ((x - 1) / 2)
  rw [legendreShift_eval, show 2 * ((x - 1) / 2) + 1 = x by ring] at this
  rw [this]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [legendreShift_coeff]
  rfl

/-- Absolute tail bound for the expansion at one. -/
theorem legendre_at_one_tail (n K : ℕ) (hK : K ≤ n) {x α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hratio : ((n - K : ℕ) : ℝ) * ((n : ℝ) + K + 1) /
      (((K : ℝ) + 1) ^ 2) * |(x - 1) / 2| ≤ α) :
    |(legendre n).eval x -
      ∑ k ∈ Finset.range K,
        (n.choose k : ℝ) * ((n + k).choose k : ℝ) * ((x - 1) / 2) ^ k|
      ≤ (n.choose K : ℝ) * ((n + K).choose K : ℝ) *
        |(x - 1) / 2| ^ K / (1 - α) := by
  set y := (x - 1) / 2 with hy
  set t : ℕ → ℝ := fun k => atOneCoeff n k * |y| ^ k with ht
  have hc0 : ∀ k, 0 ≤ atOneCoeff n k := fun k => by unfold atOneCoeff; positivity
  have ht0 : ∀ k, 0 ≤ t k := fun k => mul_nonneg (hc0 k) (pow_nonneg (abs_nonneg _) _)
  have hstep : ∀ j, t (K + j) ≤ α ^ j * t K := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rcases le_or_gt n (K + j) with hn | hn
      · have : atOneCoeff n (K + (j + 1)) = 0 := by
          unfold atOneCoeff; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
        simp only [ht, this, zero_mul]
        exact mul_nonneg (pow_nonneg hα0 _) (ht0 K)
      · set k := K + j
        have hrec := atOneCoeff_rec n k
        have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
        have hnk : ((n - K : ℕ) : ℝ) = (n : ℝ) - K := Nat.cast_sub hK
        rw [hnk] at hratio
        have hkK : (K : ℝ) ≤ k := by simp [k]
        have hkn : (k : ℝ) < n := by exact_mod_cast hn
        -- the ratio is decreasing in `k`
        have hmono : ((n : ℝ) - k) * ((n : ℝ) + k + 1) * ((K : ℝ) + 1) ^ 2 ≤
            ((n : ℝ) - K) * ((n : ℝ) + K + 1) * ((k : ℝ) + 1) ^ 2 := by
          have h1 : (0 : ℝ) ≤ (n : ℝ) - k := by linarith
          have h2 : ((n : ℝ) + k + 1) * ((K : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + K + 1) * ((k : ℝ) + 1) ^ 2 := by
            have hn0 : (0 : ℝ) ≤ n := by positivity
            have : 0 ≤ ((k : ℝ) - K) * (n * (k + K + 2) + (K + 1) * (k + 1)) :=
              mul_nonneg (by linarith) (by positivity)
            nlinarith [this]
          calc ((n : ℝ) - k) * ((n : ℝ) + k + 1) * ((K : ℝ) + 1) ^ 2
              = ((n : ℝ) - k) * (((n : ℝ) + k + 1) * ((K : ℝ) + 1) ^ 2) := by ring
            _ ≤ ((n : ℝ) - K) * (((n : ℝ) + K + 1) * ((k : ℝ) + 1) ^ 2) := by
                apply mul_le_mul (by linarith) h2 (by positivity) (by linarith)
            _ = _ := by ring
        have hr : ((n : ℝ) - k) * ((n : ℝ) + k + 1) / ((k : ℝ) + 1) ^ 2 * |y| ≤ α := by
          refine le_trans ?_ hratio
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          exact hmono
        have : t (k + 1) = ((n : ℝ) - k) * ((n : ℝ) + k + 1) / ((k : ℝ) + 1) ^ 2 * |y| * t k := by
          simp only [ht]
          rw [show atOneCoeff n (k + 1) = ((n : ℝ) - k) * ((n : ℝ) + k + 1) * atOneCoeff n k /
            ((k : ℝ) + 1) ^ 2 by rw [eq_div_iff (by positivity)]; linear_combination hrec]
          ring
        rw [show K + (j + 1) = k + 1 by omega, this, pow_succ]
        calc _ ≤ α * t k := mul_le_mul_of_nonneg_right hr (ht0 k)
          _ ≤ α * (α ^ j * t K) := mul_le_mul_of_nonneg_left ih hα0
          _ = _ := by ring
  rw [legendre_at_one, ← hy, ← Finset.sum_Ico_eq_sub _ (by omega : K ≤ n + 1),
    Finset.sum_Ico_eq_sum_range]
  calc _ ≤ ∑ j ∈ Finset.range (n + 1 - K), t (K + j) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
        simp only [ht, atOneCoeff, abs_mul, abs_pow, Nat.abs_cast]
    _ ≤ ∑ j ∈ Finset.range (n + 1 - K), α ^ j * t K := Finset.sum_le_sum fun j _ => hstep j
    _ = (∑ j ∈ Finset.range (n + 1 - K), α ^ j) * t K := by rw [Finset.sum_mul]
    _ ≤ (1 - α)⁻¹ * t K := by
        apply mul_le_mul_of_nonneg_right _ (ht0 K)
        rw [geom_sum_eq hα1.ne, div_eq_mul_inv]
        have : 0 < 1 - α := by linarith
        rw [show (α ^ (n + 1 - K) - 1) * (α - 1)⁻¹ = (1 - α ^ (n + 1 - K)) * (1 - α)⁻¹ by
          rw [← neg_sub 1 α, inv_neg]; ring]
        have := pow_nonneg hα0 (n + 1 - K)
        calc (1 - α ^ (n + 1 - K)) * (1 - α)⁻¹ ≤ 1 * (1 - α)⁻¹ :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = _ := one_mul _
    _ = _ := by simp only [ht, atOneCoeff]; field_simp

/-- Parity-aware monomial expansion; coefficients are generated by ratios at runtime. -/
theorem legendre_at_zero (n : ℕ) (x : ℝ) :
    (legendre n).eval x = (2 : ℝ)⁻¹ ^ n *
      ∑ k ∈ Finset.range (n / 2 + 1),
        (-1 : ℝ) ^ k * (n.choose k : ℝ) *
          ((2 * n - 2 * k).choose n : ℝ) * x ^ (n - 2 * k) := by
  have hdeg : (legendre n).natDegree < n + 1 := by rw [(legendre_natDegree_and_lc n).1]; omega
  rw [eval_eq_sum_range' hdeg, Finset.mul_sum]
  have hinj : Set.InjOn (fun k => n - 2 * k) (Finset.range (n / 2 + 1) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at hab
    omega
  have hsub : (Finset.range (n / 2 + 1)).image (fun k => n - 2 * k) ⊆ Finset.range (n + 1) := by
    intro j hj
    simp only [Finset.mem_image, Finset.mem_range] at hj ⊢
    omega
  rw [← Finset.sum_subset hsub, Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [legendre_coeff_formula n k (by simp at hk; omega), atZeroCoeff]
    ring
  · intro j hj hjS
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and] at hj hjS
    have hnd : ¬ (2 ∣ n - j) := by
      intro ⟨c, hc⟩
      exact hjS c (by omega) (by omega)
    have hodd : ∃ k, 2 * k + 1 ≤ n ∧ j = n - 2 * k - 1 :=
      ⟨(n - j - 1) / 2, by omega, by omega⟩
    obtain ⟨k, hk, rfl⟩ := hodd
    rw [legendre_coeff_odd n k hk, zero_mul]

def asympCoeff (n k : ℕ) : ℝ :=
  (Real.Gamma ((k : ℝ) + 1 / 2)) ^ 2 * Real.Gamma ((n : ℝ) + 1) /
    (Real.pi * 2 ^ k * Real.Gamma ((n : ℝ) + k + 3 / 2) *
      Real.Gamma ((k : ℝ) + 1))

theorem asympCoeff_zero (n : ℕ) :
    asympCoeff n 0 =
      (4 : ℝ) ^ n /
        (Real.sqrt Real.pi * ((n : ℝ) + 1 / 2) * ((2 * n).choose n : ℝ)) := by
  unfold asympCoeff
  have hG := Gamma_nat_add_half_mul n
  rw [Nat.cast_choose ℝ (by omega : n ≤ 2 * n), show 2 * n - n = n by omega]
  simp only [CharP.cast_eq_zero, zero_add, add_zero, pow_zero, mul_one]
  rw [Real.Gamma_one_half_eq, Real.Gamma_one, Real.Gamma_nat_eq_factorial,
    show (n : ℝ) + 3 / 2 = ((n : ℝ) + 1 / 2) + 1 by ring, Real.Gamma_add_one (by positivity)]
  have hpi := Real.pi_pos
  have hs : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi.le
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 hpi
  have hg : 0 < Real.Gamma ((n : ℝ) + 1 / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hf : (0 : ℝ) < (2 * n).factorial := by positivity
  have hf' : (0 : ℝ) < n.factorial := by positivity
  have hΓ : Real.Gamma ((n : ℝ) + 1 / 2) =
      ((2 * n).factorial : ℝ) * Real.sqrt Real.pi / (4 ^ n * n.factorial) := by
    rw [eq_div_iff (by positivity)]; linear_combination hG
  rw [hs, hΓ]
  field_simp

theorem asympCoeff_succ (n k : ℕ) :
    asympCoeff n (k + 1) = asympCoeff n k *
      (2 * (k : ℝ) + 1) ^ 2 /
        (4 * ((k : ℝ) + 1) * (2 * (n : ℝ) + 2 * k + 3)) := by
  unfold asympCoeff
  push_cast
  have hA : Real.Gamma ((k : ℝ) + 1 + 1 / 2) = ((k : ℝ) + 1 / 2) * Real.Gamma ((k : ℝ) + 1 / 2) := by
    rw [show (k : ℝ) + 1 + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 by ring, Real.Gamma_add_one (by positivity)]
  have hB : Real.Gamma ((n : ℝ) + ((k : ℝ) + 1) + 3 / 2) =
      ((n : ℝ) + k + 3 / 2) * Real.Gamma ((n : ℝ) + k + 3 / 2) := by
    rw [show (n : ℝ) + ((k : ℝ) + 1) + 3 / 2 = ((n : ℝ) + k + 3 / 2) + 1 by ring,
      Real.Gamma_add_one (by positivity)]
  have hC : Real.Gamma ((k : ℝ) + 1 + 1) = ((k : ℝ) + 1) * Real.Gamma ((k : ℝ) + 1) := by
    rw [Real.Gamma_add_one (by positivity)]
  rw [hA, hB, hC]
  have h1 : 0 < Real.Gamma ((k : ℝ) + 1 / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : 0 < Real.Gamma ((n : ℝ) + k + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h3 : 0 < Real.Gamma ((k : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have h4 : 0 < Real.Gamma ((n : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have := Real.pi_pos
  field_simp
  ring

/-- The asymptotic coefficients as Wallis-type integrals. -/
lemma asympCoeff_eq_W (n k : ℕ) :
    asympCoeff n k = 2 * Asymp.cc k * Asymp.W n k / (Real.sqrt Real.pi * 2 ^ k) := by
  have hsqpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  induction k with
  | zero =>
    rw [asympCoeff_zero, Asymp.W_zero, Nat.centralBinom_eq_two_mul_choose]
    simp only [Asymp.cc, pow_zero, mul_one]
    have : (0 : ℝ) < ((2 * n).choose n : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    field_simp
  | succ k ih =>
    rw [asympCoeff_succ, ih, Asymp.W_succ_right]
    simp only [Asymp.cc]
    field_simp
    ring

/-- Stieltjes' expansion of `P_n(cos θ)` with error at most twice the first omitted term
(the cosine replaced by `1`). The hypothesis `hn` is not needed by the proof; it is kept
so that the signature matches the original contract. -/
theorem legendre_asymptotic (n K : ℕ) (hn : 0 < n) (hK : 0 < K)
    {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    |(legendre n).eval (Real.cos θ) -
      Real.sqrt (2 / (Real.pi * Real.sin θ)) *
        ∑ k ∈ Finset.range K, asympCoeff n k *
          Real.cos (((n : ℝ) + k + 1 / 2) * θ -
            ((k : ℝ) + 1 / 2) * Real.pi / 2) / Real.sin θ ^ k|
      ≤ 2 * Real.sqrt (2 / (Real.pi * Real.sin θ)) *
        asympCoeff n K / Real.sin θ ^ K := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hpi := Real.pi_pos
  have hsqpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 hpi
  have hsqs : 0 < Real.sqrt (Real.sin θ) := Real.sqrt_pos.2 hs
  have hsq2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have e1 : Real.sqrt (2 / (Real.pi * Real.sin θ)) =
      Real.sqrt 2 / (Real.sqrt Real.pi * Real.sqrt (Real.sin θ)) := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_mul hpi.le]
  have e2 : Real.sqrt (2 * Real.sin θ) = Real.sqrt 2 * Real.sqrt (Real.sin θ) :=
    Real.sqrt_mul (by norm_num) _
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hπ2 : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi.le
  have hcoef : ∀ k : ℕ, 4 / Real.pi * (Asymp.cc k * Asymp.W n k) /
      ((2 * Real.sin θ) ^ k * Real.sqrt (2 * Real.sin θ)) =
      Real.sqrt (2 / (Real.pi * Real.sin θ)) * asympCoeff n k / Real.sin θ ^ k := by
    intro k
    rw [asympCoeff_eq_W, e1, e2, mul_pow]
    field_simp
    rw [hπ2, h2]
    ring
  have key := Asymp.legendre_expansion hθ0 hθπ n m
  have hsum : Real.sqrt (2 / (Real.pi * Real.sin θ)) *
      ∑ k ∈ Finset.range (m + 1), asympCoeff n k *
        Real.cos (((n : ℝ) + k + 1 / 2) * θ - ((k : ℝ) + 1 / 2) * Real.pi / 2) /
          Real.sin θ ^ k =
      ∑ k ∈ Finset.range (m + 1), 4 / Real.pi * (Asymp.cc k * Asymp.W n k) *
        (Real.cos (((n : ℝ) + k + 1 / 2) * θ - ((k : ℝ) + 1 / 2) * Real.pi / 2) /
          ((2 * Real.sin θ) ^ k * Real.sqrt (2 * Real.sin θ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := hcoef k
    rw [show Real.sqrt (2 / (Real.pi * Real.sin θ)) * (asympCoeff n k *
        Real.cos (((n : ℝ) + k + 1 / 2) * θ - ((k : ℝ) + 1 / 2) * Real.pi / 2) / Real.sin θ ^ k) =
        (Real.sqrt (2 / (Real.pi * Real.sin θ)) * asympCoeff n k / Real.sin θ ^ k) *
        Real.cos (((n : ℝ) + k + 1 / 2) * θ - ((k : ℝ) + 1 / 2) * Real.pi / 2) by ring, ← this]
    ring
  rw [hsum]
  refine key.trans (le_of_eq ?_)
  rw [show 2 * Real.sqrt (2 / (Real.pi * Real.sin θ)) * asympCoeff n (m + 1) /
      Real.sin θ ^ (m + 1) = 2 * (Real.sqrt (2 / (Real.pi * Real.sin θ)) * asympCoeff n (m + 1) /
      Real.sin θ ^ (m + 1)) by ring, ← hcoef (m + 1)]
  ring

end Intgrl
