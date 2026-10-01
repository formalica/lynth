import Mathlib
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Lynth.HGIdentities.Common
import Lynth.Hypergeometric

/-!
# The quadratic transformation `₂F̃₁(a, a - 1/2; 2a; z) = 2^(2a-1) (√(1-z) + 1)^(1-2a) / Γ(2a)`

This file proves the closed form of the regularized Gauss hypergeometric function with parameters
`(a, a - 1/2; 2a)`.

Recall that the *regularized* function carries an extra factor `1 / Γ(2a)` compared with the
classical `₂F₁`; the classical identity is
`₂F₁(a, a - 1/2; 2a; z) = 2^(2a-1) (√(1-z) + 1)^(1-2a)`.

The proof runs as follows.

* The closed form `gauss2F1Closed a` is holomorphic on the unit disc and satisfies the
  hypergeometric differential equation `z(1-z) y'' + (2a - (2a + 1/2) z) y' - a(a-1/2) y = 0`.
* Differentiating this equation `n` times at `0` yields the two–term recursion
  `(n + 2a) y⁽ⁿ⁺¹⁾(0) = (n + a)(n + a - 1/2) y⁽ⁿ⁾(0)`,
  which is exactly the recursion satisfied by `n! Γ(2a) cₙ`, where `cₙ` are the coefficients of the
  regularized hypergeometric series.
* Taylor's theorem for holomorphic functions then identifies the two functions on the unit disc.
* Finally, Abel's limit theorem extends the identity to the boundary `‖z‖ = 1`.
-/

open scoped Nat
open Metric

namespace Complex

/-- The closed form `2 ^ (2a-1) * (√(1-z) + 1) ^ (1-2a)`. -/
private noncomputable def gauss2F1Closed (a z : ℂ) : ℂ :=
  2 ^ (2 * a - 1) * (Complex.sqrt (1 - z) + 1) ^ (1 - 2 * a)

/-- The first derivative of `gauss2F1Closed a`. -/
private noncomputable def gauss2F1Closed' (a z : ℂ) : ℂ :=
  (2 * a - 1) * gauss2F1Closed a z /
    (2 * Complex.sqrt (1 - z) * (Complex.sqrt (1 - z) + 1))

/-- The second derivative of `gauss2F1Closed a`. -/
private noncomputable def gauss2F1Closed'' (a z : ℂ) : ℂ :=
  (2 * a - 1) * gauss2F1Closed a z *
      ((2 * a - 1) * Complex.sqrt (1 - z) + 2 * Complex.sqrt (1 - z) + 1) /
    (4 * Complex.sqrt (1 - z) * (1 - z) * (Complex.sqrt (1 - z) + 1) ^ 2)

section Disc

variable {a z : ℂ}

private theorem gauss2F1Closed_ne_zero (hz : ‖z‖ < 1) : gauss2F1Closed a z ≠ 0 := by
  refine mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)) ?_
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (sqrt_add_one_ne_zero hz))

end Disc

section Derivatives

variable {a z : ℂ}

private theorem hasDerivAt_gauss2F1Closed (hz : ‖z‖ < 1) :
    HasDerivAt (gauss2F1Closed a) (gauss2F1Closed' a z) z := by
  have h1 : HasDerivAt (fun w => Complex.sqrt (1 - w) + 1)
      (-(1 / (2 * Complex.sqrt (1 - z)))) z := by
    simpa using (hasDerivAt_sqrt_one_sub hz).add_const 1
  have hmem : (Complex.sqrt (1 - z) + 1) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have := re_sqrt_pos hz
    simp only [Complex.add_re, Complex.one_re]
    linarith
  refine ((h1.cpow_const hmem (c := 1 - 2 * a)).const_mul
    ((2 : ℂ) ^ (2 * a - 1))).congr_deriv ?_
  have hs : Complex.sqrt (1 - z) ≠ 0 := sqrt_ne_zero' hz
  have hs1 : Complex.sqrt (1 - z) + 1 ≠ 0 := sqrt_add_one_ne_zero hz
  rw [gauss2F1Closed', gauss2F1Closed, Complex.cpow_sub _ _ hs1, Complex.cpow_one]
  field_simp
  ring

private theorem hasDerivAt_gauss2F1Closed' (hz : ‖z‖ < 1) :
    HasDerivAt (gauss2F1Closed' a) (gauss2F1Closed'' a z) z := by
  have hds := hasDerivAt_sqrt_one_sub hz
  have hN : HasDerivAt (fun w => (2 * a - 1) * gauss2F1Closed a w)
      ((2 * a - 1) * gauss2F1Closed' a z) z := (hasDerivAt_gauss2F1Closed hz).const_mul _
  have hD : HasDerivAt (fun w => 2 * Complex.sqrt (1 - w) * (Complex.sqrt (1 - w) + 1))
      (2 * (-(1 / (2 * Complex.sqrt (1 - z)))) * (Complex.sqrt (1 - z) + 1)
        + 2 * Complex.sqrt (1 - z) * (-(1 / (2 * Complex.sqrt (1 - z))))) z :=
    (hds.const_mul 2).mul (hds.add_const 1)
  have hDne : 2 * Complex.sqrt (1 - z) * (Complex.sqrt (1 - z) + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (sqrt_ne_zero' hz)) (sqrt_add_one_ne_zero hz)
  refine (hN.div hD hDne).congr_deriv ?_
  rw [gauss2F1Closed'', gauss2F1Closed']
  have hsq : Complex.sqrt (1 - z) ^ 2 = 1 - z := sqrt_sq_eq _
  have hs : Complex.sqrt (1 - z) ≠ 0 := sqrt_ne_zero' hz
  have hs1 : Complex.sqrt (1 - z) + 1 ≠ 0 := sqrt_add_one_ne_zero hz
  set s := Complex.sqrt (1 - z) with hsdef
  clear_value s
  rw [← hsq]
  field_simp
  ring

/-- The hypergeometric differential equation for the closed form. -/
private theorem gauss2F1Closed_ode (hz : ‖z‖ < 1) :
    z * (1 - z) * gauss2F1Closed'' a z + (2 * a - (2 * a + 1 / 2) * z) * gauss2F1Closed' a z
      - a * (a - 1 / 2) * gauss2F1Closed a z = 0 := by
  rw [gauss2F1Closed'', gauss2F1Closed']
  have hsq : Complex.sqrt (1 - z) ^ 2 = 1 - z := sqrt_sq_eq _
  have hs : Complex.sqrt (1 - z) ≠ 0 := sqrt_ne_zero' hz
  have hs1 : Complex.sqrt (1 - z) + 1 ≠ 0 := sqrt_add_one_ne_zero hz
  set F := gauss2F1Closed a z with hF
  clear_value F
  set s := Complex.sqrt (1 - z) with hsdef
  clear_value s
  have hz' : z = 1 - s ^ 2 := by rw [hsq]; ring
  subst hz'
  field_simp
  ring

private theorem differentiableOn_gauss2F1Closed :
    DifferentiableOn ℂ (gauss2F1Closed a) (ball (0 : ℂ) 1) := fun w hw =>
  ((hasDerivAt_gauss2F1Closed (by simpa using mem_ball_zero_iff.mp hw)).differentiableAt).differentiableWithinAt

private theorem gauss2F1Closed_zero : gauss2F1Closed a 0 = 1 := by
  rw [gauss2F1Closed]
  simp only [sub_zero, Complex.sqrt_one]
  rw [show (1 : ℂ) + 1 = 2 by ring, ← Complex.cpow_add _ _ two_ne_zero]
  norm_num

end Derivatives

section IteratedDeriv

/-- Leibniz rule for multiplication by `z`, evaluated at `0`. -/
private theorem iteratedDeriv_id_mul {g : ℂ → ℂ} {n : ℕ}
    (hg : ContDiffAt ℂ ((n + 1 : ℕ) : WithTop ℕ∞) g 0) :
    iteratedDeriv (n + 1) (fun z => z * g z) 0 = (n + 1) * iteratedDeriv n g 0 := by
  have hid : ContDiffAt ℂ ((n + 1 : ℕ) : WithTop ℕ∞) (fun z : ℂ => z) 0 := contDiff_id.contDiffAt
  have key := iteratedDeriv_mul (n := n + 1) (x := (0 : ℂ)) (f := fun z : ℂ => z) (g := g) hid hg
  rw [show (fun z : ℂ => z * g z) = (fun z : ℂ => z) * g from rfl, key, Finset.sum_eq_single 1]
  · simp [iteratedDeriv_id, show (fun z : ℂ => z) = id from rfl]
  · intro i hi hne
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp [show (fun z : ℂ => z) = id from rfl, iteratedDeriv_id]
    · simp [show (fun z : ℂ => z) = id from rfl, iteratedDeriv_id, show i ≠ 0 by omega,
        show i ≠ 1 by omega]
  · intro h; simp at h

/-- Multiplication by `z` shifts the derivatives at `0`; the `n = 0` case is covered by the
vanishing prefactor. -/
private theorem iteratedDeriv_id_mul' {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) (n : ℕ) :
    iteratedDeriv n (fun z => z * h z) 0 = (n : ℂ) * iteratedDeriv (n - 1) h 0 := by
  cases n with
  | zero => simp
  | succ m =>
    have := iteratedDeriv_id_mul (n := m) (g := h) hh.contDiffAt
    push_cast
    simpa using this

/-- Expansion of the `n`-th derivative at `0` of the hypergeometric differential operator applied
to an analytic function. -/
private theorem iteratedDeriv_hypergeometricOperator {f : ℂ → ℂ} (hfa : AnalyticAt ℂ f 0) (n : ℕ)
    (A B C : ℂ) :
    iteratedDeriv n (fun w : ℂ => w * deriv (deriv f) w - w * (w * deriv (deriv f) w)
        + A * deriv f w - B * (w * deriv f w) - C * f w) 0
      = (n : ℂ) * iteratedDeriv (n - 1) (deriv (deriv f)) 0
        - (n : ℂ) * ((n - 1 : ℕ) : ℂ) * iteratedDeriv (n - 1 - 1) (deriv (deriv f)) 0
        + A * iteratedDeriv n (deriv f) 0
        - B * ((n : ℂ) * iteratedDeriv (n - 1) (deriv f) 0)
        - C * iteratedDeriv n f 0 := by
  have hd1 : AnalyticAt ℂ (deriv f) 0 := hfa.deriv
  have hd2 : AnalyticAt ℂ (deriv (deriv f)) 0 := hd1.deriv
  have A1 : AnalyticAt ℂ (fun w : ℂ => w * deriv (deriv f) w) 0 := analyticAt_id.mul hd2
  have A2 : AnalyticAt ℂ (fun w : ℂ => w * (w * deriv (deriv f) w)) 0 := analyticAt_id.mul A1
  have A1' : AnalyticAt ℂ (fun w : ℂ => w * deriv f w) 0 := analyticAt_id.mul hd1
  have A3 : AnalyticAt ℂ (fun w : ℂ => A * deriv f w) 0 := analyticAt_const.mul hd1
  have A4 : AnalyticAt ℂ (fun w : ℂ => B * (w * deriv f w)) 0 := analyticAt_const.mul A1'
  have A5 : AnalyticAt ℂ (fun w : ℂ => C * f w) 0 := analyticAt_const.mul hfa
  have s1 : iteratedDeriv n (fun w : ℂ => w * deriv (deriv f) w - w * (w * deriv (deriv f) w)) 0
      = iteratedDeriv n (fun w : ℂ => w * deriv (deriv f) w) 0
        - iteratedDeriv n (fun w : ℂ => w * (w * deriv (deriv f) w)) 0 :=
    iteratedDeriv_fun_sub A1.contDiffAt A2.contDiffAt
  have s2 : iteratedDeriv n (fun w : ℂ => (w * deriv (deriv f) w - w * (w * deriv (deriv f) w))
        + A * deriv f w) 0
      = iteratedDeriv n (fun w : ℂ => w * deriv (deriv f) w - w * (w * deriv (deriv f) w)) 0
        + iteratedDeriv n (fun w : ℂ => A * deriv f w) 0 :=
    iteratedDeriv_fun_add (A1.sub A2).contDiffAt A3.contDiffAt
  have s3 : iteratedDeriv n (fun w : ℂ => ((w * deriv (deriv f) w - w * (w * deriv (deriv f) w))
        + A * deriv f w) - B * (w * deriv f w)) 0
      = iteratedDeriv n (fun w : ℂ => (w * deriv (deriv f) w - w * (w * deriv (deriv f) w))
          + A * deriv f w) 0
        - iteratedDeriv n (fun w : ℂ => B * (w * deriv f w)) 0 :=
    iteratedDeriv_fun_sub ((A1.sub A2).add A3).contDiffAt A4.contDiffAt
  have s4 : iteratedDeriv n (fun w : ℂ => (((w * deriv (deriv f) w - w * (w * deriv (deriv f) w))
        + A * deriv f w) - B * (w * deriv f w)) - C * f w) 0
      = iteratedDeriv n (fun w : ℂ => ((w * deriv (deriv f) w - w * (w * deriv (deriv f) w))
          + A * deriv f w) - B * (w * deriv f w)) 0
        - iteratedDeriv n (fun w : ℂ => C * f w) 0 :=
    iteratedDeriv_fun_sub (((A1.sub A2).add A3).sub A4).contDiffAt A5.contDiffAt
  have c1 : iteratedDeriv n (fun w : ℂ => C * f w) 0 = C * iteratedDeriv n f 0 :=
    iteratedDeriv_const_mul _ hfa.contDiffAt
  have c2 : iteratedDeriv n (fun w : ℂ => B * (w * deriv f w)) 0
      = B * iteratedDeriv n (fun w : ℂ => w * deriv f w) 0 :=
    iteratedDeriv_const_mul _ A1'.contDiffAt
  have c3 : iteratedDeriv n (fun w : ℂ => A * deriv f w) 0 = A * iteratedDeriv n (deriv f) 0 :=
    iteratedDeriv_const_mul _ hd1.contDiffAt
  rw [s4, s3, s2, s1, c1, c2, c3, iteratedDeriv_id_mul' hd2 n, iteratedDeriv_id_mul' hd1 n,
    iteratedDeriv_id_mul' A1 n, iteratedDeriv_id_mul' hd2 (n - 1)]
  ring

variable {a : ℂ}

/-- The two-term recursion for the derivatives of the closed form at `0`. -/
private theorem iteratedDeriv_gauss2F1Closed_succ (n : ℕ) :
    ((n : ℂ) + 2 * a) * iteratedDeriv (n + 1) (gauss2F1Closed a) 0 =
      ((n : ℂ) + a) * ((n : ℂ) + a - 1 / 2) * iteratedDeriv n (gauss2F1Closed a) 0 := by
  have hball : ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) := isOpen_ball.mem_nhds (by simp)
  have hfa : AnalyticAt ℂ (gauss2F1Closed a) 0 :=
    differentiableOn_gauss2F1Closed.analyticAt hball
  have hd1 : deriv (gauss2F1Closed a) =ᶠ[nhds 0] gauss2F1Closed' a := by
    filter_upwards [hball] with w hw
    exact (hasDerivAt_gauss2F1Closed (by simpa using mem_ball_zero_iff.mp hw)).deriv
  have hd2 : deriv (deriv (gauss2F1Closed a)) =ᶠ[nhds 0] gauss2F1Closed'' a := by
    filter_upwards [hball] with w hw
    have hw' : ‖w‖ < 1 := by simpa using mem_ball_zero_iff.mp hw
    have h1 : deriv (deriv (gauss2F1Closed a)) w = deriv (gauss2F1Closed' a) w := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by simpa using hw'))] with v hv
      exact (hasDerivAt_gauss2F1Closed (by simpa using mem_ball_zero_iff.mp hv)).deriv
    rw [h1, (hasDerivAt_gauss2F1Closed' hw').deriv]
  have hE : (fun w : ℂ => w * deriv (deriv (gauss2F1Closed a)) w
      - w * (w * deriv (deriv (gauss2F1Closed a)) w)
      + (2 * a) * deriv (gauss2F1Closed a) w
      - (2 * a + 1 / 2) * (w * deriv (gauss2F1Closed a) w)
      - (a * (a - 1 / 2)) * gauss2F1Closed a w) =ᶠ[nhds 0] fun _ => 0 := by
    filter_upwards [hball, hd1, hd2] with w hw hw1 hw2
    have hw' : ‖w‖ < 1 := by simpa using mem_ball_zero_iff.mp hw
    rw [hw1, hw2]
    linear_combination gauss2F1Closed_ode (a := a) hw'
  have h0 := hE.iteratedDeriv_eq n
  rw [iteratedDeriv_hypergeometricOperator hfa n (2 * a) (2 * a + 1 / 2) (a * (a - 1 / 2)),
    show iteratedDeriv n (fun _ : ℂ => (0 : ℂ)) 0 = 0 from by simp] at h0
  have hshift1 : ∀ m : ℕ, iteratedDeriv m (deriv (gauss2F1Closed a)) 0
      = iteratedDeriv (m + 1) (gauss2F1Closed a) 0 := fun m => by rw [iteratedDeriv_succ']
  have hshift2 : ∀ m : ℕ, iteratedDeriv m (deriv (deriv (gauss2F1Closed a))) 0
      = iteratedDeriv (m + 2) (gauss2F1Closed a) 0 := by
    intro m
    rw [show m + 2 = (m + 1) + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_succ']
  match n with
  | 0 =>
    simp only [Nat.cast_zero, hshift1, hshift2] at h0 ⊢
    linear_combination h0
  | 1 =>
    norm_num [hshift1, hshift2] at h0 ⊢
    linear_combination h0
  | (m + 2) =>
    simp only [hshift1, hshift2] at h0 ⊢
    push_cast at h0 ⊢
    linear_combination h0

end IteratedDeriv

section Coefficients

variable {a : ℂ}

private theorem regularizedHGFunCoeff_pair (n : ℕ) :
    regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} n =
      (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval (a - 1 / 2) /
        ((n ! : ℂ) * Gamma (2 * a + n)) := by
  simp [regularizedHGFunCoeff]

private theorem regularizedHGFunCoeff_pair_zero :
    regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} 0 = (Gamma (2 * a))⁻¹ := by
  rw [regularizedHGFunCoeff_pair]
  simp

/-- The two-term recursion for the coefficients of the regularized hypergeometric series. -/
private theorem regularizedHGFunCoeff_pair_succ (n : ℕ) :
    ((n : ℂ) + 1) * ((n : ℂ) + 2 * a) * regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} (n + 1) =
      ((n : ℂ) + a) * ((n : ℂ) + a - 1 / 2) *
        regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} n := by
  rw [regularizedHGFunCoeff_pair, regularizedHGFunCoeff_pair]
  simp only [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_natCast]
  by_cases h : 2 * a + (n : ℂ) = 0
  · have h1 : Gamma (2 * a + (n : ℂ)) = 0 := by rw [h, Gamma_zero]
    have h2 : ((n : ℂ) + 2 * a) = 0 := by linear_combination h
    rw [h1, h2]
    simp
  · have hg : Gamma (2 * a + ((n : ℕ) + 1 : ℕ)) = (2 * a + n) * Gamma (2 * a + n) := by
      push_cast
      rw [show 2 * a + ((n : ℂ) + 1) = (2 * a + n) + 1 by ring, Gamma_add_one _ h]
    have hfac : ((n + 1)! : ℂ) = ((n : ℂ) + 1) * (n ! : ℂ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [hg, hfac]
    field_simp
    ring

/-- In the degenerate case `2a ∈ {0, -1, -2, …}` all coefficients vanish. -/
private theorem regularizedHGFunCoeff_pair_eq_zero {m : ℕ} (hm : 2 * a = -(m : ℂ)) (n : ℕ) :
    regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} n = 0 := by
  rw [regularizedHGFunCoeff_pair]
  rcases le_or_gt n m with hnm | hnm
  · have hg : Gamma (2 * a + n) = 0 := by
      rw [Gamma_eq_zero_iff]
      refine ⟨m - n, ?_⟩
      rw [hm, Nat.cast_sub hnm]
      ring
    rw [hg]
    simp
  · rcases Nat.even_or_odd m with ⟨p, hp⟩ | ⟨p, hp⟩
    · have ha : a = -(p : ℂ) := by
        rw [hp] at hm; push_cast at hm; linear_combination hm / 2
      have hzero : (ascPochhammer ℂ n).eval a = 0 := by
        rw [ha]
        exact ascPochhammer_eval_neg_coe_nat_of_lt (by omega)
      rw [hzero]; simp
    · have ha : a - 1 / 2 = -((p + 1 : ℕ) : ℂ) := by
        rw [hp] at hm; push_cast at hm ⊢; linear_combination hm / 2
      have hzero : (ascPochhammer ℂ n).eval (a - 1 / 2) = 0 := by
        rw [ha]
        exact ascPochhammer_eval_neg_coe_nat_of_lt (by omega)
      rw [hzero]; simp

/-- Away from the degenerate case, the `n`-th derivative of the closed form at `0` is
`n! Γ(2a) cₙ`. -/
private theorem iteratedDeriv_gauss2F1Closed_eq (hdeg : ∀ m : ℕ, 2 * a ≠ -(m : ℂ)) (n : ℕ) :
    iteratedDeriv n (gauss2F1Closed a) 0 =
      (n ! : ℂ) * Gamma (2 * a) * regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} n := by
  have hG : Gamma (2 * a) ≠ 0 := by
    rw [Ne, Gamma_eq_zero_iff]
    rintro ⟨m, hm⟩
    exact hdeg m hm
  induction n with
  | zero =>
    rw [iteratedDeriv_zero, gauss2F1Closed_zero, regularizedHGFunCoeff_pair_zero,
      Nat.factorial_zero]
    field_simp
    norm_num
  | succ n ih =>
    have hne : ((n : ℂ) + 2 * a) ≠ 0 := fun h => hdeg n (by linear_combination h)
    have h1 := iteratedDeriv_gauss2F1Closed_succ (a := a) n
    have h2 := regularizedHGFunCoeff_pair_succ (a := a) n
    rw [ih] at h1
    have hfac : ((n + 1)! : ℂ) = ((n : ℂ) + 1) * (n ! : ℂ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac]
    apply mul_left_cancel₀ hne
    rw [h1]
    linear_combination (-(n ! : ℂ) * Gamma (2 * a)) * h2

end Coefficients

section Interior

variable {a z : ℂ}

private theorem hasSum_regularized2F1_of_norm_lt_one (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} n * z ^ n)
      (gauss2F1Closed a z / Gamma (2 * a)) := by
  by_cases hdeg : ∀ m : ℕ, 2 * a ≠ -(m : ℂ)
  · have hG : Gamma (2 * a) ≠ 0 := by
      rw [Ne, Gamma_eq_zero_iff]
      rintro ⟨m, hm⟩
      exact hdeg m hm
    have hmem : z ∈ ball (0 : ℂ) 1 := by simpa using hz
    have H := Complex.hasSum_taylorSeries_on_ball
      (f := gauss2F1Closed a) (c := 0) (r := 1) differentiableOn_gauss2F1Closed hmem
    have H2 : HasSum (fun n : ℕ =>
        Gamma (2 * a) * (regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} n * z ^ n))
        (gauss2F1Closed a z) := by
      refine H.congr_fun fun n => ?_
      rw [iteratedDeriv_gauss2F1Closed_eq hdeg n]
      have hn : ((n ! : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      simp only [sub_zero, smul_eq_mul]
      field_simp
    have H3 := H2.mul_left (Gamma (2 * a))⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ hG, one_mul] at H3
    simpa [div_eq_inv_mul] using H3
  · push Not at hdeg
    obtain ⟨m, hm⟩ := hdeg
    have hG : Gamma (2 * a) = 0 := by rw [Gamma_eq_zero_iff]; exact ⟨m, hm⟩
    simp only [regularizedHGFunCoeff_pair_eq_zero hm, zero_mul, hG, div_zero]
    exact hasSum_zero

end Interior

section Boundary

variable {a z : ℂ}

/-- `(1 + x) ^ (5/4) ≤ 1 + 1.3 x` for small `x ≥ 0`. -/
private theorem rpow_five_fourths_le (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1 / 10) :
    (1 + x) ^ ((5 : ℝ) / 4) ≤ 1 + 1.3 * x := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h2 : (0 : ℝ) ≤ 1 + 1.3 * x := by linarith
  have key : ((1 + x) ^ ((5 : ℝ) / 4)) ^ (4 : ℕ) ≤ (1 + 1.3 * x) ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast ((1 + x) ^ ((5 : ℝ) / 4)) 4, ← Real.rpow_mul h1.le]
    norm_num
    nlinarith [sq_nonneg x, pow_nonneg hx 3, pow_nonneg hx 4, pow_nonneg hx 5,
      sq_nonneg (x - 1 / 10)]
  by_contra hc
  push Not at hc
  have : (1 + 1.3 * x) ^ (4 : ℕ) < ((1 + x) ^ ((5 : ℝ) / 4)) ^ 4 := by gcongr
  linarith

private theorem rpow_shift_bound (R : ℝ) (hR : 10 ≤ R) :
    (R + 1) ^ ((5 : ℝ) / 4) * R ≤ R ^ ((5 : ℝ) / 4) * (R + 1.3) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hx : (0 : ℝ) ≤ 1 / R := by positivity
  have hx' : 1 / R ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hR
  have hsplit : (R + 1) ^ ((5 : ℝ) / 4) = R ^ ((5 : ℝ) / 4) * (1 + 1 / R) ^ ((5 : ℝ) / 4) := by
    rw [← Real.mul_rpow hR0.le (by positivity)]
    congr 1
    field_simp
  rw [hsplit, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos hR0 _).le
  calc (1 + 1 / R) ^ ((5 : ℝ) / 4) * R ≤ (1 + 1.3 * (1 / R)) * R :=
        mul_le_mul_of_nonneg_right (rpow_five_fourths_le (1 / R) hx hx') hR0.le
    _ = R + 1.3 := by field_simp

/-- The elementary inequality behind the ratio test with exponent `5/4`. -/
private theorem gauss2F1_key_real (al E R : ℝ) (hE0 : 0 ≤ E) (hE : E ≤ 1 / 20)
    (hR : 1000 * (|al| + 2) ^ 2 + 1000 ≤ R) :
    (R + al + E - 1) * (R + al + E - 3 / 2) * (R + 1.3) ≤ R ^ 2 * (R - 1 + 2 * al) := by
  set m : ℝ := |al| + 1 with hm
  have hm1 : (1 : ℝ) ≤ m := by simp [hm, abs_nonneg]
  have hA1 : al + E ≤ m := by
    have := le_abs_self al
    simp only [hm]; linarith
  have hA2 : -(al + E) ≤ m := by
    have := neg_le_abs al
    simp only [hm]; linarith
  have hA3 : (al + E) ^ 2 ≤ m ^ 2 := by nlinarith
  have hRbig : 1000 * (m + 1) ^ 2 + 1000 ≤ R := by
    have hmm : (|al| + 2) = m + 1 := by simp [hm]; ring
    rwa [hmm] at hR
  have hR1 : (1 : ℝ) ≤ R := by nlinarith [sq_nonneg (m + 1)]
  have hK1 : (al + E) ^ 2 + (al + E) / 10 - 7 / 4 ≤ (m + 1) ^ 2 := by nlinarith
  have hK2 : 1.3 * (al + E) ^ 2 - 3.25 * (al + E) + 1.95 ≤ 4 * (m + 1) ^ 2 := by nlinarith
  have hexp : R ^ 2 * (R - 1 + 2 * al) - (R + al + E - 1) * (R + al + E - 3 / 2) * (R + 1.3)
      = R ^ 2 * (1 / 5 - 2 * E) - R * ((al + E) ^ 2 + (al + E) / 10 - 7 / 4)
        - (1.3 * (al + E) ^ 2 - 3.25 * (al + E) + 1.95) := by ring
  have hfinal : 0 ≤ R ^ 2 * (1 / 5 - 2 * E) - R * ((al + E) ^ 2 + (al + E) / 10 - 7 / 4)
      - (1.3 * (al + E) ^ 2 - 3.25 * (al + E) + 1.95) := by
    have h1 : R ^ 2 / 10 ≤ R ^ 2 * (1 / 5 - 2 * E) := by nlinarith [sq_nonneg R]
    have h2 : R * ((al + E) ^ 2 + (al + E) / 10 - 7 / 4) ≤ R * (m + 1) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (m + 1), hRbig, hR1]
  linarith [hexp, hfinal]

private theorem norm_le_of_sq_le {w : ℂ} {Y : ℝ} (hY : 0 ≤ Y) (h : w.re ^ 2 + w.im ^ 2 ≤ Y ^ 2) :
    ‖w‖ ≤ Y := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  calc Real.sqrt (w.re ^ 2 + w.im ^ 2) ≤ Real.sqrt (Y ^ 2) := Real.sqrt_le_sqrt h
    _ = Y := Real.sqrt_sq hY

/-- The ratio test step: for large `n`, the sequence `‖cₙ‖ (n+1)^(5/4)` is decreasing. -/
private theorem regularizedHGFunCoeff_pair_ratio_step (n : ℕ)
    (hn : 1000 * (|a.re| + 2) ^ 2 + 1000 + 10 * a.im ^ 2 + |a.re| + 10 ≤ (n : ℝ)) :
    ‖regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} (n + 1)‖ * ((n : ℝ) + 2) ^ ((5 : ℝ) / 4)
      ≤ ‖regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} n‖ * ((n : ℝ) + 1) ^ ((5 : ℝ) / 4) := by
  set al := a.re with hal
  set be := a.im with hbe
  have habs : al ≤ |al| := le_abs_self al
  have habs' : -al ≤ |al| := neg_le_abs al
  have habs0 : (0 : ℝ) ≤ |al| := abs_nonneg al
  have hsq : (0 : ℝ) ≤ be ^ 2 := sq_nonneg be
  have hbig : (0 : ℝ) ≤ 1000 * (|al| + 2) ^ 2 := by positivity
  set R : ℝ := (n : ℝ) + 1 with hRdef
  set u : ℝ := (n : ℝ) + al - 1 / 2 with hudef
  have hu1 : (10 : ℝ) ≤ u := by nlinarith
  have hu0 : (0 : ℝ) < u := by linarith
  set E : ℝ := be ^ 2 / (2 * u) with hEdef
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hEu : 2 * u * E = be ^ 2 := by rw [hEdef]; field_simp
  have hE20 : E ≤ 1 / 20 := by
    rw [hEdef, div_le_iff₀ (by linarith)]
    nlinarith
  have hR10 : (10 : ℝ) ≤ R := by nlinarith
  have hRkey : 1000 * (|al| + 2) ^ 2 + 1000 ≤ R := by nlinarith
  have hP : ‖(n : ℂ) + a‖ ≤ R + al + E - 1 := by
    refine norm_le_of_sq_le (by nlinarith) ?_
    have h1 : ((n : ℂ) + a).re = (n : ℝ) + al := by simp [hal]
    have h2 : ((n : ℂ) + a).im = be := by simp [hbe]
    rw [h1, h2, show R + al + E - 1 = (n : ℝ) + al + E by rw [hRdef]; ring]
    nlinarith [sq_nonneg E]
  have hQ : ‖(n : ℂ) + a - 1 / 2‖ ≤ R + al + E - 3 / 2 := by
    refine norm_le_of_sq_le (by nlinarith) ?_
    have h1 : ((n : ℂ) + a - 1 / 2).re = (n : ℝ) + al - 1 / 2 := by simp [hal]
    have h2 : ((n : ℂ) + a - 1 / 2).im = be := by simp [hbe]
    rw [h1, h2, show R + al + E - 3 / 2 = u + E by rw [hRdef, hudef]; ring]
    nlinarith [sq_nonneg E]
  have hS : R - 1 + 2 * al ≤ ‖(n : ℂ) + 2 * a‖ := by
    have h := Complex.re_le_norm ((n : ℂ) + 2 * a)
    simp only [Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat] at h
    rw [hRdef]
    simpa [hal] using h
  set P := ‖(n : ℂ) + a‖ with hPdef
  set Q := ‖(n : ℂ) + a - 1 / 2‖ with hQdef
  set S := ‖(n : ℂ) + 2 * a‖ with hSdef
  set cn := ‖regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} n‖ with hcn
  set cn1 := ‖regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} (n + 1)‖ with hcn1
  have hP0 : 0 ≤ P := norm_nonneg _
  have hQ0 : 0 ≤ Q := norm_nonneg _
  have hcn0 : 0 ≤ cn := norm_nonneg _
  have hS0 : 0 < S := lt_of_lt_of_le (by nlinarith) hS
  have hR0 : (0 : ℝ) < R := by linarith
  have hrec : R * S * cn1 = P * Q * cn := by
    have h := congrArg norm (regularizedHGFunCoeff_pair_succ (a := a) n)
    rw [norm_mul, norm_mul, norm_mul, norm_mul,
      show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast] at h
    rw [hRdef, hSdef, hPdef, hQdef, hcn, hcn1]
    push_cast at h ⊢
    convert h using 3
  have hRp : (0 : ℝ) ≤ R ^ ((5 : ℝ) / 4) := (Real.rpow_pos_of_pos hR0 _).le
  have step2 : P * Q * (R + 1.3) ≤ R ^ 2 * S := by
    have h1 : P * Q ≤ (R + al + E - 1) * (R + al + E - 3 / 2) :=
      mul_le_mul hP hQ hQ0 (by nlinarith)
    calc P * Q * (R + 1.3) ≤ (R + al + E - 1) * (R + al + E - 3 / 2) * (R + 1.3) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ R ^ 2 * (R - 1 + 2 * al) := gauss2F1_key_real al E R hE0 hE20 hRkey
      _ ≤ R ^ 2 * S := mul_le_mul_of_nonneg_left hS (sq_nonneg R)
  have step1 : P * Q * ((R + 1) ^ ((5 : ℝ) / 4) * R) ≤ P * Q * (R ^ ((5 : ℝ) / 4) * (R + 1.3)) :=
    mul_le_mul_of_nonneg_left (rpow_shift_bound R hR10) (by positivity)
  have step5 : P * Q * (R + 1) ^ ((5 : ℝ) / 4) ≤ R ^ ((5 : ℝ) / 4) * (R * S) := by
    refine le_of_mul_le_mul_right ?_ hR0
    calc P * Q * (R + 1) ^ ((5 : ℝ) / 4) * R = P * Q * ((R + 1) ^ ((5 : ℝ) / 4) * R) := by ring
      _ ≤ P * Q * (R ^ ((5 : ℝ) / 4) * (R + 1.3)) := step1
      _ = R ^ ((5 : ℝ) / 4) * (P * Q * (R + 1.3)) := by ring
      _ ≤ R ^ ((5 : ℝ) / 4) * (R ^ 2 * S) := mul_le_mul_of_nonneg_left step2 hRp
      _ = R ^ ((5 : ℝ) / 4) * (R * S) * R := by ring
  have hgoal : cn1 * ((R + 1) ^ ((5 : ℝ) / 4)) ≤ cn * (R ^ ((5 : ℝ) / 4)) := by
    have hRS : 0 < R * S := by positivity
    refine le_of_mul_le_mul_left ?_ hRS
    calc R * S * (cn1 * (R + 1) ^ ((5 : ℝ) / 4)) = (R * S * cn1) * (R + 1) ^ ((5 : ℝ) / 4) := by
          ring
      _ = (P * Q * cn) * (R + 1) ^ ((5 : ℝ) / 4) := by rw [hrec]
      _ = cn * (P * Q * (R + 1) ^ ((5 : ℝ) / 4)) := by ring
      _ ≤ cn * (R ^ ((5 : ℝ) / 4) * (R * S)) := mul_le_mul_of_nonneg_left step5 hcn0
      _ = R * S * (cn * R ^ ((5 : ℝ) / 4)) := by ring
  rw [show ((n : ℝ) + 2) = R + 1 by rw [hRdef]; ring]
  exact hgoal

/-- Absolute convergence of the coefficient series (the parameters satisfy
`Re (c - a - b) = 1/2 > 0`). -/
private theorem summable_norm_regularizedHGFunCoeff_pair :
    Summable (fun n : ℕ => ‖regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} n‖) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (1000 * (|a.re| + 2) ^ 2 + 1000 + 10 * a.im ^ 2 + |a.re| + 10)
  set c : ℕ → ℝ := fun n => ‖regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} n‖ with hc
  set K : ℝ := c N * ((N : ℝ) + 1) ^ ((5 : ℝ) / 4) with hK
  have mono : ∀ n : ℕ, N ≤ n → c n * ((n : ℝ) + 1) ^ ((5 : ℝ) / 4) ≤ K := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
      have hstep := regularizedHGFunCoeff_pair_ratio_step (a := a) n
        (le_trans hN (by exact_mod_cast hn))
      have heq : c (n + 1) * (((n + 1 : ℕ) : ℝ) + 1) ^ ((5 : ℝ) / 4)
          = c (n + 1) * (((n : ℝ)) + 2) ^ ((5 : ℝ) / 4) := by push_cast; ring_nf
      rw [heq]
      exact le_trans hstep ih
  have hbase : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-((5 : ℝ) / 4))) := by
    have h : Summable (fun n : ℕ => (((n : ℝ)) ^ ((5 : ℝ) / 4))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    refine ((summable_nat_add_iff (f := fun n : ℕ => (((n : ℝ)) ^ ((5 : ℝ) / 4))⁻¹) 1).mpr h).congr
      fun n => ?_
    rw [Real.rpow_neg (by positivity)]
    push_cast
    ring_nf
  rw [← summable_nat_add_iff N]
  have hsum : Summable (fun n : ℕ => K * ((((n + N : ℕ)) : ℝ) + 1) ^ (-((5 : ℝ) / 4))) :=
    ((summable_nat_add_iff (f := fun m : ℕ => ((m : ℝ) + 1) ^ (-((5 : ℝ) / 4))) N).mpr
      hbase).mul_left K
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsum
  have hpos : (0 : ℝ) < (((n + N : ℕ) : ℝ) + 1) ^ ((5 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (by positivity) _
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hpos]
  exact mono (n + N) (Nat.le_add_left N n)

/-- The closed form is continuous on the closed unit disc. -/
private theorem continuousAt_gauss2F1Closed (hz : ‖z‖ ≤ 1) : ContinuousAt (gauss2F1Closed a) z := by
  have hre : 0 ≤ (1 - z).re := by
    have h := abs_le.mp (Complex.abs_re_le_norm z)
    simp only [Complex.sub_re, Complex.one_re]
    linarith [h.2]
  have hsqrt : ContinuousAt (fun w : ℂ => Complex.sqrt (1 - w)) z :=
    (continuousAt_cpow_const_of_re_pos (Or.inl hre) (by norm_num)).comp (by fun_prop)
  have hre2 : 0 ≤ (Complex.sqrt (1 - z)).re := by
    rw [Complex.sqrt, Complex.cpow_inv_two_re]
    positivity
  have hmem : (Complex.sqrt (1 - z) + 1) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have h3 : ContinuousAt (fun x : ℂ => x ^ (1 - 2 * a)) (Complex.sqrt (1 - z) + 1) :=
    continuousAt_cpow_const hmem
  have hg : ContinuousAt (fun w : ℂ => Complex.sqrt (1 - w) + 1) z := hsqrt.add continuousAt_const
  have h4 : ContinuousAt (fun w : ℂ => (Complex.sqrt (1 - w) + 1) ^ (1 - 2 * a)) z :=
    ContinuousAt.comp (g := fun x : ℂ => x ^ (1 - 2 * a))
      (f := fun w : ℂ => Complex.sqrt (1 - w) + 1) (x := z) h3 hg
  exact h4.const_mul _

/-- The identity on the closed unit disc, obtained from the interior case by Abel's limit
theorem. -/
private theorem hasSum_regularized2F1_of_norm_le_one (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} n * z ^ n)
      (gauss2F1Closed a z / Gamma (2 * a)) := by
  rcases lt_or_eq_of_le hz with hlt | hz1
  · exact hasSum_regularized2F1_of_norm_lt_one hlt
  have habs : Summable (fun n : ℕ => regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} n * z ^ n) := by
    refine Summable.of_norm ?_
    simpa [norm_mul, norm_pow, hz1] using summable_norm_regularizedHGFunCoeff_pair (a := a)
  set c : ℕ → ℂ := fun n => regularizedHGFunCoeff {a, a - 1 / 2} {2 * a} n with hc
  have hS : HasSum (fun n => c n * z ^ n) (∑' n, c n * z ^ n) := habs.hasSum
  suffices h : (∑' n, c n * z ^ n) = gauss2F1Closed a z / Gamma (2 * a) by rw [← h]; exact hS
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzSet (M := 2)
      (f := fun n => c n * z ^ n) hS.tendsto_sum_nat
  have hpath : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 1 (Set.Iio 1))
      (nhdsWithin 1 (Complex.stolzSet 2)) :=
    Complex.nhdsWithin_lt_le_nhdsWithin_stolzSet (by norm_num)
  have h1 : Filter.Tendsto (fun t : ℝ => ∑' n, (c n * z ^ n) * (t : ℂ) ^ n)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (∑' n, c n * z ^ n)) := habel.comp hpath
  have h2 : (fun t : ℝ => ∑' n, (c n * z ^ n) * (t : ℂ) ^ n)
      =ᶠ[nhdsWithin 1 (Set.Iio 1)] fun t : ℝ => gauss2F1Closed a ((t : ℂ) * z) / Gamma (2 * a) := by
    filter_upwards [Ioo_mem_nhdsLT (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num)] with t ht
    have hnorm : ‖(t : ℂ) * z‖ < 1 := by
      rw [norm_mul, hz1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      exact ht.2
    rw [← (hasSum_regularized2F1_of_norm_lt_one (a := a) hnorm).tsum_eq]
    exact tsum_congr fun n => by rw [mul_pow]; ring
  have h3 : Filter.Tendsto (fun t : ℝ => gauss2F1Closed a ((t : ℂ) * z) / Gamma (2 * a))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (gauss2F1Closed a z / Gamma (2 * a))) := by
    have hcont : ContinuousAt (fun w : ℂ => gauss2F1Closed a w / Gamma (2 * a)) z :=
      (continuousAt_gauss2F1Closed hz).div_const _
    have hmap : Filter.Tendsto (fun t : ℝ => (t : ℂ) * z) (nhdsWithin 1 (Set.Iio 1)) (nhds z) := by
      have hct : ContinuousAt (fun t : ℝ => (t : ℂ) * z) 1 := by fun_prop
      simpa using hct.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    exact Filter.Tendsto.comp (g := fun w : ℂ => gauss2F1Closed a w / Gamma (2 * a))
      (f := fun t : ℝ => (t : ℂ) * z) hcont.tendsto hmap
  exact tendsto_nhds_unique (h1.congr' h2) h3

end Boundary

section Main

variable {a z : ℂ}

/-- **The requested identity.**  For the *regularized* Gauss hypergeometric function one has
`₂F̃₁(a, a - 1/2; 2a; z) = 2^(2a-1) (√(1-z) + 1)^(1-2a) / Γ(2a)`,
under the convergence condition `‖z‖ < 1` or (`‖z‖ = 1` and `Re (c - a - b) > 0`), where
`c - a - b = 2a - a - (a - 1/2) = 1/2`. -/
theorem regularized2F1_0 (hz : ‖z‖ < 1 ∨ (‖z‖ = 1 ∧ 0 < (2 * a - a - (a - 1 / 2)).re)) :
    regularizedHGFun {a, a - 1 / 2} {2 * a} z =
      2 ^ (2 * a - 1) * (Complex.sqrt (1 - z) + 1) ^ (1 - 2 * a) / Gamma (2 * a) := by
  have hle : ‖z‖ ≤ 1 := by
    rcases hz with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  rw [regularizedHGFun_eq_tsum]
  exact (hasSum_regularized2F1_of_norm_le_one hle).tsum_eq

/-- **The requested identity** for the non-regularized Gauss hypergeometric function:
`₂F₁(a, a - 1/2; 2a; z) = 2^(2a-1) (√(1-z) + 1)^(1-2a)`,
under the convergence condition `‖z‖ < 1` or (`‖z‖ = 1` and `Re (c - a - b) > 0`), where
`c - a - b = 2a - a - (a - 1/2) = 1/2`.

Here no Gamma factor appears: multiplying the regularized function by `Γ(2a)` cancels the
factor `1 / Γ(2a)` of `Complex.regularized2F1_0`.  The hypothesis `ha` (that `2a` is not a
non-positive integer) is the classical requirement that the lower parameter be admissible. -/
theorem HGFun2F1_0 (ha : ∀ k : ℕ, 2 * a ≠ -k)
    (hz : ‖z‖ < 1 ∨ (‖z‖ = 1 ∧ 0 < (2 * a - a - (a - 1 / 2)).re)) :
    HGFun {a, a - 1 / 2} {2 * a} z =
      2 ^ (2 * a - 1) * (Complex.sqrt (1 - z) + 1) ^ (1 - 2 * a) := by
  have hG : Gamma (2 * a) ≠ 0 := Gamma_ne_zero ha
  rw [HGFun_def, regularized2F1_0 hz]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  field_simp

/-- The factor `1 / Γ(2a)` in `Complex.regularized2F1_0` cannot be omitted: the identity
`₂F̃₁(a, a - 1/2; 2a; z) = 2^(2a-1) (√(1-z) + 1)^(1-2a)` already fails at `a = 3/2`, `z = 0`,
where the left-hand side is `1 / Γ(3) = 1/2` and the right-hand side is `1`.

(The classical, non-regularized Gauss function does satisfy
`₂F₁(a, a - 1/2; 2a; z) = 2^(2a-1) (√(1-z) + 1)^(1-2a)`; the regularized function differs from it
by the factor `1 / Γ(2a)`.) -/
theorem not_regularized2F1_0 :
    ¬ ∀ a z : ℂ, ‖z‖ ≤ 1 → regularizedHGFun {a, a - 1 / 2} {2 * a} z
      = 2 ^ (2 * a - 1) * (Complex.sqrt (1 - z) + 1) ^ (1 - 2 * a) := by
  intro h
  have h1 := h (3 / 2) 0 (by simp)
  have h2 := regularized2F1_0 (a := 3 / 2) (z := 0) (Or.inl (by simp))
  rw [h1] at h2
  have hclosed : (2 : ℂ) ^ (2 * (3 / 2 : ℂ) - 1) *
      (Complex.sqrt (1 - 0) + 1) ^ (1 - 2 * (3 / 2 : ℂ)) = 1 := gauss2F1Closed_zero (a := 3 / 2)
  rw [hclosed] at h2
  have hG : Gamma (2 * (3 / 2 : ℂ)) = 2 := by
    rw [show (2 * (3 / 2 : ℂ)) = ((2 : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
    norm_num
  rw [hG] at h2
  norm_num at h2

end Main

end Complex

/-
The statement as originally requested,

  theorem Complex.regularized2F1_0 {a z : ℂ} :
      regularizedHGFun {a, a-1/2} {2*a} z = 2^(2*a-1) * (Complex.sqrt (1-z)+1)^(1-2*a) := by
    sorry

is not provable, for two reasons.

* `regularizedHGFun` is the *regularized* hypergeometric function, whose coefficients carry
  `1 / Γ(c + n)` instead of `1 / (c)ₙ`; it therefore differs from the classical `₂F₁` by the
  factor `1 / Γ(2a)`.  Omitting this factor makes the statement false already at `a = 3/2`,
  `z = 0`; see `Complex.not_regularized2F1_0`.
* Some convergence hypothesis on `z` is needed, as requested:
  `‖z‖ < 1 ∨ (‖z‖ = 1 ∧ 0 < Re (c - a - b))`, which here (with `c - a - b = 1/2`) amounts to
  `‖z‖ ≤ 1`.

The corrected statement, with both changes, is `Complex.regularized2F1_0` above.  For the
non-regularized function `Complex.HGFun` the Gamma factor disappears, so the requested
right-hand side is correct as written: see `Complex.HGFun2F1_0` (which needs the same
convergence hypothesis, and that `2a` is not a non-positive integer, so that `₂F₁` is defined).
-/
