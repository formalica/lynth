import Mathlib
import Lynth.HGIdentities.Common
import Lynth.SeriesTools

/-!
# Complex inverse trigonometric and inverse hyperbolic functions

Mathlib provides `Real.arcsin` and `Real.artanh`, but no complex versions.  The hypergeometric
identities of this project are stated for complex arguments, so the two functions we need are
defined here through the principal branch of the complex logarithm:

* `Complex.arcsin z = -i log (i z + √(1 - z²))`;
* `Complex.artanh z = (log (1 + z) - log (1 - z)) / 2`.

Both are holomorphic on the open unit disc, which is where the hypergeometric series converge,
and this file records everything about them that the identity proofs need:

* the values at `0` (`Complex.arcsin_zero`, `Complex.artanh_zero`);
* the derivatives on the unit disc (`Complex.hasDerivAt_arcsin`, `Complex.hasDerivAt_artanh`);
* the defining properties `sin (arcsin z) = z`, `cos (arcsin z) = √(1 - z²)` and
  `tanh (artanh z) = z` (`Complex.sin_arcsin`, `Complex.cos_arcsin`, `Complex.tanh_artanh`);
* the agreement with the real functions on real arguments (`Complex.arcsin_ofReal`,
  `Complex.artanh_ofReal`).

It also records the two elementary power series that are used by more than one identity file:

* `Complex.tsum_atanhCoeff_eq` : `v ∑ₙ (v²)ⁿ/(2n+1) = artanh v` on the unit disc, whose
  coefficient sequence is `Complex.atanhCoeff`;
* `Complex.hasSum_neg_log_div` : `∑ₙ zⁿ/(n+1) = -log(1 - z)/z` on the punctured unit disc.
-/

open Metric

namespace Complex

/-- The principal branch of the complex arcsine, `arcsin z = -i log (i z + √(1 - z²))`. -/
noncomputable def arcsin (z : ℂ) : ℂ := -I * log (I * z + Complex.sqrt (1 - z ^ 2))

/-- The principal branch of the complex inverse hyperbolic tangent,
`artanh z = (log (1 + z) - log (1 - z)) / 2`. -/
noncomputable def artanh (z : ℂ) : ℂ := (log (1 + z) - log (1 - z)) / 2

/-- The principal square root of a nonnegative real number is the real square root. -/
theorem sqrt_ofReal {x : ℝ} (hx : 0 ≤ x) : Complex.sqrt (x : ℂ) = (Real.sqrt x : ℂ) := by
  rw [Complex.sqrt, show ((2 : ℂ))⁻¹ = ((2⁻¹ : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hx,
    Real.sqrt_eq_rpow]
  norm_num

@[simp] theorem artanh_zero : artanh 0 = 0 := by simp [artanh]

@[simp] theorem arcsin_zero : arcsin 0 = 0 := by simp [arcsin, Complex.sqrt]

section Disc

variable {z : ℂ}

theorem norm_sq_lt_one (hz : ‖z‖ < 1) : ‖z ^ 2‖ < 1 := by
  rw [norm_pow]
  nlinarith [norm_nonneg z]

/-- On the unit disc, `√(1 - z²)` has positive real part. -/
theorem re_sqrt_one_sub_sq_pos (hz : ‖z‖ < 1) : 0 < (Complex.sqrt (1 - z ^ 2)).re :=
  re_sqrt_pos (norm_sq_lt_one hz)

theorem sqrt_one_sub_sq_ne_zero (hz : ‖z‖ < 1) : Complex.sqrt (1 - z ^ 2) ≠ 0 :=
  sqrt_ne_zero' (norm_sq_lt_one hz)

theorem sq_sqrt_one_sub_sq (z : ℂ) : Complex.sqrt (1 - z ^ 2) ^ 2 = 1 - z ^ 2 :=
  sqrt_sq_eq _

/-- The two numbers `i z + √(1-z²)` and `√(1-z²) - i z` are reciprocal. -/
theorem arcsinArg_mul (z : ℂ) :
    (I * z + Complex.sqrt (1 - z ^ 2)) * (Complex.sqrt (1 - z ^ 2) - I * z) = 1 := by
  have h := sq_sqrt_one_sub_sq z
  have hI : I ^ 2 = -1 := Complex.I_sq
  linear_combination h - z ^ 2 * hI

theorem arcsinArg_ne_zero (z : ℂ) : I * z + Complex.sqrt (1 - z ^ 2) ≠ 0 := by
  intro h
  have hmul := arcsinArg_mul z
  rw [h, zero_mul] at hmul
  exact zero_ne_one hmul

theorem inv_arcsinArg (z : ℂ) :
    (I * z + Complex.sqrt (1 - z ^ 2))⁻¹ = Complex.sqrt (1 - z ^ 2) - I * z :=
  inv_eq_of_mul_eq_one_right (arcsinArg_mul z)

/-- On the unit disc `i z + √(1 - z²)` lies in the slit plane, so the principal logarithm is
holomorphic there. -/
theorem arcsinArg_mem_slitPlane (hz : ‖z‖ < 1) :
    I * z + Complex.sqrt (1 - z ^ 2) ∈ slitPlane := by
  set X := I * z + Complex.sqrt (1 - z ^ 2) with hX
  have hXne : X ≠ 0 := arcsinArg_ne_zero z
  rcases eq_or_ne X.im 0 with him | him
  · -- `X` is real; since `X + X⁻¹ = 2 √(1-z²)` has positive real part, `X > 0`.
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have hsum : X + X⁻¹ = 2 * Complex.sqrt (1 - z ^ 2) := by
      rw [inv_arcsinArg z, hX]; ring
    have hre : 0 < (X + X⁻¹).re := by
      rw [hsum]
      simpa using re_sqrt_one_sub_sq_pos hz
    have hXreal : X = (X.re : ℂ) := by apply Complex.ext <;> simp [him]
    have hXre0 : X.re ≠ 0 := by
      intro h
      apply hXne
      rw [hXreal, h]
      simp
    have hinvre : (X⁻¹).re = (X.re)⁻¹ := by
      rw [hXreal]
      simp [← Complex.ofReal_inv]
    rw [Complex.add_re, hinvre] at hre
    rcases lt_or_gt_of_ne hXre0 with hneg | hpos
    · exact absurd hre (by simp only [not_lt]; nlinarith [inv_neg''.mpr hneg])
    · exact hpos
  · exact mem_slitPlane_iff.mpr (Or.inr him)

/-- The derivative of `z ↦ √(1 - z²)` on the unit disc. -/
theorem hasDerivAt_sqrt_one_sub_sq (hz : ‖z‖ < 1) :
    HasDerivAt (fun w => Complex.sqrt (1 - w ^ 2)) (-(z / Complex.sqrt (1 - z ^ 2))) z := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w ^ 2) (-(2 * z)) z := by
    simpa using ((hasDerivAt_pow 2 z).const_sub 1)
  have hmem : (1 - z ^ 2) ∈ slitPlane :=
    mem_slitPlane_iff.mpr (Or.inl (re_one_sub_pos (norm_sq_lt_one hz)))
  have hne : (1 : ℂ) - z ^ 2 ≠ 0 := one_sub_ne_zero' (norm_sq_lt_one hz)
  have hs : Complex.sqrt (1 - z ^ 2) ≠ 0 := sqrt_one_sub_sq_ne_zero hz
  have h2 : Complex.sqrt (1 - z ^ 2) ^ 2 = 1 - z ^ 2 := sqrt_sq_eq _
  have key : HasDerivAt (fun w => Complex.sqrt (1 - w ^ 2))
      (2⁻¹ * (1 - z ^ 2) ^ ((2 : ℂ)⁻¹ - 1) * -(2 * z)) z := h1.cpow_const hmem (c := 2⁻¹)
  have hcp : (1 - z ^ 2 : ℂ) ^ ((2 : ℂ)⁻¹ - 1) = Complex.sqrt (1 - z ^ 2) / (1 - z ^ 2) := by
    rw [Complex.cpow_sub _ _ hne, Complex.cpow_one]
    rfl
  rw [hcp] at key
  convert key using 1
  generalize hgen : Complex.sqrt (1 - z ^ 2) = s at h2 hs ⊢
  rw [← h2]
  field_simp

/-- The derivative of the complex arcsine on the unit disc. -/
theorem hasDerivAt_arcsin (hz : ‖z‖ < 1) :
    HasDerivAt arcsin (1 / Complex.sqrt (1 - z ^ 2)) z := by
  have hI : I ^ 2 = -1 := Complex.I_sq
  have hs : Complex.sqrt (1 - z ^ 2) ≠ 0 := sqrt_one_sub_sq_ne_zero hz
  have hX : I * z + Complex.sqrt (1 - z ^ 2) ≠ 0 := arcsinArg_ne_zero z
  have hf : HasDerivAt (fun w : ℂ => I * w + Complex.sqrt (1 - w ^ 2))
      (I - z / Complex.sqrt (1 - z ^ 2)) z := by
    have h1 : HasDerivAt (fun w : ℂ => I * w) I z := by
      simpa using (hasDerivAt_id z).const_mul I
    exact (h1.add (hasDerivAt_sqrt_one_sub_sq hz)).congr_deriv (by ring)
  have hfin := (hf.clog (arcsinArg_mem_slitPlane hz)).const_mul (-I)
  have hgoal : -I * ((I - z / Complex.sqrt (1 - z ^ 2)) / (I * z + Complex.sqrt (1 - z ^ 2)))
      = 1 / Complex.sqrt (1 - z ^ 2) := by
    have hnum : I - z / Complex.sqrt (1 - z ^ 2)
        = I * (I * z + Complex.sqrt (1 - z ^ 2)) / Complex.sqrt (1 - z ^ 2) := by
      field_simp
      linear_combination (-z) * hI
    rw [hnum]
    field_simp
    linear_combination -hI
  rw [hgoal] at hfin
  exact hfin

/-- The derivative of the complex inverse hyperbolic tangent on the unit disc. -/
theorem hasDerivAt_artanh (hz : ‖z‖ < 1) : HasDerivAt artanh (1 / (1 - z ^ 2)) z := by
  have h1p : (1 : ℂ) + z ∈ slitPlane := by
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have h := abs_le.mp (Complex.abs_re_le_norm z)
    simp only [Complex.add_re, Complex.one_re]
    linarith [h.1]
  have h1m : (1 : ℂ) - z ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (re_one_sub_pos hz))
  have hp : HasDerivAt (fun w : ℂ => log (1 + w)) (1 / (1 + z)) z := by
    have h : HasDerivAt (fun w : ℂ => 1 + w) 1 z := by simpa using (hasDerivAt_id z).const_add 1
    simpa [div_eq_inv_mul] using h.clog h1p
  have hm : HasDerivAt (fun w : ℂ => log (1 - w)) (-(1 / (1 - z))) z := by
    have h : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub 1
    simpa [div_eq_inv_mul, neg_div] using h.clog h1m
  have hne1 : (1 : ℂ) + z ≠ 0 := slitPlane_ne_zero h1p
  have hne2 : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero' hz
  have hne3 : (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro h
    apply hne2
    have : (1 - z) * (1 + z) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact h1
    · exact absurd h1 hne1
  have hfin := (hp.sub hm).div_const 2
  have hgoal : ((1 / (1 + z) - -(1 / (1 - z))) / 2 : ℂ) = 1 / (1 - z ^ 2) := by
    field_simp
    ring
  rw [hgoal] at hfin
  exact hfin

end Disc

section Values

variable {z : ℂ}

theorem exp_mul_I_arcsin (z : ℂ) : exp (I * arcsin z) = I * z + Complex.sqrt (1 - z ^ 2) := by
  rw [arcsin, show I * (-I * log (I * z + Complex.sqrt (1 - z ^ 2)))
      = log (I * z + Complex.sqrt (1 - z ^ 2)) by rw [← mul_assoc]; simp [Complex.I_mul_I]]
  exact Complex.exp_log (arcsinArg_ne_zero z)

theorem exp_neg_mul_I_arcsin (z : ℂ) :
    exp (-(I * arcsin z)) = Complex.sqrt (1 - z ^ 2) - I * z := by
  rw [Complex.exp_neg, exp_mul_I_arcsin, inv_arcsinArg]

@[simp] theorem sin_arcsin (z : ℂ) : sin (arcsin z) = z := by
  rw [Complex.sin, show -arcsin z * I = -(I * arcsin z) by ring,
    show arcsin z * I = I * arcsin z by ring, exp_mul_I_arcsin, exp_neg_mul_I_arcsin]
  have hI : I ^ 2 = -1 := Complex.I_sq
  have hIne : I ≠ 0 := Complex.I_ne_zero
  field_simp
  linear_combination (-2 * z) * hI

@[simp] theorem cos_arcsin (z : ℂ) : cos (arcsin z) = Complex.sqrt (1 - z ^ 2) := by
  rw [Complex.cos, show -arcsin z * I = -(I * arcsin z) by ring,
    show arcsin z * I = I * arcsin z by ring, exp_mul_I_arcsin, exp_neg_mul_I_arcsin]
  ring

theorem tanh_artanh (hz : ‖z‖ < 1) : tanh (artanh z) = z := by
  have hne1 : (1 : ℂ) + z ≠ 0 := by
    intro h
    have hre : (1 + z).re = 0 := by rw [h]; simp
    have hb := abs_le.mp (Complex.abs_re_le_norm z)
    simp only [Complex.add_re, Complex.one_re] at hre
    linarith [hb.1]
  have hne2 : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero' hz
  have hexp : exp (artanh z) ^ 2 = (1 + z) / (1 - z) := by
    rw [← Complex.exp_nat_mul, artanh]
    push_cast
    rw [show (2 : ℂ) * ((log (1 + z) - log (1 - z)) / 2) = log (1 + z) - log (1 - z) by ring,
      Complex.exp_sub, Complex.exp_log hne1, Complex.exp_log hne2]
  set E := exp (artanh z) with hE
  have hEne : E ≠ 0 := Complex.exp_ne_zero _
  have hden : E ^ 2 + 1 ≠ 0 := by
    intro h
    rw [hexp, div_add' _ _ _ hne2] at h
    rcases div_eq_zero_iff.mp h with h1 | h1
    · have h2 : (2 : ℂ) = 0 := by linear_combination h1
      norm_num at h2
    · exact hne2 h1
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.sinh, Complex.cosh, Complex.exp_neg, ← hE]
  have key : (E - E⁻¹) / 2 / ((E + E⁻¹) / 2) = (E ^ 2 - 1) / (E ^ 2 + 1) := by
    rw [div_div_div_comm]
    field_simp
  rw [key, hexp]
  field_simp
  ring

end Values

section Real

/-- On real arguments of modulus `< 1`, `Complex.artanh` agrees with `Real.artanh`. -/
theorem artanh_ofReal {x : ℝ} (hx : |x| < 1) : artanh (x : ℂ) = (Real.artanh x : ℂ) := by
  have hb := abs_lt.mp hx
  have h1 : (0 : ℝ) < 1 + x := by linarith [hb.1]
  have h2 : (0 : ℝ) < 1 - x := by linarith [hb.2]
  rw [artanh, Real.artanh_eq_half_log (by constructor <;> [linarith [hb.1]; linarith [hb.2]]),
    show ((1 : ℂ) + (x : ℂ)) = ((1 + x : ℝ) : ℂ) by push_cast; ring,
    show ((1 : ℂ) - (x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log h1.le, ← Complex.ofReal_log h2.le,
    Real.log_div (by linarith) (by linarith)]
  push_cast
  ring

/-- On real arguments of modulus `< 1`, `Complex.arcsin` agrees with `Real.arcsin`. -/
theorem arcsin_ofReal {x : ℝ} (hx : |x| < 1) : arcsin (x : ℂ) = (Real.arcsin x : ℂ) := by
  have hb := abs_lt.mp hx
  have hx1 : x ^ 2 < 1 := by nlinarith [hb.1, hb.2]
  have hpos : (0 : ℝ) < 1 - x ^ 2 := by linarith
  have hsqrt : Complex.sqrt (1 - (x : ℂ) ^ 2) = (Real.sqrt (1 - x ^ 2) : ℂ) := by
    rw [show (1 : ℂ) - (x : ℂ) ^ 2 = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring, sqrt_ofReal hpos.le]
  rw [arcsin, hsqrt]
  have hz : (I * (x : ℂ) + (Real.sqrt (1 - x ^ 2) : ℂ))
      = Complex.exp ((Real.arcsin x : ℂ) * I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.sin_arcsin (by linarith [hb.1]) (by linarith [hb.2]), Real.cos_arcsin]
    ring
  rw [hz, Complex.log_exp]
  · ring_nf
    rw [Complex.I_sq]
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re,
      mul_one, mul_zero, add_zero]
    have h1 : -(Real.pi / 2) ≤ Real.arcsin x := Real.neg_pi_div_two_le_arcsin x
    have := Real.pi_pos
    linarith
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re,
      mul_one, mul_zero, add_zero]
    have h1 : Real.arcsin x ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two x
    have := Real.pi_pos
    linarith

end Real

section Series

/-- The coefficient sequence `1/(2n+1)`. -/
noncomputable def atanhCoeff (n : ℕ) : ℂ := 1 / (2 * (n : ℂ) + 1)

theorem seriesOnDisc_atanhCoeff : SeriesOnDisc atanhCoeff := by
  refine seriesOnDisc_of_bdd (B := 1) fun n => ?_
  rw [atanhCoeff, norm_div, norm_one]
  rw [div_le_one (norm_pos_iff.mpr (two_mul_add_one_ne_zero n))]
  have h : (2 * (n : ℂ) + 1) = (((2 * (n : ℝ) + 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The derivative combination of the coefficient series is the geometric series. -/
theorem tsum_atanh_deriv {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' n : ℕ, atanhCoeff n * z ^ n)
      + 2 * z * ∑' n : ℕ, ((n : ℂ) + 1) * atanhCoeff (n + 1) * z ^ n = (1 - z)⁻¹ := by
  have h1 := seriesOnDisc_atanhCoeff.hasSum_deriv_combo hz
  have h2 : HasSum (fun n : ℕ => (2 * (n : ℂ) + 1) * atanhCoeff n * z ^ n) (1 - z)⁻¹ := by
    refine (hasSum_geometric_of_norm_lt_one hz).congr_fun fun n => ?_
    rw [atanhCoeff]
    field_simp [two_mul_add_one_ne_zero n]
  exact h1.unique h2

/-- The key series identity on the unit disc: `v ∑ₙ (v²)ⁿ/(2n+1) = artanh v`. -/
theorem tsum_atanhCoeff_eq {v : ℂ} (hv : ‖v‖ < 1) :
    v * ∑' n : ℕ, atanhCoeff n * (v ^ 2) ^ n = artanh v := by
  refine eq_of_hasDerivAt_ball (F := fun w : ℂ => w * ∑' n : ℕ, atanhCoeff n * (w ^ 2) ^ n)
    (G := artanh) (D := fun w => 1 / (1 - w ^ 2)) one_pos ?_ ?_ ?_ (mem_ball_zero_iff.mpr hv)
  · intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hw2 : ‖w ^ 2‖ < 1 := by
      rw [norm_pow]; nlinarith [norm_nonneg w]
    have h := seriesOnDisc_atanhCoeff.hasDerivAt_odd_series hw1
    rw [tsum_atanh_deriv hw2] at h
    simpa [one_div] using h
  · intro w hw
    exact hasDerivAt_artanh (mem_ball_zero_iff.mp hw)
  · simp

/-- The series `∑ₙ zⁿ / (n+1)` sums to `-log(1-z)/z` for `0 < ‖z‖ < 1`. -/
theorem hasSum_neg_log_div (z : ℂ) (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasSum (fun n : ℕ => (1 / ((n : ℂ) + 1)) * z ^ n) (-(Complex.log (1 - z) / z)) := by
  have H := Complex.hasSum_taylorSeries_neg_log hz
  have hshift : HasSum (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1)) (-Complex.log (1 - z)) := by
    have hinj : Function.Injective (fun n : ℕ => n + 1) := fun m n h => by simpa using h
    have hzero : ∀ x ∉ Set.range (fun n : ℕ => n + 1), (fun n : ℕ => z ^ n / (n : ℂ)) x = 0 := by
      intro x hx
      have : x = 0 := by
        by_contra h
        exact hx ⟨x - 1, by simp only []; omega⟩
      simp [this]
    have := (hinj.hasSum_iff (f := fun n : ℕ => z ^ n / (n : ℂ)) hzero).mpr H
    refine this.congr_fun fun n => ?_
    simp [Function.comp]
  have h2 := hshift.div_const z
  rw [neg_div] at h2
  refine h2.congr_fun fun n => ?_
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    have h := Nat.cast_ne_zero (R := ℂ) (n := n + 1) |>.mpr (Nat.succ_ne_zero n)
    simpa using h
  field_simp
  ring

end Series

end Complex
