import Lynth.Interval.Integral.Math.LegendreEval

/-! Integer-only Bonnet recurrence with delayed scalar divisions (FLINT).
This definition and its error contract are mirrored in /tmp/intgrl/FixedPoint.lean.
-/

namespace Intgrl

/-- State after the first k recurrence updates, storing a common denominator. -/
def fixedState (p : ℕ) (x : ℤ) : ℕ → ℤ × ℤ × ℤ
  | 0 => ((2 : ℤ) ^ p, x, 1)
  | k + 1 =>
    let (a, b, den) := fixedState p x k
    let j : ℤ := k + 1
    let t := (b * x).tdiv ((2 : ℤ) ^ p)
    let v := (2 * j + 1) * t - j * j * a
    if den * (j + 1) ≥ (2 : ℤ) ^ 62 then
      (b.tdiv den, v.tdiv den, j + 1)
    else (b, v, den * (j + 1))

/-- Simultaneous P_(n-1),P_n, in units of 2^(-p). -/
def fixedPair (p : ℕ) (x : ℤ) (n : ℕ) : ℤ × ℤ :=
  if n = 0 then (0, (2 : ℤ) ^ p) else
    let (a, b, den) := fixedState p x (n - 1)
    (a.tdiv (den.tdiv (n : ℤ)), b.tdiv den)

theorem tdiv_real_err (a b : ℤ) (hb : 0 < b) :
    |((a.tdiv b : ℤ) : ℝ) - (a : ℝ) / (b : ℝ)| < 1 := by
  have h := Int.mul_tdiv_add_tmod a b
  have h1 := Int.tmod_lt_of_pos a hb
  have h2 := Int.lt_tmod_of_pos a hb
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hR : (b:ℝ) * (a.tdiv b : ℤ) + (a.tmod b : ℤ) = a := by exact_mod_cast h
  have h1R : ((a.tmod b : ℤ) : ℝ) < b := by exact_mod_cast h1
  have h2R : -(b:ℝ) < ((a.tmod b : ℤ) : ℝ) := by exact_mod_cast h2
  have e : ((a.tdiv b : ℤ) : ℝ) - (a : ℝ) / (b : ℝ) = -((a.tmod b : ℤ) : ℝ) / b := by
    field_simp; linarith
  rw [e, abs_div, abs_of_pos hbR, div_lt_one hbR, abs_lt]
  constructor <;> linarith

/-- Energy coordinates for the error of the Legendre recurrence: for `|X| ≤ 1`,
`‖recZ X a b‖² = a² - 2Xab + b²`, which does not increase along the recurrence. -/
noncomputable def recZ (X a b : ℝ) : ℂ := ⟨b - X * a, Real.sqrt (1 - X ^ 2) * a⟩

theorem recZ_add (X a b a' b' : ℝ) :
    recZ X (a + a') (b + b') = recZ X a b + recZ X a' b' := by
  apply Complex.ext <;> simp [recZ] <;> ring

theorem recZ_sq (X a b : ℝ) (hX : |X| ≤ 1) :
    ‖recZ X a b‖ ^ 2 = a ^ 2 - 2 * X * a * b + b ^ 2 := by
  have h1 : 0 ≤ 1 - X ^ 2 := by
    have := abs_le.1 hX; nlinarith
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mk, recZ]
  simp only
  have := Real.mul_self_sqrt h1
  nlinarith [this]

theorem recZ_le (X a b : ℝ) (hX : |X| ≤ 1) : ‖recZ X a b‖ ≤ |a| + |b| := by
  have h := recZ_sq X a b hX
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, h]
  have : -(X * (a * b)) ≤ |a| * |b| := by
    rw [← abs_mul]
    calc -(X * (a * b)) ≤ |X * (a*b)| := neg_le_abs _
      _ = |X| * |a*b| := abs_mul _ _
      _ ≤ 1 * |a*b| := by gcongr
      _ = _ := one_mul _
  nlinarith [sq_abs a, sq_abs b]

theorem recZ_hom (X j a b : ℝ) (hX : |X| ≤ 1) (hj : 0 < j) :
    ‖recZ X b (((2 * j + 1) * X * b - j * a) / (j + 1))‖ ≤ ‖recZ X a b‖ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
    recZ_sq _ _ _ hX, recZ_sq _ _ _ hX]
  have hX2 : 0 ≤ 1 - X ^ 2 := by
    have := abs_le.1 hX; nlinarith
  have hF : (1 - X^2) * b^2 ≤ a ^ 2 - 2 * X * a * b + b ^ 2 := by
    nlinarith [sq_nonneg (a - X*b)]
  set c := ((2 * j + 1) * X * b - j * a) / (j + 1) with hc
  have hc' : c * (j+1) = (2 * j + 1) * X * b - j * a := by rw [hc]; field_simp
  have key : (j+1)^2 * (b ^ 2 - 2 * X * b * c + c ^ 2) =
      j^2 * (a ^ 2 - 2 * X * a * b + b ^ 2) + (2*j+1) * ((1 - X^2) * b^2) := by
    have : (j+1)^2 * (b ^ 2 - 2 * X * b * c + c ^ 2) =
        (j+1)^2 * b^2 - 2 * X * b * (j+1) * (c*(j+1)) + (c*(j+1))^2 := by ring
    rw [this, hc']; ring
  have hpos : 0 < (j+1)^2 := by positivity
  rw [← mul_le_mul_iff_of_pos_left hpos, key]
  nlinarith

/-- Budget for the accumulated energy of the rounding errors after `k` steps. -/
noncomputable def recG (k : ℕ) : ℝ := 3 * (k:ℝ) / 2 + 6 - 6 / ((k:ℝ) + 1)

theorem nat_quad_nonneg (k : ℕ) : 0 ≤ ((k:ℝ) - 1) * ((k:ℝ) - 2) := by
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k <;> norm_num
  · have : (2:ℝ) ≤ k := by exact_mod_cast h
    nlinarith

theorem rec_abstract_step (X : ℝ) (hX : |X| ≤ 1) (k : ℕ) (α β ρA ρB : ℝ)
    (hZ : ‖recZ X α β‖ ≤ recG k) (hβ : |β| ≤ (k:ℝ)^2 + 5*k)
    (hA : |ρA| ≤ 1) (hB : |ρB| ≤ (3*((k:ℝ)+1)+1) / (((k:ℝ)+1)*((k:ℝ)+2))) :
    ‖recZ X (β + ρA) (((2*((k:ℝ)+1)+1) * X * β - ((k:ℝ)+1) * α) / ((k:ℝ)+1+1) + ρB)‖
        ≤ recG (k+1) ∧
      |β + ρA| ≤ ((k+1:ℕ):ℝ)^2 + 5*((k+1:ℕ):ℝ) ∧
      |((2*((k:ℝ)+1)+1) * X * β - ((k:ℝ)+1) * α) / ((k:ℝ)+1+1) + ρB| ≤
        ((k+1:ℕ):ℝ)^2 + 5*((k+1:ℕ):ℝ) := by
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hZ' : ‖recZ X (β + ρA) (((2*((k:ℝ)+1)+1) * X * β - ((k:ℝ)+1) * α) / ((k:ℝ)+1+1) + ρB)‖
      ≤ recG (k+1) := by
    rw [recZ_add]
    refine (norm_add_le _ _).trans ?_
    have h1 := recZ_hom X ((k:ℝ)+1) α β hX (by positivity)
    have h2 := recZ_le X ρA ρB hX
    have hg : recG k + 1 + (3*((k:ℝ)+1)+1) / (((k:ℝ)+1)*((k:ℝ)+2)) ≤ recG (k+1) := by
      unfold recG
      push_cast
      rw [← sub_nonneg]
      have e : 3 * ((k:ℝ) + 1) / 2 + 6 - 6 / ((k:ℝ) + 1 + 1) -
          (3 * (k:ℝ) / 2 + 6 - 6 / ((k:ℝ) + 1) + 1 +
            (3 * ((k:ℝ) + 1) + 1) / (((k:ℝ) + 1) * ((k:ℝ) + 2)))
          = ((k:ℝ)^2 - 3*k + 6) / (2 * (((k:ℝ) + 1) * ((k:ℝ) + 2))) := by
        field_simp; ring
      rw [e]; apply div_nonneg <;> nlinarith
    linarith
  have hα' : |β + ρA| ≤ (k:ℝ)^2 + 5*k + 1 := (abs_add_le _ _).trans (by linarith)
  refine ⟨hZ', ?_, ?_⟩
  · push_cast; nlinarith
  · set β' := ((2*((k:ℝ)+1)+1) * X * β - ((k:ℝ)+1) * α) / ((k:ℝ)+1+1) + ρB
    have hre : |β' - X * (β + ρA)| ≤ ‖recZ X (β + ρA) β'‖ :=
      Complex.abs_re_le_norm (recZ X (β + ρA) β')
    have hXa : |X * (β + ρA)| ≤ |β + ρA| := by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hX
    have hb : |β'| ≤ |β' - X * (β + ρA)| + |X * (β + ρA)| := by
      have := abs_add_le (β' - X * (β + ρA)) (X * (β + ρA)); simpa using this
    have hg2 : recG (k+1) ≤ 2 * k + 5 := by
      unfold recG; push_cast
      have q := nat_quad_nonneg k
      rw [← sub_nonneg]
      have e : 2 * (k:ℝ) + 5 - (3 * ((k:ℝ) + 1) / 2 + 6 - 6 / ((k:ℝ) + 1 + 1)) =
          (((k:ℝ) - 1) * ((k:ℝ) - 2)) / (2 * ((k:ℝ) + 2)) := by
        field_simp; ring
      rw [e]; positivity
    push_cast
    nlinarith

theorem fixedState_succ (p : ℕ) (x : ℤ) (k : ℕ) (a b den : ℤ)
    (h : fixedState p x k = (a, b, den)) :
    fixedState p x (k+1) =
      if den * ((k:ℤ) + 1 + 1) ≥ (2 : ℤ) ^ 62 then
        (b.tdiv den, ((2 * ((k:ℤ)+1) + 1) * (b * x).tdiv ((2 : ℤ) ^ p) -
          ((k:ℤ)+1) * ((k:ℤ)+1) * a).tdiv den, (k:ℤ) + 1 + 1)
      else (b, (2 * ((k:ℤ)+1) + 1) * (b * x).tdiv ((2 : ℤ) ^ p) -
          ((k:ℤ)+1) * ((k:ℤ)+1) * a, den * ((k:ℤ) + 1 + 1)) := by
  rw [fixedState, h]

theorem fixedPoint_legendre_eval_rec (X : ℝ) (k : ℕ) :
    ((k:ℝ) + 2) * (legendre (k+2)).eval X =
      (2 * (k:ℝ) + 3) * X * (legendre (k+1)).eval X -
        ((k:ℝ)+1) * (legendre k).eval X := by
  rw [legendre]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  field_simp

theorem rec_step_eq (s X x a b den t τ j P0 P1 P2 : ℝ) (hs : s ≠ 0) (hden : den ≠ 0)
    (hj : j + 1 ≠ 0) (hX : x = X * s) (hτ : t = b * x / s + τ)
    (hrec : (j+1) * P2 = (2*j+1) * X * P1 - j * P0) :
    ((2*j+1) * t - j*j*a) / (den*(j+1)) - s*P2 =
      ((2*j+1) * X * (b/den - s * P1) - j * (a*j/den - s * P0)) / (j+1) +
        (2*j+1)*τ/(den*(j+1)) := by
  subst hX hτ
  field_simp
  linear_combination (-(s*den)) * hrec

/-- Invariant of the fixed-point Bonnet recurrence: positivity and divisibility of the
denominator, and the size of the scaled errors of both stored values. -/
theorem fixedState_inv (p : ℕ) (x : ℤ) (hx : |(x : ℝ) / (2 : ℝ) ^ p| ≤ 1) (k : ℕ) :
    0 < (fixedState p x k).2.2 ∧ ((k:ℤ) + 1) ∣ (fixedState p x k).2.2 ∧
    ‖recZ ((x : ℝ) / (2 : ℝ) ^ p)
        (((fixedState p x k).1 : ℝ) * ((k:ℝ) + 1) / ((fixedState p x k).2.2 : ℝ) -
          (2:ℝ)^p * (legendre k).eval ((x : ℝ) / (2 : ℝ) ^ p))
        (((fixedState p x k).2.1 : ℝ) / ((fixedState p x k).2.2 : ℝ) -
          (2:ℝ)^p * (legendre (k+1)).eval ((x : ℝ) / (2 : ℝ) ^ p))‖ ≤ recG k ∧
    |((fixedState p x k).1 : ℝ) * ((k:ℝ) + 1) / ((fixedState p x k).2.2 : ℝ) -
          (2:ℝ)^p * (legendre k).eval ((x : ℝ) / (2 : ℝ) ^ p)| ≤ (k:ℝ)^2 + 5*k ∧
    |((fixedState p x k).2.1 : ℝ) / ((fixedState p x k).2.2 : ℝ) -
          (2:ℝ)^p * (legendre (k+1)).eval ((x : ℝ) / (2 : ℝ) ^ p)| ≤ (k:ℝ)^2 + 5*k := by
  set X := (x : ℝ) / (2 : ℝ) ^ p with hXdef
  have hs : (0:ℝ) < (2:ℝ)^p := by positivity
  have hxX : (x:ℝ) = X * (2:ℝ)^p := by rw [hXdef]; field_simp
  induction k with
  | zero =>
    simp only [fixedState]
    have e1 : (x:ℝ) - (2:ℝ)^p * X = 0 := by rw [hxX]; ring
    refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
      simp [legendre, recG, recZ, e1, Complex.ext_iff]
  | succ k ih =>
    rcases hst : fixedState p x k with ⟨a, b, den⟩
    rw [hst] at ih
    simp only at ih
    obtain ⟨hden, hdvd, hZ, hα, hβ⟩ := ih
    rw [fixedState_succ p x k a b den hst]
    have hdenR : (0:ℝ) < den := by exact_mod_cast hden
    have hjden : (k:ℝ) + 1 ≤ den := by
      have := Int.le_of_dvd hden hdvd; exact_mod_cast this
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hrec := fixedPoint_legendre_eval_rec X k
    -- truncation in the product with x
    have hτ := tdiv_real_err (b * x) ((2:ℤ)^p) (by positivity)
    set t := (b * x).tdiv ((2:ℤ)^p) with ht
    set τ : ℝ := (t:ℝ) - ((b * x : ℤ) : ℝ) / (((2:ℤ)^p : ℤ) : ℝ) with hτdef
    have htτ : (t:ℝ) = (b:ℝ) * x / (2:ℝ)^p + τ := by rw [hτdef]; push_cast; ring
    set v := (2 * ((k:ℤ)+1) + 1) * t - ((k:ℤ)+1) * ((k:ℤ)+1) * a with hv
    have hvR : (v:ℝ) = (2 * ((k:ℝ)+1) + 1) * t - ((k:ℝ)+1) * ((k:ℝ)+1) * a := by
      rw [hv]; push_cast; ring
    set α := (a:ℝ) * ((k:ℝ) + 1) / (den:ℝ) - (2:ℝ)^p * (legendre k).eval X with hαdef
    set β := (b:ℝ) / (den:ℝ) - (2:ℝ)^p * (legendre (k+1)).eval X with hβdef
    have hmain : (v:ℝ) / ((den:ℝ) * ((k:ℝ) + 1 + 1)) - (2:ℝ)^p * (legendre (k+2)).eval X =
        ((2*((k:ℝ)+1)+1) * X * β - ((k:ℝ)+1) * α) / ((k:ℝ)+1+1) +
          (2*((k:ℝ)+1)+1) * τ / ((den:ℝ) * ((k:ℝ)+1+1)) := by
      rw [hvR, hαdef, hβdef]
      exact rec_step_eq _ X x a b den t τ ((k:ℝ)+1) _ _ _ hs.ne' hdenR.ne' (by positivity)
        hxX htτ (by linear_combination hrec)
    have hρ0 : |(2*((k:ℝ)+1)+1) * τ / ((den:ℝ) * ((k:ℝ)+1+1))| ≤
        (2*((k:ℝ)+1)+1) / (((k:ℝ)+1) * ((k:ℝ)+2)) := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*((k:ℝ)+1)+1),
        abs_of_pos (by positivity : (0:ℝ) < (den:ℝ) * ((k:ℝ)+1+1))]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (2*((k:ℝ)+1)+1) * |τ| ≤ (2*((k:ℝ)+1)+1) := by
        have := hτ.le; nlinarith
      have h2 : ((k:ℝ)+1) * ((k:ℝ)+2) ≤ (den:ℝ) * ((k:ℝ)+1+1) := by nlinarith
      nlinarith [abs_nonneg τ]
    split_ifs with hren
    · -- renormalisation step
      simp only
      have hρ1 := tdiv_real_err b den hden
      have hρ2 := tdiv_real_err v den hden
      refine ⟨by positivity, by push_cast; exact dvd_refl _, ?_⟩
      have eA : (((b.tdiv den : ℤ)) : ℝ) * (((k+1 : ℕ) : ℝ) + 1) / (((k:ℤ) + 1 + 1 : ℤ) : ℝ) -
          (2:ℝ)^p * (legendre (k+1)).eval X = β + ((b.tdiv den : ℤ) - (b:ℝ) / den) := by
        rw [hβdef]; push_cast; field_simp; ring
      have eB : (((v.tdiv den : ℤ)) : ℝ) / (((k:ℤ) + 1 + 1 : ℤ) : ℝ) -
          (2:ℝ)^p * (legendre (k+1+1)).eval X =
          ((2*((k:ℝ)+1)+1) * X * β - ((k:ℝ)+1) * α) / ((k:ℝ)+1+1) +
            ((2*((k:ℝ)+1)+1) * τ / ((den:ℝ) * ((k:ℝ)+1+1)) +
              ((v.tdiv den : ℤ) - (v:ℝ) / den) / ((k:ℝ)+1+1)) := by
        rw [← add_assoc, ← hmain]; push_cast; field_simp; ring
      rw [eA, eB]
      have hB : |(2*((k:ℝ)+1)+1) * τ / ((den:ℝ) * ((k:ℝ)+1+1)) +
              ((v.tdiv den : ℤ) - (v:ℝ) / den) / ((k:ℝ)+1+1)| ≤
          (3*((k:ℝ)+1)+1) / (((k:ℝ)+1)*((k:ℝ)+2)) := by
        refine (abs_add_le _ _).trans ?_
        have h3 : |(((v.tdiv den : ℤ) : ℝ) - (v:ℝ) / den) / ((k:ℝ)+1+1)| ≤ 1 / ((k:ℝ)+1+1) := by
          rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (k:ℝ)+1+1)]
          exact div_le_div_of_nonneg_right hρ2.le (by positivity)
        have e : (3*((k:ℝ)+1)+1) / (((k:ℝ)+1)*((k:ℝ)+2)) =
            (2*((k:ℝ)+1)+1) / (((k:ℝ)+1) * ((k:ℝ)+2)) + 1 / ((k:ℝ)+1+1) := by
          field_simp; ring
        rw [e]; linarith
      exact rec_abstract_step X hx k α β _ _ hZ hβ hρ1.le hB
    · simp only
      refine ⟨by positivity, by push_cast; exact Dvd.intro_left _ rfl, ?_⟩
      have eA : (b : ℝ) * (((k+1 : ℕ) : ℝ) + 1) / ((den * ((k:ℤ) + 1 + 1) : ℤ) : ℝ) -
          (2:ℝ)^p * (legendre (k+1)).eval X = β + 0 := by
        rw [hβdef]; push_cast; field_simp; ring
      have eB : (v : ℝ) / ((den * ((k:ℤ) + 1 + 1) : ℤ) : ℝ) -
          (2:ℝ)^p * (legendre (k+1+1)).eval X =
          ((2*((k:ℝ)+1)+1) * X * β - ((k:ℝ)+1) * α) / ((k:ℝ)+1+1) +
            (2*((k:ℝ)+1)+1) * τ / ((den:ℝ) * ((k:ℝ)+1+1)) := by
        rw [← hmain]; push_cast; ring_nf
      rw [eA, eB]
      have hB : |(2*((k:ℝ)+1)+1) * τ / ((den:ℝ) * ((k:ℝ)+1+1))| ≤
          (3*((k:ℝ)+1)+1) / (((k:ℝ)+1)*((k:ℝ)+2)) := by
        refine hρ0.trans ?_
        gcongr; linarith
      exact rec_abstract_step X hx k α β 0 _ hZ hβ (by simp) hB


theorem fixedPair_correct (p n : ℕ) (x : ℤ)
    (hx : |(x : ℝ) / (2 : ℝ) ^ p| ≤ 1) :
    |((fixedPair p x n).2 : ℝ) / (2 : ℝ) ^ p -
      (legendre n).eval ((x : ℝ) / (2 : ℝ) ^ p)| ≤
        (((n : ℝ) + 1) * ((n : ℝ) + 2)) / (2 : ℝ) ^ p ∧
    (0 < n →
      |((fixedPair p x n).1 : ℝ) / (2 : ℝ) ^ p -
        (legendre (n - 1)).eval ((x : ℝ) / (2 : ℝ) ^ p)| ≤
          (((n : ℝ) + 1) * ((n : ℝ) + 2)) / (2 : ℝ) ^ p) := by
  have hs : (0:ℝ) < (2:ℝ)^p := by positivity
  rcases n with _ | k
  · refine ⟨?_, fun h => absurd h (lt_irrefl 0)⟩
    simp [fixedPair, legendre, hs.ne']
    positivity
  set X := (x : ℝ) / (2 : ℝ) ^ p with hXdef
  obtain ⟨hden, hdvd, -, hα, hβ⟩ := fixedState_inv p x hx k
  rcases hst : fixedState p x k with ⟨a, b, den⟩
  rw [hst] at hden hdvd hα hβ
  simp only at hden hdvd hα hβ
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : 0 < q := by
    rcases lt_trichotomy q 0 with h | h | h
    · nlinarith
    · subst h; simp at hq; omega
    · exact h
  have hfp : fixedPair p x (k+1) = (a.tdiv q, b.tdiv den) := by
    simp only [fixedPair, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, hst]
    rw [hq]; push_cast
    rw [Int.mul_tdiv_cancel_left _ (by omega : ((k:ℤ) + 1) ≠ 0)]
  rw [hfp]
  have hρb := tdiv_real_err b den hden
  have hρa := tdiv_real_err a q hq0
  have hdenR : (den:ℝ) = ((k:ℝ)+1) * q := by rw [hq]; push_cast; ring
  have hqR : (0:ℝ) < q := by exact_mod_cast hq0
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hfin : (k:ℝ)^2 + 5*k + 1 ≤ ((((k+1:ℕ) : ℝ) + 1) * (((k+1:ℕ) : ℝ) + 2)) := by
    push_cast; nlinarith
  constructor
  · have e : ((b.tdiv den : ℤ) : ℝ) / (2:ℝ)^p - (legendre (k+1)).eval X =
        (((b:ℝ) / den - (2:ℝ)^p * (legendre (k+1)).eval X) +
          (((b.tdiv den : ℤ) : ℝ) - (b:ℝ) / den)) / (2:ℝ)^p := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos hs]
    apply div_le_div_of_nonneg_right _ hs.le
    exact (abs_add_le _ _).trans (by linarith)
  · intro _
    simp only [Nat.add_sub_cancel]
    have e : ((a.tdiv q : ℤ) : ℝ) / (2:ℝ)^p - (legendre k).eval X =
        (((a:ℝ) * ((k:ℝ) + 1) / den - (2:ℝ)^p * (legendre k).eval X) +
          (((a.tdiv q : ℤ) : ℝ) - (a:ℝ) / q)) / (2:ℝ)^p := by
      rw [hdenR]; field_simp; ring
    rw [e, abs_div, abs_of_pos hs]
    apply div_le_div_of_nonneg_right _ hs.le
    exact (abs_add_le _ _).trans (by linarith)

end Intgrl
