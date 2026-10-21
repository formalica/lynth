import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Fixed-point sine/cosine on [-2,2]. Only integer endpoint arithmetic is
used in the series loop. This Mathlib-only module is mirrored in /tmp/intgrl.
The series is an elementary-function kernel, not Taylor quadrature. -/

namespace Intgrl

/-- The remaining series is bounded by twice the current term from index 1.
Endpoint products are divided with directed integer rounding. -/
def fixedTrigLoop (p : ℕ) (a2 : ℤ) (sine : Bool) :
    ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ × ℤ
  | 0, k, lo, hi, sl, sh =>
      if k = 0 then (-((2 : ℤ)^p), (2 : ℤ)^p) else
        let tail := (2 * max lo.natAbs hi.natAbs : ℕ)
        (sl - tail, sh + tail)
  | fuel + 1, k, lo, hi, sl, sh =>
      let sl := sl + lo
      let sh := sh + hi
      let d : ℤ := if sine then (2*k+2)*(2*k+3) else (2*k+1)*(2*k+2)
      let nextLo := ((-hi * a2) >>> (2*p)) / d
      let nextHi := -(((lo * a2) >>> (2*p)) / d)
      if k ≥ 1 && max nextLo.natAbs nextHi.natAbs ≤ 1 then
        (sl - 2, sh + 2)
      else fixedTrigLoop p a2 sine fuel (k+1) nextLo nextHi sl sh

/-- Bounds in units of 2^(-p). Rounding the argument down costs at most
one unit by the Lipschitz bounds for sine and cosine. -/
def fixedTrigBounds (p : ℕ) (sine : Bool) (x : ℚ) : ℤ × ℤ :=
  let scale : ℤ := (2 : ℤ)^p
  if x = 0 then
    if sine then (0, 0) else (scale, scale)
  else
    let a := (x * (scale : ℚ)).floor
    let first := if sine then a else scale
    let (lo, hi) := fixedTrigLoop p (a*a) sine (p+16) 0 first first 0 0
    (lo-1, hi+1)

/-- Generic fixed-point series contract. The proof consists of the rounded
term recurrence invariant, a geometric tail from index 1, and the argument
rounding error. No interval implementation or integration definitions occur. -/
theorem trig_ediv_le_real (u m : ℤ) (hm : 0 < m) : ((u / m : ℤ) : ℝ) ≤ (u : ℝ) / m := by
  rw [le_div_iff₀ (by exact_mod_cast hm)]
  exact_mod_cast Int.ediv_mul_le u hm.ne'

theorem trig_shiftRight_le_real (u : ℤ) (p : ℕ) : ((u >>> p : ℤ) : ℝ) ≤ (u : ℝ) / 2 ^ p := by
  rw [Int.shiftRight_eq_div_pow]
  have := trig_ediv_le_real u (↑(2 ^ p)) (by positivity)
  simpa using this

theorem tail_le_two_mul {f : ℕ → ℝ} {S : ℝ} (hf : HasSum f S) (k : ℕ)
    (hr : ∀ j, k ≤ j → |f (j + 1)| ≤ |f j| / 2) :
    |S - ∑ j ∈ Finset.range k, f j| ≤ 2 * |f k| := by
  have h1 := (hasSum_nat_add_iff' k).2 hf
  have hb : ∀ n, |f (n + k)| ≤ |f k| * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hr (n + k) (by omega)
      rw [show n + 1 + k = n + k + 1 by ring, pow_succ]
      linarith
  have h2 : HasSum (fun n => |f k| * (1 / 2) ^ n) (|f k| * 2) := hasSum_geometric_two.mul_left _
  have := h1.norm_le_of_bounded h2 (fun n => by rw [Real.norm_eq_abs]; exact hb n)
  rw [Real.norm_eq_abs] at this
  linarith

def trigS (sine : Bool) : ℕ := if sine then 1 else 0

noncomputable def trigFun (sine : Bool) (t : ℝ) : ℝ := if sine then Real.sin t else Real.cos t

noncomputable def trigTerm (p : ℕ) (a : ℤ) (sine : Bool) (k : ℕ) : ℝ :=
  2 ^ p * ((-1) ^ k * ((a : ℝ) / 2 ^ p) ^ (2 * k + trigS sine) /
    (2 * k + trigS sine).factorial)

theorem trigTerm_hasSum (p : ℕ) (a : ℤ) (sine : Bool) :
    HasSum (trigTerm p a sine) (2 ^ p * trigFun sine ((a : ℝ) / 2 ^ p)) := by
  unfold trigTerm trigFun
  cases sine
  · simpa [trigS] using (Real.hasSum_cos ((a : ℝ) / 2 ^ p)).mul_left (2 ^ p)
  · simpa [trigS] using (Real.hasSum_sin ((a : ℝ) / 2 ^ p)).mul_left (2 ^ p)

theorem trigTerm_succ (p : ℕ) (a : ℤ) (sine : Bool) (k : ℕ) :
    trigTerm p a sine (k + 1) = -(trigTerm p a sine k) * ((a * a : ℤ) : ℝ) /
      (2 ^ (2 * p) * (((if sine then (2*k+2)*(2*k+3) else (2*k+1)*(2*k+2) : ℤ)) : ℝ)) := by
  unfold trigTerm
  rw [show (2:ℝ) ^ (2 * p) = (2 ^ p) ^ 2 by rw [← pow_mul, mul_comm]]
  cases sine
  · simp only [trigS, Bool.false_eq_true, ite_false, add_zero]
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    simp only [div_pow, pow_succ]
    push_cast
    field_simp
    ring
  · simp only [trigS, ite_true]
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    simp only [div_pow, pow_succ]
    push_cast
    field_simp
    ring

theorem trigTerm_ratio (p : ℕ) (a : ℤ) (sine : Bool) (ht : |(a : ℝ) / 2 ^ p| ≤ 2) (j : ℕ)
    (hj : 1 ≤ j) : |trigTerm p a sine (j + 1)| ≤ |trigTerm p a sine j| / 2 := by
  set D : ℝ := (((if sine then (2*j+2)*(2*j+3) else (2*j+1)*(2*j+2) : ℤ)) : ℝ) with hDdef
  have hj' : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hD : (12:ℝ) ≤ D := by
    rw [hDdef]; cases sine <;> simp <;> nlinarith
  have h2p : (0:ℝ) < 2 ^ p := by positivity
  have e : trigTerm p a sine (j + 1) =
      -(trigTerm p a sine j) * (((a : ℝ) / 2 ^ p) ^ 2 / D) := by
    rw [trigTerm_succ, ← hDdef]
    rw [show (2:ℝ) ^ (2 * p) = (2 ^ p) ^ 2 by rw [← pow_mul, mul_comm]]
    push_cast
    field_simp
  have ht2 : ((a : ℝ) / 2 ^ p) ^ 2 ≤ 4 := by
    have := sq_abs ((a : ℝ) / 2 ^ p)
    nlinarith [abs_nonneg ((a : ℝ) / 2 ^ p)]
  have hq : ((a : ℝ) / 2 ^ p) ^ 2 / D ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hq0 : 0 ≤ ((a : ℝ) / 2 ^ p) ^ 2 / D := div_nonneg (sq_nonneg _) (by linarith)
  rw [e, abs_mul, abs_neg, abs_of_nonneg hq0]
  have := abs_nonneg (trigTerm p a sine j)
  nlinarith

theorem trigFun_abs_le (sine : Bool) (t : ℝ) : |trigFun sine t| ≤ 1 := by
  unfold trigFun; cases sine
  · simpa using Real.abs_cos_le_one t
  · simpa using Real.abs_sin_le_one t

theorem fixedTrigLoop_sound (p : ℕ) (a : ℤ) (sine : Bool) (ht : |(a : ℝ) / 2 ^ p| ≤ 2) :
    ∀ (fuel k : ℕ) (lo hi sl sh : ℤ),
      (lo : ℝ) ≤ trigTerm p a sine k → trigTerm p a sine k ≤ hi →
      (sl : ℝ) ≤ ∑ j ∈ Finset.range k, trigTerm p a sine j →
      ∑ j ∈ Finset.range k, trigTerm p a sine j ≤ sh →
      ((fixedTrigLoop p (a * a) sine fuel k lo hi sl sh).1 : ℝ) ≤
        2 ^ p * trigFun sine ((a : ℝ) / 2 ^ p) ∧
      2 ^ p * trigFun sine ((a : ℝ) / 2 ^ p) ≤
        (fixedTrigLoop p (a * a) sine fuel k lo hi sl sh).2 := by
  have h2p : (0:ℝ) < 2 ^ p := by positivity
  have hS := trigTerm_hasSum p a sine
  have hf := trigFun_abs_le sine ((a : ℝ) / 2 ^ p)
  have hfS : |2 ^ p * trigFun sine ((a : ℝ) / 2 ^ p)| ≤ 2 ^ p := by
    rw [abs_mul, abs_of_pos h2p]; nlinarith [abs_nonneg (trigFun sine ((a : ℝ) / 2 ^ p))]
  have htail : ∀ k, 1 ≤ k → |2 ^ p * trigFun sine ((a : ℝ) / 2 ^ p) -
      ∑ j ∈ Finset.range k, trigTerm p a sine j| ≤ 2 * |trigTerm p a sine k| := fun k hk =>
    tail_le_two_mul hS k (fun j hj => trigTerm_ratio p a sine ht j (by omega))
  intro fuel
  induction fuel with
  | zero =>
    intro k lo hi sl sh hlo hhi hsl hsh
    simp only [fixedTrigLoop]
    split_ifs with hk0
    · rw [abs_le] at hfS; push_cast; constructor <;> linarith
    · have ht' := htail k (by omega)
      have hT : |trigTerm p a sine k| ≤ max |(lo:ℝ)| |(hi:ℝ)| := by
        rw [abs_le]; constructor
        · linarith [neg_abs_le (lo:ℝ), le_max_left |(lo:ℝ)| |(hi:ℝ)|]
        · linarith [le_abs_self (hi:ℝ), le_max_right |(lo:ℝ)| |(hi:ℝ)|]
      rw [abs_le] at ht'
      push_cast
      constructor <;> linarith
  | succ fuel ih =>
    intro k lo hi sl sh hlo hhi hsl hsh
    simp only [fixedTrigLoop]
    set d : ℤ := (if sine then (2*k+2)*(2*k+3) else (2*k+1)*(2*k+2) : ℤ) with hd
    have hdpos : 0 < d := by rw [hd]; split_ifs <;> positivity
    have hdr : (0:ℝ) < d := by exact_mod_cast hdpos
    have hsucc := trigTerm_succ p a sine k
    rw [← hd] at hsucc
    have ha2 : (0:ℝ) ≤ ((a * a : ℤ) : ℝ) := by push_cast; nlinarith
    have h4p : (0:ℝ) < 2 ^ (2 * p) := by positivity
    have hNL : (((-hi * (a * a)) >>> (2 * p) / d : ℤ) : ℝ) ≤ trigTerm p a sine (k + 1) := by
      have h1 := trig_ediv_le_real ((-hi * (a * a)) >>> (2 * p)) d hdpos
      have h2 := trig_shiftRight_le_real (-hi * (a * a)) (2 * p)
      rw [hsucc]
      have h3 : ((-hi * (a * a) : ℤ) : ℝ) ≤ -(trigTerm p a sine k) * ((a * a : ℤ) : ℝ) := by
        push_cast at ha2 ⊢; nlinarith
      calc (((-hi * (a * a)) >>> (2 * p) / d : ℤ) : ℝ)
          ≤ (((-hi * (a * a)) >>> (2 * p) : ℤ) : ℝ) / d := h1
        _ ≤ (((-hi * (a * a) : ℤ) : ℝ) / 2 ^ (2 * p)) / d := by gcongr
        _ ≤ (-(trigTerm p a sine k) * ((a * a : ℤ) : ℝ) / 2 ^ (2 * p)) / d := by gcongr
        _ = _ := by rw [div_div]
    have hNH : trigTerm p a sine (k + 1) ≤ ((-((lo * (a * a)) >>> (2 * p) / d) : ℤ) : ℝ) := by
      have h1 := trig_ediv_le_real ((lo * (a * a)) >>> (2 * p)) d hdpos
      have h2 := trig_shiftRight_le_real (lo * (a * a)) (2 * p)
      rw [hsucc]
      have h3 : ((lo * (a * a) : ℤ) : ℝ) ≤ trigTerm p a sine k * ((a * a : ℤ) : ℝ) := by
        push_cast at ha2 ⊢; nlinarith
      have h4 : (((lo * (a * a)) >>> (2 * p) / d : ℤ) : ℝ) ≤
          (trigTerm p a sine k * ((a * a : ℤ) : ℝ) / 2 ^ (2 * p)) / d := by
        calc (((lo * (a * a)) >>> (2 * p) / d : ℤ) : ℝ)
            ≤ (((lo * (a * a)) >>> (2 * p) : ℤ) : ℝ) / d := h1
          _ ≤ (((lo * (a * a) : ℤ) : ℝ) / 2 ^ (2 * p)) / d := by gcongr
          _ ≤ _ := by gcongr
      have e : -(trigTerm p a sine k) * ((a * a : ℤ) : ℝ) / (2 ^ (2 * p) * (d : ℝ)) =
          -((trigTerm p a sine k * ((a * a : ℤ) : ℝ) / 2 ^ (2 * p)) / d) := by
        rw [div_div]; ring
      rw [e]; push_cast at h4 ⊢; linarith
    generalize (-hi * (a * a)) >>> (2 * p) / d = nl at hNL ⊢
    generalize -((lo * (a * a)) >>> (2 * p) / d) = nh at hNH ⊢
    have hsl' : ((sl + lo : ℤ) : ℝ) ≤ ∑ j ∈ Finset.range (k + 1), trigTerm p a sine j := by
      rw [Finset.sum_range_succ]; push_cast; linarith
    have hsh' : ∑ j ∈ Finset.range (k + 1), trigTerm p a sine j ≤ ((sh + hi : ℤ) : ℝ) := by
      rw [Finset.sum_range_succ]; push_cast; linarith
    split_ifs with hstop
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hstop
      have h1 : nl.natAbs ≤ 1 := le_trans (le_max_left _ _) hstop.2
      have h2 : nh.natAbs ≤ 1 := le_trans (le_max_right _ _) hstop.2
      have h3 : (-1 : ℤ) ≤ nl := by omega
      have h4 : nh ≤ (1 : ℤ) := by omega
      have h3' : (-1 : ℝ) ≤ nl := by exact_mod_cast h3
      have h4' : (nh : ℝ) ≤ 1 := by exact_mod_cast h4
      have ht' := htail (k + 1) (by omega)
      have hT : |trigTerm p a sine (k + 1)| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
      rw [abs_le] at ht'
      push_cast at hsl' hsh' ⊢
      constructor <;> linarith
    · exact ih (k + 1) nl nh (sl + lo) (sh + hi) hNL hNH hsl' hsh'

/-- Generic fixed-point series contract. The proof consists of the rounded
term recurrence invariant, a geometric tail from index 1, and the argument
rounding error. No interval implementation or integration definitions occur. -/

theorem fixedTrigBounds_sound (p : ℕ) (sine : Bool) (x : ℚ)
    (hx : |(x : ℝ)| ≤ 2) :
    ((fixedTrigBounds p sine x).1 : ℝ) * (2 : ℝ)^(-(p : ℤ)) ≤
      (if sine then Real.sin (x : ℝ) else Real.cos (x : ℝ)) ∧
    (if sine then Real.sin (x : ℝ) else Real.cos (x : ℝ)) ≤
      ((fixedTrigBounds p sine x).2 : ℝ) * (2 : ℝ)^(-(p : ℤ)) := by
  have h2p : (0:ℝ) < 2 ^ p := by positivity
  have hzp : (2 : ℝ)^(-(p : ℤ)) = 1 / 2 ^ p := by
    rw [zpow_neg, zpow_natCast, one_div]
  rw [hzp]
  change ((fixedTrigBounds p sine x).1 : ℝ) * (1 / 2 ^ p) ≤ trigFun sine x ∧
    trigFun sine x ≤ ((fixedTrigBounds p sine x).2 : ℝ) * (1 / 2 ^ p)
  by_cases hx0 : x = 0
  · subst hx0; cases sine <;> simp [fixedTrigBounds, trigFun]
  · simp only [fixedTrigBounds, hx0, ite_false]
    set a : ℤ := (x * ((2:ℤ)^p : ℤ)).floor with ha
    have hfl1 : (a : ℝ) ≤ (x : ℝ) * 2 ^ p := by
      have : ((a : ℤ) : ℚ) ≤ x * ((2:ℤ)^p : ℤ) := Int.floor_le _
      have h := (Rat.cast_le (K := ℝ)).2 this
      push_cast at h
      exact h
    have hfl2 : (x : ℝ) * 2 ^ p < a + 1 := by
      have : x * ((2:ℤ)^p : ℤ) < ((a : ℤ) : ℚ) + 1 := Int.lt_floor_add_one _
      have h := (Rat.cast_lt (K := ℝ)).2 this
      push_cast at h
      exact h
    have hxa := abs_le.1 hx
    have hlow : -(2:ℤ) ^ (p + 1) ≤ a := by
      have h1 : ((-(2:ℤ) ^ (p + 1) - 1 : ℤ) : ℝ) < a := by
        push_cast; rw [pow_succ]; nlinarith
      have h2 : -(2:ℤ) ^ (p + 1) - 1 < a := by exact_mod_cast h1
      omega
    have hlow' : -(2:ℝ) * 2 ^ p ≤ a := by
      have := (Int.cast_le (R := ℝ)).2 hlow
      push_cast at this; rw [pow_succ] at this; linarith
    set t : ℝ := (a : ℝ) / 2 ^ p with htdef
    have ht1 : t ≤ x := by rw [htdef, div_le_iff₀ h2p]; linarith
    have ht2 : (x : ℝ) - 1 / 2 ^ p < t := by
      rw [htdef, lt_div_iff₀ h2p, sub_mul, div_mul_cancel₀ _ h2p.ne']; linarith
    have ht3 : -2 ≤ t := by rw [htdef, le_div_iff₀ h2p]; linarith
    have ht : |t| ≤ 2 := abs_le.2 ⟨ht3, by linarith⟩
    have h0eq : trigTerm p a sine 0 = (((if sine then a else (2:ℤ) ^ p) : ℤ) : ℝ) := by
      cases sine
      · simp [trigTerm, trigS]
      · simp only [trigTerm, trigS, ite_true]
        simp only [mul_zero, zero_add, pow_zero, one_mul, pow_one, Nat.factorial_one,
          Nat.cast_one, div_one]
        exact mul_div_cancel₀ _ h2p.ne'
    have h0lo : (((if sine then a else (2:ℤ) ^ p) : ℤ) : ℝ) ≤ trigTerm p a sine 0 := h0eq.ge
    have h0hi : trigTerm p a sine 0 ≤ (((if sine then a else (2:ℤ) ^ p) : ℤ) : ℝ) := h0eq.le
    have hloop := fixedTrigLoop_sound p a sine ht (p + 16) 0 _ _ 0 0 h0lo h0hi
      (by simp) (by simp)
    generalize fixedTrigLoop p (a * a) sine (p + 16) 0 (if sine then a else 2 ^ p)
      (if sine then a else 2 ^ p) 0 0 = res at hloop ⊢
    obtain ⟨L, H⟩ := res
    simp only at hloop ⊢
    obtain ⟨hL, hH⟩ := hloop
    have hlip : |trigFun sine x - trigFun sine t| ≤ 1 / 2 ^ p := by
      have : |(x:ℝ) - t| ≤ 1 / 2 ^ p := abs_le.2 ⟨by linarith, by linarith⟩
      refine le_trans ?_ this
      unfold trigFun; cases sine
      · simpa using Real.abs_cos_sub_cos_le x t
      · simpa using Real.abs_sin_sub_sin_le x t
    rw [abs_le] at hlip
    push_cast
    constructor
    · rw [← div_eq_mul_one_div, div_le_iff₀ h2p]
      have e2 : (1 / 2 ^ p) * (2:ℝ) ^ p = 1 := by field_simp
      nlinarith
    · rw [← div_eq_mul_one_div, le_div_iff₀ h2p]
      have e2 : (1 / 2 ^ p) * (2:ℝ) ^ p = 1 := by field_simp
      nlinarith

end Intgrl
