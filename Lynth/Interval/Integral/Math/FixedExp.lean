module

public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Bitwise.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Integer endpoint arithmetic for exp on [-1/2,1/2]. Mathlib-only proof
handoff; ordinary scaling and squaring reconstructs the full exponential. -/

namespace Intgrl

@[expose] public def fixedExpLoop (p : ℕ) (a : ℤ) :
    ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ × ℤ
  | 0, _, lo, hi, sl, sh =>
      let tail := (2 * max lo.natAbs hi.natAbs : ℕ)
      (sl-tail, sh+tail)
  | fuel+1, k, lo, hi, sl, sh =>
      let sl := sl+lo
      let sh := sh+hi
      let (l,h) := if 0 ≤ a then (lo*a,hi*a) else (hi*a,lo*a)
      let nextLo := (l >>> p) / (k+1 : ℤ)
      let nextHi := -(((-h) >>> p) / (k+1 : ℤ))
      if max nextLo.natAbs nextHi.natAbs ≤ 1 then (sl-2, sh+2)
      else fixedExpLoop p a fuel (k+1) nextLo nextHi sl sh

@[expose] public def fixedExpBounds (p : ℕ) (x : ℚ) : ℤ × ℤ :=
  let scale : ℤ := (2 : ℤ)^p
  if x = 0 then (scale,scale) else
    let a := (x * (scale : ℚ)).floor
    let (lo,hi) := fixedExpLoop p a (p+16) 0 scale scale 0 0
    (lo-2,hi+2)

/-- Rounded series invariant, geometric tail, and a two-unit bound for
rounding the reduced argument. -/
theorem int_ediv_le_real (u m : ℤ) (hm : 0 < m) : ((u / m : ℤ) : ℝ) ≤ (u : ℝ) / m := by
  rw [le_div_iff₀ (by exact_mod_cast hm)]
  exact_mod_cast Int.ediv_mul_le u hm.ne'

theorem int_shiftRight_le_real (u : ℤ) (p : ℕ) : ((u >>> p : ℤ) : ℝ) ≤ (u : ℝ) / 2 ^ p := by
  rw [Int.shiftRight_eq_div_pow]
  have := int_ediv_le_real u (↑(2 ^ p)) (by positivity)
  simpa using this

/-- Scaled exponential series terms. -/
noncomputable def expTerm (p : ℕ) (a : ℤ) (j : ℕ) : ℝ :=
  2 ^ p * ((a : ℝ) / 2 ^ p) ^ j / j.factorial

theorem expTerm_succ (p : ℕ) (a : ℤ) (j : ℕ) :
    expTerm p a (j + 1) = expTerm p a j * a / (2 ^ p * (j + 1)) := by
  unfold expTerm
  simp only [div_pow, pow_succ, Nat.factorial_succ]
  push_cast
  field_simp

theorem expTerm_tail (p : ℕ) (a : ℤ) (ht : |(a : ℝ) / 2 ^ p| ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    |2 ^ p * Real.exp ((a : ℝ) / 2 ^ p) - ∑ j ∈ Finset.range k, expTerm p a j| ≤
      2 * |expTerm p a k| := by
  have h := Real.exp_bound ht (n := k) (by omega)
  have e : 2 ^ p * Real.exp ((a : ℝ) / 2 ^ p) - ∑ j ∈ Finset.range k, expTerm p a j =
      2 ^ p * (Real.exp ((a : ℝ) / 2 ^ p) -
        ∑ m ∈ Finset.range k, ((a : ℝ) / 2 ^ p) ^ m / m.factorial) := by
    rw [mul_sub, Finset.mul_sum]; unfold expTerm
    congr 1; refine Finset.sum_congr rfl fun j _ => by ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 ^ p)]
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hfac : (0:ℝ) < k.factorial := by positivity
  have hr : ((k.succ : ℕ) : ℝ) / (k.factorial * k) ≤ 2 / k.factorial := by
    rw [div_le_div_iff₀ (by positivity) hfac]
    push_cast; nlinarith
  calc 2 ^ p * |Real.exp ((a:ℝ) / 2 ^ p) -
        ∑ m ∈ Finset.range k, ((a : ℝ) / 2 ^ p) ^ m / m.factorial|
      ≤ 2 ^ p * (|(a:ℝ) / 2 ^ p| ^ k * (k.succ / (k.factorial * k))) := by gcongr
    _ ≤ 2 ^ p * (|(a:ℝ) / 2 ^ p| ^ k * (2 / k.factorial)) := by gcongr
    _ = 2 * |expTerm p a k| := by
      have : |expTerm p a k| = 2 ^ p * |(a:ℝ) / 2 ^ p| ^ k / k.factorial := by
        unfold expTerm
        rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 ^ p), abs_pow,
          abs_of_pos hfac]
      rw [this]; ring

theorem fixedExpLoop_sound (p : ℕ) (a : ℤ) (ht : |(a : ℝ) / 2 ^ p| ≤ 1) :
    ∀ (fuel k : ℕ) (lo hi sl sh : ℤ), 1 ≤ k + fuel →
      (lo : ℝ) ≤ expTerm p a k → expTerm p a k ≤ hi →
      (sl : ℝ) ≤ ∑ j ∈ Finset.range k, expTerm p a j →
      ∑ j ∈ Finset.range k, expTerm p a j ≤ sh →
      ((fixedExpLoop p a fuel k lo hi sl sh).1 : ℝ) ≤ 2 ^ p * Real.exp ((a : ℝ) / 2 ^ p) ∧
      2 ^ p * Real.exp ((a : ℝ) / 2 ^ p) ≤ (fixedExpLoop p a fuel k lo hi sl sh).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro k lo hi sl sh hk hlo hhi hsl hsh
    simp only [fixedExpLoop]
    have htail := expTerm_tail p a ht k (by omega)
    have hT : |expTerm p a k| ≤ max |(lo:ℝ)| |(hi:ℝ)| := by
      rw [abs_le]; constructor
      · linarith [neg_abs_le (lo:ℝ), le_max_left |(lo:ℝ)| |(hi:ℝ)|]
      · linarith [le_abs_self (hi:ℝ), le_max_right |(lo:ℝ)| |(hi:ℝ)|]
    rw [abs_le] at htail
    push_cast at hT ⊢
    constructor <;> linarith
  | succ fuel ih =>
    intro k lo hi sl sh hk hlo hhi hsl hsh
    simp only [fixedExpLoop]
    have hk1 : (0:ℤ) < (k:ℤ) + 1 := by positivity
    have hk1r : (0:ℝ) < (k:ℝ) + 1 := by positivity
    have h2p : (0:ℝ) < 2 ^ p := by positivity
    have hPl : (((if 0 ≤ a then (lo * a, hi * a) else (hi * a, lo * a)).1 : ℤ) : ℝ) ≤
        expTerm p a k * a := by
      split_ifs with ha
      · push_cast; exact mul_le_mul_of_nonneg_right hlo (by exact_mod_cast ha)
      · push_cast
        exact mul_le_mul_of_nonpos_right hhi (by exact_mod_cast (le_of_lt (not_le.1 ha)))
    have hPh : expTerm p a k * a ≤
        (((if 0 ≤ a then (lo * a, hi * a) else (hi * a, lo * a)).2 : ℤ) : ℝ) := by
      split_ifs with ha
      · push_cast; exact mul_le_mul_of_nonneg_right hhi (by exact_mod_cast ha)
      · push_cast
        exact mul_le_mul_of_nonpos_right hlo (by exact_mod_cast (le_of_lt (not_le.1 ha)))
    generalize (if 0 ≤ a then (lo * a, hi * a) else (hi * a, lo * a)).1 = l at hPl ⊢
    generalize (if 0 ≤ a then (lo * a, hi * a) else (hi * a, lo * a)).2 = h at hPh ⊢
    have hsucc := expTerm_succ p a k
    have hNL : ((l >>> p / ((k:ℤ) + 1) : ℤ) : ℝ) ≤ expTerm p a (k + 1) := by
      have h1 := int_ediv_le_real (l >>> p) ((k:ℤ) + 1) hk1
      have h2 := int_shiftRight_le_real l p
      push_cast at h1
      rw [hsucc]
      calc ((l >>> p / ((k:ℤ) + 1) : ℤ) : ℝ) ≤ ((l >>> p : ℤ) : ℝ) / ((k:ℝ) + 1) := h1
        _ ≤ ((l : ℝ) / 2 ^ p) / ((k:ℝ) + 1) := by gcongr
        _ ≤ (expTerm p a k * a / 2 ^ p) / ((k:ℝ) + 1) := by gcongr
        _ = expTerm p a k * a / (2 ^ p * (k + 1)) := by rw [div_div]
    have hNH : expTerm p a (k + 1) ≤ ((-((-h) >>> p / ((k:ℤ) + 1)) : ℤ) : ℝ) := by
      have h1 := int_ediv_le_real ((-h) >>> p) ((k:ℤ) + 1) hk1
      have h2 := int_shiftRight_le_real (-h) p
      push_cast at h1 h2 ⊢
      rw [hsucc]
      have h3 : ((((-h) >>> p : ℤ)) : ℝ) / ((k:ℝ) + 1) ≤ (-(h : ℝ) / 2 ^ p) / ((k:ℝ) + 1) := by
        gcongr
      have h4 : expTerm p a k * a / (2 ^ p * (k + 1)) ≤ (h : ℝ) / 2 ^ p / ((k:ℝ) + 1) := by
        rw [← div_div]; gcongr
      have h5 : -(h : ℝ) / 2 ^ p / ((k:ℝ) + 1) = -((h : ℝ) / 2 ^ p / ((k:ℝ) + 1)) := by ring
      linarith
    generalize l >>> p / ((k:ℤ) + 1) = nl at hNL ⊢
    generalize -((-h) >>> p / ((k:ℤ) + 1)) = nh at hNH ⊢
    have hsl' : ((sl + lo : ℤ) : ℝ) ≤ ∑ j ∈ Finset.range (k + 1), expTerm p a j := by
      rw [Finset.sum_range_succ]; push_cast; linarith
    have hsh' : ∑ j ∈ Finset.range (k + 1), expTerm p a j ≤ ((sh + hi : ℤ) : ℝ) := by
      rw [Finset.sum_range_succ]; push_cast; linarith
    split_ifs with hstop
    · have h1 : nl.natAbs ≤ 1 := le_trans (le_max_left _ _) hstop
      have h2 : nh.natAbs ≤ 1 := le_trans (le_max_right _ _) hstop
      have h3 : (-1 : ℤ) ≤ nl := by omega
      have h4 : nh ≤ (1 : ℤ) := by omega
      have h3' : (-1 : ℝ) ≤ nl := by exact_mod_cast h3
      have h4' : (nh : ℝ) ≤ 1 := by exact_mod_cast h4
      have htail := expTerm_tail p a ht (k + 1) (by omega)
      have hT : |expTerm p a (k + 1)| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
      rw [abs_le] at htail
      push_cast at hsl' hsh' ⊢
      constructor <;> linarith
    · exact ih (k + 1) nl nh (sl + lo) (sh + hi) (by omega) hNL hNH hsl' hsh'

theorem exp_half_le_two : Real.exp (1/2) ≤ 2 := by
  have h1 : Real.exp (1/2) * Real.exp (-(1/2)) = 1 := by
    rw [← Real.exp_add]; norm_num
  have h2 := Real.add_one_le_exp (-(1/2))
  have h3 := Real.exp_pos (1/2)
  nlinarith

/-- Rounded series invariant, geometric tail, and a two-unit bound for
rounding the reduced argument. -/

theorem fixedExpBounds_sound (p : ℕ) (hp : 0 < p) (x : ℚ)
    (hx : |(x : ℝ)| ≤ 1/2) :
    ((fixedExpBounds p x).1 : ℝ) * (2 : ℝ)^(-(p : ℤ)) ≤ Real.exp (x : ℝ) ∧
    Real.exp (x : ℝ) ≤ ((fixedExpBounds p x).2 : ℝ) * (2 : ℝ)^(-(p : ℤ)) := by
  have h2p : (0:ℝ) < 2 ^ p := by positivity
  have hzp : (2 : ℝ)^(-(p : ℤ)) = 1 / 2 ^ p := by
    rw [zpow_neg, zpow_natCast, one_div]
  rw [hzp]
  unfold fixedExpBounds
  split_ifs with hx0
  · subst hx0; simp
  · simp only
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
    set t : ℝ := (a : ℝ) / 2 ^ p with htdef
    have ht1 : t ≤ x := by rw [htdef, div_le_iff₀ h2p]; linarith
    have ht2 : (x : ℝ) - 1 / 2 ^ p < t := by
      rw [htdef, lt_div_iff₀ h2p, sub_mul, div_mul_cancel₀ _ h2p.ne']; linarith
    have hpow : (2:ℝ) ≤ 2 ^ p := by
      calc (2:ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp
    have hinv : 1 / (2:ℝ) ^ p ≤ 1 / 2 := by
      rw [div_le_div_iff₀ h2p (by norm_num)]; linarith
    have ht : |t| ≤ 1 := by
      rw [abs_le] at hx ⊢; constructor <;> linarith
    have hloop := fixedExpLoop_sound p a ht (p + 16) 0 (2 ^ p) (2 ^ p) 0 0 (by omega)
      (by simp [expTerm]) (by simp [expTerm]) (by simp) (by simp)
    generalize fixedExpLoop p a (p + 16) 0 (2 ^ p) (2 ^ p) 0 0 = res at hloop ⊢
    obtain ⟨L, H⟩ := res
    simp only at hloop ⊢
    obtain ⟨hL, hH⟩ := hloop
    have hmono : Real.exp t ≤ Real.exp x := Real.exp_le_exp.2 ht1
    have hxle : (x : ℝ) ≤ 1 / 2 := (abs_le.1 hx).2
    have hconv : Real.exp x - Real.exp t ≤ Real.exp x * (x - t) := by
      have := Real.add_one_le_exp (t - x)
      have e : Real.exp t = Real.exp x * Real.exp (t - x) := by
        rw [← Real.exp_add]; ring_nf
      rw [e]; nlinarith [Real.exp_pos x]
    have hex : Real.exp x ≤ 2 := (Real.exp_le_exp.2 hxle).trans exp_half_le_two
    have hdiff : Real.exp x * (x - t) ≤ 2 * (1 / 2 ^ p) := by
      apply mul_le_mul hex (by linarith) (by linarith) (by norm_num)
    push_cast
    constructor
    · rw [← div_eq_mul_one_div, div_le_iff₀ h2p]; nlinarith
    · rw [← div_eq_mul_one_div, le_div_iff₀ h2p]
      have : Real.exp x ≤ Real.exp t + 2 * (1 / 2 ^ p) := by linarith
      have e2 : (2 * (1 / 2 ^ p)) * (2:ℝ) ^ p = 2 := by field_simp
      nlinarith

end Intgrl
