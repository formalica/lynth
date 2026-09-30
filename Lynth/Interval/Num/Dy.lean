import Lynth.Interval.Vendor.Dyadic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Dyadic numbers for interval arithmetic

`Dy` (= vendored LeanCert `Dyadic`, value `m * 2^e`) with directed rounding
to a relative precision of `p` mantissa bits.  Every rounded operation has a
lemma stating that it is below (`…D`) or above (`…U`) the exact result.

All functions are non-recursive, so they reduce well in the kernel.
See `docs/interval/02-numerics.md`.
-/

namespace Lynth.Interval

/-- Dyadic numbers `m * 2^e` (not normalized). -/
abbrev Dy := Vendor.Dyadic

namespace Dy

open Vendor.Dyadic (toRat toRat_eq)

/-- The real value `d.toReal` is the vendored `Vendor.Dyadic.toReal = Rat.cast ∘ toRat`. -/
theorem toReal_def (d : Dy) : d.toReal = (d.toRat : ℝ) := rfl

def ofInt (i : Int) : Dy := ⟨i, 0⟩
def ofNat (n : Nat) : Dy := ⟨n, 0⟩
def zero : Dy := ⟨0, 0⟩
def one : Dy := ⟨1, 0⟩

@[simp] theorem toRat_mk (m e : Int) : (⟨m, e⟩ : Dy).toRat = m * (2 : ℚ) ^ e := toRat_eq _

@[simp] theorem toRat_ofInt (i : Int) : (ofInt i).toRat = i := by simp [ofInt]
@[simp] theorem toRat_ofNat (n : Nat) : (ofNat n).toRat = n := by simp [ofNat]
@[simp] theorem toRat_zero : zero.toRat = 0 := by simp [zero]
@[simp] theorem toRat_one : one.toRat = 1 := by simp [one]

@[simp] theorem toRat_add' (a b : Dy) : (a.add b).toRat = a.toRat + b.toRat :=
  Vendor.Dyadic.toRat_add a b
@[simp] theorem toRat_mul' (a b : Dy) : (a.mul b).toRat = a.toRat * b.toRat :=
  Vendor.Dyadic.toRat_mul a b
@[simp] theorem toRat_neg' (a : Dy) : (a.neg).toRat = -a.toRat :=
  Vendor.Dyadic.toRat_neg a

/-- Exact scaling by `2^n`. -/
def scale2 (d : Dy) (n : Int) : Dy := ⟨d.mantissa, d.exponent + n⟩

@[simp] theorem toRat_scale2 (d : Dy) (n : Int) : (scale2 d n).toRat = d.toRat * 2 ^ n := by
  simp only [scale2, toRat_mk, toRat_eq d]
  rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]; ring

/-! ### Comparisons -/

/-- `a ≤ b` as a Bool. -/
def leB (a b : Dy) : Bool := Vendor.Dyadic.le a b
/-- `a < b` as a Bool. -/
def ltB (a b : Dy) : Bool := Vendor.Dyadic.lt a b

theorem leB_iff (a b : Dy) : leB a b = true ↔ a.toRat ≤ b.toRat :=
  Vendor.Dyadic.le_iff_toRat_le a b

theorem ltB_iff (a b : Dy) : ltB a b = true ↔ a.toRat < b.toRat := by
  unfold ltB Vendor.Dyadic.lt
  simp only [beq_iff_eq]
  exact Vendor.Dyadic.compare_lt_iff a b

theorem toReal_le_of_leB {a b : Dy} (h : leB a b = true) : a.toReal ≤ b.toReal := by
  rw [toReal_def, toReal_def]; exact_mod_cast (leB_iff a b).1 h

theorem toReal_lt_of_ltB {a b : Dy} (h : ltB a b = true) : a.toReal < b.toReal := by
  rw [toReal_def, toReal_def]; exact_mod_cast (ltB_iff a b).1 h

def min (a b : Dy) : Dy := if leB a b then a else b
def max (a b : Dy) : Dy := if leB a b then b else a

theorem toRat_min_le_left (a b : Dy) : (min a b).toRat ≤ a.toRat := by
  unfold min; split
  · exact le_rfl
  · rename_i h; simp only [Bool.not_eq_true] at h
    have : ¬ a.toRat ≤ b.toRat := fun h' => by simp [(leB_iff a b).2 h'] at h
    exact le_of_lt (not_le.1 this)

theorem toRat_min_le_right (a b : Dy) : (min a b).toRat ≤ b.toRat := by
  unfold min; split
  · rename_i h; exact (leB_iff a b).1 h
  · exact le_rfl

theorem le_toRat_max_left (a b : Dy) : a.toRat ≤ (max a b).toRat := by
  unfold max; split
  · rename_i h; exact (leB_iff a b).1 h
  · exact le_rfl

theorem le_toRat_max_right (a b : Dy) : b.toRat ≤ (max a b).toRat := by
  unfold max; split
  · exact le_rfl
  · rename_i h; simp only [Bool.not_eq_true] at h
    have : ¬ a.toRat ≤ b.toRat := fun h' => by simp [(leB_iff a b).2 h'] at h
    exact le_of_lt (not_le.1 this)

theorem toRat_min_eq_or (a b : Dy) : min a b = a ∨ min a b = b := by
  unfold min; split <;> simp

theorem toRat_max_eq_or (a b : Dy) : max a b = a ∨ max a b = b := by
  unfold max; split <;> simp

/-- Sign tests. -/
def isNeg (a : Dy) : Bool := decide (a.mantissa < 0)
def isPos (a : Dy) : Bool := decide (0 < a.mantissa)
def isNonneg (a : Dy) : Bool := decide (0 ≤ a.mantissa)
def isZero (a : Dy) : Bool := a.mantissa == 0

theorem two_zpow_pos (e : Int) : (0 : ℚ) < 2 ^ e := zpow_pos (by norm_num) e

theorem toRat_nonneg_iff (a : Dy) : 0 ≤ a.toRat ↔ 0 ≤ a.mantissa := by
  rw [toRat_eq]
  constructor
  · intro h
    by_contra hneg; push Not at hneg
    have : (a.mantissa : ℚ) * 2 ^ a.exponent < 0 :=
      mul_neg_of_neg_of_pos (by exact_mod_cast hneg) (two_zpow_pos _)
    linarith
  · intro h; exact mul_nonneg (by exact_mod_cast h) (le_of_lt (two_zpow_pos _))

theorem toRat_pos_iff (a : Dy) : 0 < a.toRat ↔ 0 < a.mantissa := by
  rw [toRat_eq]
  constructor
  · intro h
    by_contra hneg; push Not at hneg
    have : (a.mantissa : ℚ) * 2 ^ a.exponent ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hneg) (le_of_lt (two_zpow_pos _))
    linarith
  · intro h; exact mul_pos (by exact_mod_cast h) (two_zpow_pos _)

theorem toRat_neg_iff (a : Dy) : a.toRat < 0 ↔ a.mantissa < 0 := by
  have := toRat_nonneg_iff a
  constructor
  · intro h; by_contra h'; push Not at h'; linarith [this.2 h']
  · intro h; by_contra h'; push Not at h'; have := this.1 h'; omega

theorem toRat_eq_zero_iff (a : Dy) : a.toRat = 0 ↔ a.mantissa = 0 := by
  rw [toRat_eq]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · exact_mod_cast h
    · exact absurd h (ne_of_gt (two_zpow_pos _))
  · intro h; simp [h]

theorem isNonneg_iff (a : Dy) : isNonneg a = true ↔ 0 ≤ a.toRat := by
  simp [isNonneg, toRat_nonneg_iff]
theorem isPos_iff (a : Dy) : isPos a = true ↔ 0 < a.toRat := by
  simp [isPos, toRat_pos_iff]
theorem isNeg_iff (a : Dy) : isNeg a = true ↔ a.toRat < 0 := by
  simp [isNeg, toRat_neg_iff]

/-! ### Directed rounding to `p` mantissa bits -/

/-- Round down to at most `p` significant bits. -/
def rd (p : Nat) (d : Dy) : Dy := Vendor.Dyadic.normalizeDown d p
/-- Round up to at most `p` significant bits. -/
def ru (p : Nat) (d : Dy) : Dy := Vendor.Dyadic.normalizeUp d p

theorem rd_le (p : Nat) (d : Dy) : (rd p d).toRat ≤ d.toRat :=
  Vendor.Dyadic.toRat_normalizeDown_le d p
theorem le_ru (p : Nat) (d : Dy) : d.toRat ≤ (ru p d).toRat :=
  Vendor.Dyadic.toRat_normalizeUp_ge d p

def addD (p : Nat) (a b : Dy) : Dy := rd p (a.add b)
def addU (p : Nat) (a b : Dy) : Dy := ru p (a.add b)
def subD (p : Nat) (a b : Dy) : Dy := rd p (a.add b.neg)
def subU (p : Nat) (a b : Dy) : Dy := ru p (a.add b.neg)
def mulD (p : Nat) (a b : Dy) : Dy := rd p (a.mul b)
def mulU (p : Nat) (a b : Dy) : Dy := ru p (a.mul b)

theorem addD_le (p a b) : (addD p a b).toRat ≤ a.toRat + b.toRat := by
  unfold addD; simpa using rd_le p (a.add b)
theorem le_addU (p a b) : a.toRat + b.toRat ≤ (addU p a b).toRat := by
  unfold addU; simpa using le_ru p (a.add b)
theorem subD_le (p a b) : (subD p a b).toRat ≤ a.toRat - b.toRat := by
  unfold subD; simpa [sub_eq_add_neg] using rd_le p (a.add b.neg)
theorem le_subU (p a b) : a.toRat - b.toRat ≤ (subU p a b).toRat := by
  unfold subU; simpa [sub_eq_add_neg] using le_ru p (a.add b.neg)
theorem mulD_le (p a b) : (mulD p a b).toRat ≤ a.toRat * b.toRat := by
  unfold mulD; simpa using rd_le p (a.mul b)
theorem le_mulU (p a b) : a.toRat * b.toRat ≤ (mulU p a b).toRat := by
  unfold mulU; simpa using le_ru p (a.mul b)

/-! ### Division -/

/-- Bit length of `|m|`. -/
def bits (m : Int) : Nat := Vendor.Dyadic.bitLength m

/-- Extra scaling for a quotient with about `p+2` significant bits. -/
def divShift (p : Nat) (a b : Dy) : Nat := (p + 2 + bits b.mantissa) - bits a.mantissa

/-- Lower bound of `a / b` (junk `0` if `b = 0`). -/
def divD (p : Nat) (a b : Dy) : Dy :=
  if b.mantissa = 0 then zero else
  let s : Int := if b.mantissa < 0 then -1 else 1
  let k := divShift p a b
  rd p ⟨(s * a.mantissa * 2 ^ k) / (s * b.mantissa), a.exponent - b.exponent - k⟩

/-- Upper bound of `a / b` (junk `0` if `b = 0`). -/
def divU (p : Nat) (a b : Dy) : Dy :=
  if b.mantissa = 0 then zero else
  let s : Int := if b.mantissa < 0 then -1 else 1
  let k := divShift p a b
  ru p ⟨-((-(s * a.mantissa * 2 ^ k)) / (s * b.mantissa)), a.exponent - b.exponent - k⟩

/-- `a / b` as rationals in terms of mantissas. -/
private theorem div_eq_aux (a b : Dy) (s : Int) (hs : s = 1 ∨ s = -1) (k : Nat)
    (hb : b.mantissa ≠ 0) :
    a.toRat / b.toRat =
      ((s * a.mantissa * 2 ^ k : Int) : ℚ) / ((s * b.mantissa : Int) : ℚ) *
        (2 : ℚ) ^ (a.exponent - b.exponent - k) := by
  rw [toRat_eq a, toRat_eq b]
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hb' : (b.mantissa : ℚ) ≠ 0 := by exact_mod_cast hb
  have hs' : (s : ℚ) ≠ 0 := by rcases hs with h | h <;> simp [h]
  push_cast
  rw [zpow_sub₀ h2, zpow_sub₀ h2, zpow_natCast]
  field_simp

private theorem ediv_le_div (N D : Int) (hD : 0 < D) : ((N / D : Int) : ℚ) ≤ (N : ℚ) / D := by
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  rw [le_div_iff₀ hD']
  have := Int.ediv_mul_le N (ne_of_gt hD)
  exact_mod_cast this

theorem divD_le (p : Nat) (a b : Dy) (hb : b.toRat ≠ 0) :
    (divD p a b).toRat ≤ a.toRat / b.toRat := by
  have hbm : b.mantissa ≠ 0 := fun h => hb ((toRat_eq_zero_iff b).2 h)
  unfold divD
  simp only [hbm, ↓reduceIte]
  set s : Int := if b.mantissa < 0 then -1 else 1 with hs_def
  have hs : s = 1 ∨ s = -1 := by rw [hs_def]; split <;> simp
  have hsb : 0 < s * b.mantissa := by
    rw [hs_def]; split
    · rename_i h; linarith
    · rename_i h; push Not at h; simp only [one_mul]; omega
  refine le_trans (rd_le _ _) ?_
  rw [div_eq_aux a b s hs (divShift p a b) hbm, toRat_mk]
  apply mul_le_mul_of_nonneg_right _ (le_of_lt (two_zpow_pos _))
  exact ediv_le_div _ _ hsb

theorem le_divU (p : Nat) (a b : Dy) (hb : b.toRat ≠ 0) :
    a.toRat / b.toRat ≤ (divU p a b).toRat := by
  have hbm : b.mantissa ≠ 0 := fun h => hb ((toRat_eq_zero_iff b).2 h)
  unfold divU
  simp only [hbm, ↓reduceIte]
  set s : Int := if b.mantissa < 0 then -1 else 1 with hs_def
  have hs : s = 1 ∨ s = -1 := by rw [hs_def]; split <;> simp
  have hsb : 0 < s * b.mantissa := by
    rw [hs_def]; split
    · rename_i h; linarith
    · rename_i h; push Not at h; simp only [one_mul]; omega
  refine le_trans ?_ (le_ru _ _)
  rw [div_eq_aux a b s hs (divShift p a b) hbm, toRat_mk]
  apply mul_le_mul_of_nonneg_right _ (le_of_lt (two_zpow_pos _))
  have h := ediv_le_div (-(s * a.mantissa * 2 ^ divShift p a b)) (s * b.mantissa) hsb
  push_cast at h ⊢
  have : ((s * a.mantissa * 2 ^ divShift p a b : Int) : ℚ) / ((s * b.mantissa : Int) : ℚ) ≤
      -(((-(s * a.mantissa * 2 ^ divShift p a b)) / (s * b.mantissa) : Int) : ℚ) := by
    push_cast
    rw [neg_div] at h
    linarith
  push_cast at this
  exact this

/-! ### Rationals -/

/-- Lower dyadic bound of a rational. -/
def ofRatD (p : Nat) (q : ℚ) : Dy := divD p (ofInt q.num) (ofNat q.den)
/-- Upper dyadic bound of a rational. -/
def ofRatU (p : Nat) (q : ℚ) : Dy := divU p (ofInt q.num) (ofNat q.den)

theorem ofRatD_le (p : Nat) (q : ℚ) : (ofRatD p q).toRat ≤ q := by
  have h := divD_le p (ofInt q.num) (ofNat q.den) (by simp [q.den_nz])
  unfold ofRatD; simpa [Rat.num_div_den] using h

theorem le_ofRatU (p : Nat) (q : ℚ) : q ≤ (ofRatU p q).toRat := by
  have h := le_divU p (ofInt q.num) (ofNat q.den) (by simp [q.den_nz])
  unfold ofRatU; simpa [Rat.num_div_den] using h

/-! ### Square roots -/

/-- Extra even scaling for a square root with about `p+1` significant bits. -/
def sqrtShift (p : Nat) (a : Dy) : Nat :=
  let j0 : Nat := (2 * p + 2) - bits a.mantissa
  j0 + ((a.exponent - j0) % 2).toNat

/-- Integer square root of the scaled mantissa. -/
def sqrtCore (p : Nat) (a : Dy) : Nat :=
  Nat.sqrt (a.mantissa.toNat * 2 ^ sqrtShift p a)

/-- Lower bound of `√a` (`0` if `a ≤ 0`). -/
def sqrtD (p : Nat) (a : Dy) : Dy :=
  if a.mantissa ≤ 0 then zero else
  rd p ⟨sqrtCore p a, (a.exponent - sqrtShift p a) / 2⟩

/-- Upper bound of `√a` (`0` if `a ≤ 0`). -/
def sqrtU (p : Nat) (a : Dy) : Dy :=
  if a.mantissa ≤ 0 then zero else
  ru p ⟨sqrtCore p a + 1, (a.exponent - sqrtShift p a) / 2⟩

private theorem sqrtShift_even (p : Nat) (a : Dy) :
    2 * ((a.exponent - sqrtShift p a) / 2) = a.exponent - sqrtShift p a := by
  unfold sqrtShift
  simp only
  set j0 : Nat := (2 * p + 2) - bits a.mantissa
  have hr : 0 ≤ (a.exponent - j0) % 2 := Int.emod_nonneg _ (by norm_num)
  have hr2 : (a.exponent - j0) % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
  have hd : (2 : Int) ∣ a.exponent - ((j0 + ((a.exponent - j0) % 2).toNat : Nat) : Int) := by
    push_cast
    rw [Int.toNat_of_nonneg hr]
    omega
  exact Int.mul_ediv_cancel' hd

/-- The scaled value: `a = M * 2^(2f)` with `M` the scaled mantissa. -/
private theorem sqrt_scaled_eq (p : Nat) (a : Dy) (ha : 0 < a.mantissa) :
    (a.toRat : ℝ) =
      ((a.mantissa.toNat * 2 ^ sqrtShift p a : Nat) : ℝ) *
        ((2 : ℝ) ^ ((a.exponent - sqrtShift p a) / 2)) ^ 2 := by
  have hm : ((a.mantissa.toNat : ℕ) : ℝ) = (a.mantissa : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_of_lt ha)
  rw [toRat_eq]
  push_cast
  rw [hm, ← zpow_natCast ((2:ℝ) ^ ((a.exponent - ↑(sqrtShift p a)) / 2)) 2, ← zpow_mul]
  rw [show ((a.exponent - ↑(sqrtShift p a)) / 2) * ((2 : ℕ) : ℤ) =
      a.exponent - sqrtShift p a by
    have := sqrtShift_even p a; push_cast; linarith]
  rw [zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0), zpow_natCast]
  field_simp

theorem sqrtD_le (p : Nat) (a : Dy) : ((sqrtD p a).toRat : ℝ) ≤ Real.sqrt (a.toRat : ℝ) := by
  unfold sqrtD
  split
  · simp [Real.sqrt_nonneg]
  · rename_i ha; push Not at ha
    refine le_trans (Rat.cast_le.2 (rd_le p _)) ?_
    rw [sqrt_scaled_eq p a ha, toRat_mk]
    set M := a.mantissa.toNat * 2 ^ sqrtShift p a
    set f : ℤ := (a.exponent - ↑(sqrtShift p a)) / 2
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ f := le_of_lt (zpow_pos (by norm_num) f)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hpos]
    push_cast
    apply mul_le_mul_of_nonneg_right _ hpos
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have := Nat.sqrt_le' M
    unfold sqrtCore
    exact_mod_cast this

theorem le_sqrtU (p : Nat) (a : Dy) (ha : 0 ≤ a.toRat) :
    Real.sqrt (a.toRat : ℝ) ≤ ((sqrtU p a).toRat : ℝ) := by
  unfold sqrtU
  split
  · rename_i hm
    have : a.toRat = 0 := le_antisymm (by
      have := (toRat_nonneg_iff a).1 ha
      rw [toRat_eq]; have hm0 : a.mantissa = 0 := le_antisymm hm this
      simp [hm0]) ha
    simp [this]
  · rename_i ha'; push Not at ha'
    refine le_trans ?_ (Rat.cast_le.2 (le_ru p _))
    rw [sqrt_scaled_eq p a ha', toRat_mk]
    set M := a.mantissa.toNat * 2 ^ sqrtShift p a
    set f : ℤ := (a.exponent - ↑(sqrtShift p a)) / 2
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ f := le_of_lt (zpow_pos (by norm_num) f)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hpos]
    push_cast
    apply mul_le_mul_of_nonneg_right _ hpos
    rw [Real.sqrt_le_left (by positivity)]
    have := Nat.lt_succ_sqrt' M
    unfold sqrtCore
    have h' : (M : ℝ) < ((Nat.sqrt M + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast (by nlinarith [this])
    push_cast at h'
    linarith

end Dy

end Lynth.Interval
