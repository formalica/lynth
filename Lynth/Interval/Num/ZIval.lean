import Lynth.Interval.Num.Ival
import Lynth.Interval.Num.NIval

/-!
# Integer intervals

`ZIval` encloses integers: `lo ≤ z ≤ hi` (`none` means unbounded).
Used for `ℤ`-typed subexpressions (custom-function integer arguments).
Mirrors `NIval`, except the lower bound is also optional since integers
are unbounded below.
-/

namespace Lynth.Interval

structure ZIval where
  lo : Option Int
  hi : Option Int
deriving Repr, Inhabited, DecidableEq

namespace ZIval

def Mem (I : ZIval) (z : ℤ) : Prop :=
  (∀ l, I.lo = some l → l ≤ z) ∧ ∀ h, I.hi = some h → z ≤ h

instance : Membership ℤ ZIval := ⟨ZIval.Mem⟩

@[simp] theorem mem_mk {z : ℤ} {lo hi : Option Int} :
    z ∈ (⟨lo, hi⟩ : ZIval) ↔ (∀ l, lo = some l → l ≤ z) ∧ ∀ h, hi = some h → z ≤ h :=
  Iff.rfl

def top : ZIval := ⟨none, none⟩
theorem mem_top (z : ℤ) : z ∈ top := by simp [top]

def pt (z : Int) : ZIval := ⟨some z, some z⟩
theorem mem_pt (z : ℤ) : z ∈ pt z := by simp [pt]

/-- `some z` if the interval is the single point `z` -/
def isPoint (I : ZIval) : Option Int :=
  match I.lo, I.hi with
  | some l, some h => if l = h then some h else none
  | _, _ => none

theorem eq_of_isPoint {I : ZIval} {z : ℤ} {m : Int}
    (hz : z ∈ I) (h : I.isPoint = some m) : z = m := by
  unfold isPoint at h
  cases hl : I.lo with
  | none => simp [hl] at h
  | some l =>
    cases hh : I.hi with
    | none => simp [hl, hh] at h
    | some k =>
      simp only [hl, hh] at h
      split at h
      · rename_i heq
        cases h
        have h1 := hz.1 _ hl
        have h2 := hz.2 _ hh
        omega
      · simp at h

def olift2 (f : Int → Int → Int) : Option Int → Option Int → Option Int
  | some a, some b => some (f a b)
  | _, _ => none

def add (I J : ZIval) : ZIval := ⟨olift2 (· + ·) I.lo J.lo, olift2 (· + ·) I.hi J.hi⟩
def neg (I : ZIval) : ZIval := ⟨I.hi.map (-·), I.lo.map (-·)⟩
def sub (I J : ZIval) : ZIval := add I (neg J)

/-- exact multiplication on bounded intervals; `top` otherwise.
Unbounded-times-anything falls back to `top`: sound, just less precise.
(Refine if profiling ever demands it.) -/
def mul (I J : ZIval) : ZIval :=
  match I.lo, I.hi, J.lo, J.hi with
  | some a, some b, some c, some d =>
    ⟨some (min (min (a * c) (a * d)) (min (b * c) (b * d))),
     some (max (max (a * c) (a * d)) (max (b * c) (b * d)))⟩
  | _, _, _, _ => top

/-- `(n : ℤ)` literal -/
def ofNat (n : Nat) : ZIval := pt n

theorem mem_add {x y : ℤ} {I J : ZIval} (hx : x ∈ I) (hy : y ∈ J) : x + y ∈ add I J := by
  refine ⟨?_, ?_⟩
  · intro l hl
    cases h1 : I.lo <;> cases h2 : J.lo <;> simp [add, olift2, h1, h2] at hl
    subst hl
    have := hx.1 _ h1; have := hy.1 _ h2; omega
  · intro h hh
    cases h1 : I.hi <;> cases h2 : J.hi <;> simp [add, olift2, h1, h2] at hh
    subst hh
    have := hx.2 _ h1; have := hy.2 _ h2; omega

theorem mem_neg {x : ℤ} {I : ZIval} (hx : x ∈ I) : -x ∈ neg I := by
  refine ⟨?_, ?_⟩
  · intro l hl
    cases h1 : I.hi <;> simp [neg, h1] at hl
    subst hl
    have := hx.2 _ h1; omega
  · intro h hh
    cases h1 : I.lo <;> simp [neg, h1] at hh
    subst hh
    have := hx.1 _ h1; omega

theorem mem_sub {x y : ℤ} {I J : ZIval} (hx : x ∈ I) (hy : y ∈ J) : x - y ∈ sub I J := by
  rw [sub_eq_add_neg]; exact mem_add hx (mem_neg hy)

/-- corner bound: the minimum of the four corner products is below `x * y` -/
theorem corner_min_le {a b c d x y : ℤ}
    (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y) (hyd : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  by_cases hy : 0 ≤ y
  · have h1 : a * y ≤ x * y := by
      have hnn := mul_nonneg (sub_nonneg.mpr hax) hy
      linarith
    by_cases ha : 0 ≤ a
    · have h2 : a * c ≤ a * y := by
        have hnn := mul_nonpos_of_nonneg_of_nonpos ha (sub_nonpos.mpr hcy)
        linarith
      exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans h2 h1))
    · have ha' : a < 0 := lt_of_not_ge ha
      have h2 : a * d ≤ a * y := by
        have hnn := mul_nonpos_of_nonpos_of_nonneg (le_of_lt ha') (sub_nonneg.mpr hyd)
        linarith
      exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (le_trans h2 h1))
  · have hy' : y < 0 := lt_of_not_ge hy
    have h1 : b * y ≤ x * y := by
      have hnn := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxb) (le_of_lt hy')
      linarith
    by_cases hb : b ≤ 0
    · have h2 : b * d ≤ b * y := by
        have hnn := mul_nonneg_of_nonpos_of_nonpos hb (sub_nonpos.mpr hyd)
        linarith
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans h2 h1))
    · have hb' : 0 < b := lt_of_not_ge hb
      have h2 : b * c ≤ b * y := by
        have hnn := mul_nonneg (le_of_lt hb') (sub_nonneg.mpr hcy)
        linarith
      exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (le_trans h2 h1))

/-- dual corner bound via negation -/
theorem corner_le_max {a b c d x y : ℤ}
    (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y) (hyd : y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have h2 := corner_min_le (x := -x) (a := -b) (b := -a) (by omega) (by omega) hcy hyd
  have e1 : (-x) * y = -(x * y) := by ring
  have e2 : min (min ((-b) * c) ((-b) * d)) (min ((-a) * c) ((-a) * d))
      = -(max (max (b * c) (b * d)) (max (a * c) (a * d))) := by
    simp only [neg_mul]
    omega
  omega

theorem mem_mul {x y : ℤ} {I J : ZIval} (hx : x ∈ I) (hy : y ∈ J) : x * y ∈ mul I J := by
  cases h1 : I.lo <;> cases h2 : I.hi <;> cases h3 : J.lo <;> cases h4 : J.hi <;>
    simp only [mul, h1, h2, h3, h4]
  all_goals (first
    | exact mem_top _
    | (refine ⟨?_, ?_⟩
       · intro l hl; have hl' := Option.some_inj.mp hl; subst hl'
         exact corner_min_le (hx.1 _ h1) (hx.2 _ h2) (hy.1 _ h3) (hy.2 _ h4)
       · intro h hh; have hh' := Option.some_inj.mp hh; subst hh'
         exact corner_le_max (hx.1 _ h1) (hx.2 _ h2) (hy.1 _ h3) (hy.2 _ h4)))

/-- cast to a real interval (exact on points via dyadics) -/
def toIval (I : ZIval) : Ival :=
  ⟨I.lo.map (fun l => Dy.ofInt l), I.hi.map (fun h => Dy.ofInt h)⟩

theorem mem_toIval {z : ℤ} {I : ZIval} (hz : z ∈ I) : (z : ℝ) ∈ toIval I := by
  refine ⟨?_, ?_⟩
  · intro l hl
    cases h1 : I.lo with
    | none =>
      simp only [toIval, h1, Option.map_none] at hl
      exact nomatch hl
    | some a =>
      simp only [toIval, h1, Option.map_some] at hl
      have hl' := Option.some_inj.mp hl; subst hl'
      simp only [Dy.toReal_def, Dy.toRat_ofInt]
      have hle := hz.1 _ h1
      exact_mod_cast hle
  · intro h hh
    cases h1 : I.hi with
    | none =>
      simp only [toIval, h1, Option.map_none] at hh
      exact nomatch hh
    | some a =>
      simp only [toIval, h1, Option.map_some] at hh
      have hh' := Option.some_inj.mp hh; subst hh'
      simp only [Dy.toReal_def, Dy.toRat_ofInt]
      have hle := hz.2 _ h1
      exact_mod_cast hle

/-- `(n : ℤ)` enclosure from a natural enclosure -/
def ofNatIval (N : NIval) : ZIval := ⟨some N.lo, N.hi.map Int.ofNat⟩

theorem mem_ofNatIval {n : ℕ} {N : NIval} (hn : n ∈ N) : (n : ℤ) ∈ ofNatIval N := by
  refine ⟨?_, ?_⟩
  · intro l hl
    simp only [ofNatIval] at hl
    have hl' := Option.some_inj.mp hl; subst hl'
    have hle := hn.1
    omega
  · intro h hh
    cases h1 : N.hi with
    | none =>
      simp only [ofNatIval, h1, Option.map_none] at hh
      exact nomatch hh
    | some b =>
      simp only [ofNatIval, h1, Option.map_some] at hh
      have hh' := Option.some_inj.mp hh; subst hh'
      simp only [Int.ofNat_eq_natCast]
      have hle := hn.2 _ h1
      omega

end ZIval

end Lynth.Interval
