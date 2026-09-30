import Lynth.Interval.Num.Ival

/-!
# Natural-number intervals

`NIval` encloses natural numbers: `lo ≤ n ≤ hi` (`hi = none` means unbounded).
Used for `ℕ`-typed subexpressions (sum indices, factorials, Fibonacci numbers).
-/

namespace Lynth.Interval

structure NIval where
  lo : Nat
  hi : Option Nat
deriving Repr, Inhabited, DecidableEq

namespace NIval

def Mem (I : NIval) (n : ℕ) : Prop := I.lo ≤ n ∧ ∀ h, I.hi = some h → n ≤ h

instance : Membership ℕ NIval := ⟨NIval.Mem⟩

@[simp] theorem mem_mk {n lo : ℕ} {hi : Option ℕ} :
    n ∈ (⟨lo, hi⟩ : NIval) ↔ lo ≤ n ∧ ∀ h, hi = some h → n ≤ h := Iff.rfl

def top : NIval := ⟨0, none⟩
theorem mem_top (n : ℕ) : n ∈ top := by simp [top]

def pt (n : Nat) : NIval := ⟨n, some n⟩
theorem mem_pt (n : ℕ) : n ∈ pt n := by simp [pt]

/-- `some n` if the interval is the single point `n` -/
def isPoint (I : NIval) : Option Nat :=
  match I.hi with
  | some h => if I.lo = h then some h else none
  | none => none

theorem eq_of_isPoint {I : NIval} {n m : ℕ} (hn : n ∈ I) (h : I.isPoint = some m) : n = m := by
  unfold isPoint at h
  cases hh : I.hi with
  | none => simp [hh] at h
  | some k =>
    simp only [hh] at h
    split at h
    · rename_i hlo
      cases h
      have := hn.2 _ hh
      have := hn.1
      omega
    · simp at h

def ohi2 (f : Nat → Nat → Nat) : Option Nat → Option Nat → Option Nat
  | some a, some b => some (f a b)
  | _, _ => none

def add (I J : NIval) : NIval := ⟨I.lo + J.lo, ohi2 (· + ·) I.hi J.hi⟩
def mul (I J : NIval) : NIval := ⟨I.lo * J.lo, ohi2 (· * ·) I.hi J.hi⟩
/-- truncated subtraction `n - m` -/
def sub (I J : NIval) : NIval :=
  ⟨match J.hi with | some b => I.lo - b | none => 0, I.hi.map (· - J.lo)⟩

theorem mem_add {n m : ℕ} {I J : NIval} (hn : n ∈ I) (hm : m ∈ J) : n + m ∈ add I J := by
  refine ⟨Nat.add_le_add hn.1 hm.1, ?_⟩
  intro h hh
  cases h1 : I.hi <;> cases h2 : J.hi <;> simp [add, ohi2, h1, h2] at hh
  subst hh
  exact Nat.add_le_add (hn.2 _ h1) (hm.2 _ h2)

theorem mem_mul {n m : ℕ} {I J : NIval} (hn : n ∈ I) (hm : m ∈ J) : n * m ∈ mul I J := by
  refine ⟨Nat.mul_le_mul hn.1 hm.1, ?_⟩
  intro h hh
  cases h1 : I.hi <;> cases h2 : J.hi <;> simp [mul, ohi2, h1, h2] at hh
  subst hh
  exact Nat.mul_le_mul (hn.2 _ h1) (hm.2 _ h2)

theorem mem_sub {n m : ℕ} {I J : NIval} (hn : n ∈ I) (hm : m ∈ J) : n - m ∈ sub I J := by
  constructor
  · show (match J.hi with | some b => I.lo - b | none => 0) ≤ n - m
    cases h2 : J.hi with
    | none => simp
    | some b => have := hm.2 _ h2; have := hn.1; simp only; omega
  · intro h hh
    cases h1 : I.hi <;> simp [sub, h1] at hh
    subst hh
    have := hn.2 _ h1; have := hm.1; omega

/-- lift of a monotone function -/
def mapMono (f : Nat → Nat) (I : NIval) : NIval := ⟨f I.lo, I.hi.map f⟩

theorem mem_mapMono {f : ℕ → ℕ} (hf : Monotone f) {n : ℕ} {I : NIval} (hn : n ∈ I) :
    f n ∈ mapMono f I := by
  refine ⟨hf hn.1, ?_⟩
  intro h hh
  cases h1 : I.hi <;> simp [mapMono, h1] at hh
  subst hh
  exact hf (hn.2 _ h1)

/-- cast to a real interval (exact) -/
def toIval (I : NIval) : Ival :=
  ⟨some (Dy.ofNat I.lo), I.hi.map Dy.ofNat⟩

theorem mem_toIval {n : ℕ} {I : NIval} (hn : n ∈ I) : (n : ℝ) ∈ toIval I := by
  refine ⟨?_, ?_⟩
  · simp only [toIval, Ival.loLe_some, Dy.toReal_def, Dy.toRat_ofNat, Rat.cast_natCast]
    exact_mod_cast hn.1
  · intro h hh
    cases h1 : I.hi <;> simp [toIval, h1] at hh
    subst hh
    simp only [Dy.toReal_def, Dy.toRat_ofNat, Rat.cast_natCast]
    exact_mod_cast hn.2 _ h1

end NIval

end Lynth.Interval
