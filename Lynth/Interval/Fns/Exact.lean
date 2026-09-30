import Lynth.Interval.Reify.ExactAttr
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Combinatorics.Enumerative.Bell

/-!
# Exact evaluation lemmas (`@[lynth_exact]`)

Closed combinatorial / polynomial terms (Chebyshev, Bernoulli, Bell,
Pochhammer, binomials, factorials) are rewritten to rationals by
`norm_num [lynth_exact]` inside the reifier.  To support a new exactly
computable function, tag recursion lemmas that only fire on numerals.
-/

namespace Lynth.Interval.Exact

open Polynomial

theorem cheb_T_ofNat (R : Type*) [CommRing R] (n : ℕ) [n.AtLeastTwo] :
    Chebyshev.T R (ofNat(n) : ℤ) =
      2 * X * Chebyshev.T R ((ofNat(n) : ℤ) - 1) - Chebyshev.T R ((ofNat(n) : ℤ) - 2) := by
  have := Chebyshev.T_add_two R ((ofNat(n) : ℤ) - 2)
  rw [show (ofNat(n) : ℤ) - 2 + 2 = ofNat(n) by ring,
    show (ofNat(n) : ℤ) - 2 + 1 = ofNat(n) - 1 by ring] at this
  exact this

theorem cheb_U_ofNat (R : Type*) [CommRing R] (n : ℕ) [n.AtLeastTwo] :
    Chebyshev.U R (ofNat(n) : ℤ) =
      2 * X * Chebyshev.U R ((ofNat(n) : ℤ) - 1) - Chebyshev.U R ((ofNat(n) : ℤ) - 2) := by
  have := Chebyshev.U_add_two R ((ofNat(n) : ℤ) - 2)
  rw [show (ofNat(n) : ℤ) - 2 + 2 = ofNat(n) by ring,
    show (ofNat(n) : ℤ) - 2 + 1 = ofNat(n) - 1 by ring] at this
  exact this

theorem bell_succ_range (n : ℕ) :
    Nat.bell (n + 1) = ∑ i ∈ Finset.range (n + 1), n.choose i * Nat.bell (n - i) := by
  rw [Nat.bell_succ]; congr 1; ext i; simp

theorem bernoulli'_succ_def (n : ℕ) :
    bernoulli' (n + 1) =
      1 - ∑ k ∈ Finset.range (n + 1), ((n + 1).choose k : ℚ) / (((n + 1 : ℕ) : ℚ) - k + 1) * bernoulli' k :=
  bernoulli'_def (n + 1)

attribute [lynth_exact] cheb_T_ofNat cheb_U_ofNat Chebyshev.T_zero Chebyshev.T_one
  Chebyshev.U_zero Chebyshev.U_one
  bell_succ_range Nat.bell_zero
  bernoulli'_succ_def bernoulli'_zero bernoulli_eq_bernoulli'_of_ne_one _root_.bernoulli_one
  Polynomial.bernoulli_def
  ascPochhammer_zero ascPochhammer_succ_eval
  Nat.choose_succ_succ Nat.choose_zero_right Nat.factorial_succ Nat.factorial_zero
  Finset.sum_range_succ Finset.sum_range_zero Finset.prod_range_succ Finset.prod_range_zero

end Lynth.Interval.Exact
