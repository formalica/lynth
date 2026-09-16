-- Soundness of Farkas combinations (the mathematics behind
-- `Fourier.checkCert`): nonnegative weights combining satisfiable
-- `≤`-rows to `0 < 0` is impossible. This is the reconstruction core
-- for arithmetic refutations; the remaining step (reflecting runtime
-- `LeC` systems into this finite form) is tracked in `docs/Z3-NOTES.md`.
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Tactic.Linarith

namespace Lynth.Arith.FarkasSound

open Finset BigOperators

/-- Farkas combination soundness: if every row holds under `v`, no
nonnegative weighting can combine them to a positive constant with a
vanishing left-hand side. -/
theorem farkas_sound {n m : Nat} (A : Fin m → Fin n → Rat)
    (b : Fin m → Rat) (w : Fin m → Rat) (v : Fin n → Rat)
    (hw : ∀ i, 0 ≤ w i)
    (hsys : ∀ i, ∑ j, A i j * v j + b i ≤ 0)
    (hcomb : ∀ j, ∑ i, w i * A i j = 0)
    (hpos : 0 < ∑ i, w i * b i) : False := by
  -- each weighted row is nonpositive
  have hrow : ∀ i ∈ (univ : Finset (Fin m)),
      w i * (∑ j, A i j * v j + b i) ≤ 0 := by
    intro i _
    have h := mul_le_mul_of_nonneg_left (hsys i) (hw i)
    rwa [mul_zero] at h
  have hsum : ∑ i, w i * (∑ j, A i j * v j + b i) ≤ 0 := by
    have h := sum_le_sum hrow
    rwa [sum_const_zero] at h
  -- per-row expansion
  have h1 : ∀ i, w i * (∑ j, A i j * v j + b i)
      = (∑ j, w i * (A i j * v j)) + w i * b i := by
    intro i
    rw [mul_add, mul_sum]
  -- per-column factorisation
  have hper : ∀ j, (∑ i, w i * A i j) * v j
      = ∑ i, w i * (A i j * v j) := by
    intro j
    rw [sum_mul]
    apply sum_congr rfl
    intro i _
    exact mul_assoc _ _ _
  -- recombine and swap sums
  have hexpand : ∑ i, w i * (∑ j, A i j * v j + b i)
      = ∑ j, (∑ i, w i * A i j) * v j + ∑ i, w i * b i := by
    have e1 : (∑ i, w i * (∑ j, A i j * v j + b i))
        = ∑ i, ((∑ j, w i * (A i j * v j)) + w i * b i) :=
      sum_congr rfl fun i _ => h1 i
    have e2 : (∑ i, ((∑ j, w i * (A i j * v j)) + w i * b i))
        = (∑ i, ∑ j, w i * (A i j * v j)) + ∑ i, w i * b i :=
      sum_add_distrib
    have e3 : (∑ i, ∑ j, w i * (A i j * v j))
        = ∑ j, ∑ i, w i * (A i j * v j) := sum_comm
    have e4 : (∑ j, ∑ i, w i * (A i j * v j))
        = ∑ j, (∑ i, w i * A i j) * v j :=
      sum_congr rfl fun j _ => (hper j).symm
    rw [e1, e2, e3, e4]
  -- the left-hand side vanishes by `hcomb`
  have hzero : ∑ j, (∑ i, w i * A i j) * v j = 0 :=
    sum_eq_zero fun j _ => by rw [hcomb j, zero_mul]
  have hcon : ∑ i, w i * b i ≤ 0 := by
    have h := hexpand ▸ hsum
    rwa [hzero, zero_add] at h
  exact absurd (lt_of_lt_of_le hpos hcon) (lt_irrefl _)

end Lynth.Arith.FarkasSound
