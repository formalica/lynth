import Mathlib

/-!
# `Even` — ten equivalent definitions

`Even : α → Prop` is the generic parity predicate (Mathlib routes `ℕ`, `ℤ`, `ℝ`
through the same class; note there is **no** `Nat.Even` / `Nat.Odd` constant —
use `Even` / `Odd` unqualified).

Each theorem below is a *definition-level* equivalence: the same predicate
presented in ten different shapes (existential factorization, modular
arithmetic, division, set image, integer lift, and complements).  All ten are
proved, not asserted.
-/

namespace Equiv.Even

variable (n : ℕ)

/-- 1. As the image of doubling. -/
theorem even_iff_two_mul (n : ℕ) : Even n ↔ ∃ k, n = 2 * k := by
  constructor
  · rintro ⟨r, rfl⟩; exact ⟨r, by omega⟩
  · rintro ⟨k, rfl⟩; exact ⟨k, by omega⟩

/-- 2. As a sum of two equal halves.  This *is* the definition of `Even` on a
`Semigroup`, so the equivalence is `Iff.rfl`. -/
theorem even_iff_add_self (n : ℕ) : Even n ↔ ∃ k, n = k + k := Iff.rfl

/-- 3. As a vanishing remainder. -/
theorem even_iff_mod_eq_zero (n : ℕ) : Even n ↔ n % 2 = 0 := Nat.even_iff

/-- 4. As a division that loses nothing. -/
theorem even_iff_div_mul (n : ℕ) : Even n ↔ n / 2 * 2 = n := by
  have h := Nat.div_add_mod n 2
  rw [Nat.even_iff]
  constructor
  · intro hn; omega
  · intro he; omega

/-- 5. As "subtracting the remainder is a no-op". -/
theorem even_iff_sub_mod (n : ℕ) : Even n ↔ n - n % 2 = n := by
  have h2 := Nat.mod_lt n (y := 2) (by omega)
  rw [Nat.even_iff]
  constructor
  · intro hn; omega
  · intro he; omega

/-- 6. As the complement of "the remainder is 1". -/
theorem even_iff_mod_ne_one (n : ℕ) : Even n ↔ n % 2 ≠ 1 := by
  have h2 := Nat.mod_lt n (y := 2) (by omega)
  rw [Nat.even_iff]
  constructor
  · intro _; omega
  · intro h; omega

/-- 7. As membership in the set of doubles. -/
theorem even_iff_mem_range_two_mul (n : ℕ) :
    Even n ↔ n ∈ Set.range (fun k : ℕ => 2 * k) := by
  simp [Even]

/-- 8. As parity after lifting to the integers. -/
theorem even_iff_int (n : ℕ) : Even n ↔ Even (n : ℤ) := by
  constructor
  · rintro ⟨r, h⟩; exact ⟨r, by exact_mod_cast h⟩
  · rintro ⟨k, hk⟩
    have hw : 0 ≤ k := by
      have hn : (0:ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
      have h2 : 2 * k = (n:ℤ) := by omega
      linarith
    have hw' : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hw
    refine ⟨k.toNat, ?_⟩
    omega

/-- 9. As the complement of oddness. -/
theorem even_iff_not_odd (n : ℕ) : Even n ↔ ¬ Odd n := by
  constructor
  · rintro ⟨r, hr⟩ ⟨k, hk⟩; omega
  · intro h
    rcases Nat.even_or_odd n with he | ho
    · exact he
    · exact absurd ho h

/-- 10. As "not of the form 2k+1". -/
theorem even_iff_ne_two_succ (n : ℕ) : Even n ↔ ∀ k : ℕ, n ≠ 2 * k + 1 := by
  constructor
  · rintro ⟨r, hr⟩ k hk; omega
  · intro h
    rcases Nat.even_or_odd n with he | ho
    · exact he
    · obtain ⟨k, hk⟩ := ho
      exact (h k hk).elim

end Equiv.Even
