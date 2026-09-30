import Mathlib

/-!
# `Odd` — ten equivalent definitions

Companion to `Even.lean`.  `Odd : α → Prop` is generic in the same way; there is
no `Nat.Odd` constant, use `Odd` unqualified.

Where `Even.lean` expresses evenness in its own terms, several of these express
oddness *in terms of `Even`* (`even_iff_odd_iff_even_succ`,
`even_iff_odd_iff_not_even`, `even_iff_ne_two_mul`) — the parity predicates are
determined by each other, which is itself part of what makes them useful as a
corpus.
-/

namespace Equiv.Odd

variable (n : ℕ)

/-- 1. As `2k+1`. -/
theorem odd_iff_two_mul_add_one (n : ℕ) : Odd n ↔ ∃ k, n = 2 * k + 1 := by
  constructor
  · rintro ⟨k, h⟩; exact ⟨k, by omega⟩
  · rintro ⟨k, rfl⟩; exact ⟨k, by omega⟩

/-- 2. As a sum of two equal halves plus one. -/
theorem odd_iff_add_add_add_one (n : ℕ) : Odd n ↔ ∃ k, n = k + k + 1 := by
  constructor
  · rintro ⟨k, h⟩; exact ⟨k, by omega⟩
  · rintro ⟨k, h⟩; exact ⟨k, by omega⟩

/-- 3. As a unit remainder. -/
theorem odd_iff_mod_eq_one (n : ℕ) : Odd n ↔ n % 2 = 1 := Nat.odd_iff

/-- 4. As evenness of the successor. -/
theorem odd_iff_even_succ (n : ℕ) : Odd n ↔ Even (n + 1) := by
  constructor
  · rintro ⟨k, h⟩; exact ⟨k + 1, by omega⟩
  · rintro ⟨k, h⟩; exact ⟨k - 1, by omega⟩

/-- 5. As the complement of evenness. -/
theorem odd_iff_not_even (n : ℕ) : Odd n ↔ ¬ Even n := by
  constructor
  · rintro ⟨k, hk⟩ ⟨r, hr⟩; omega
  · intro h
    rcases Nat.even_or_odd n with he | ho
    · exact absurd he h
    · exact ho

/-- 6. As "removing the remainder changes the number". -/
theorem odd_iff_sub_mod_ne (n : ℕ) : Odd n ↔ n - n % 2 ≠ n := by
  have h2 := Nat.mod_lt n (y := 2) (by omega)
  rw [Nat.odd_iff]
  constructor
  · intro hn; omega
  · intro hne; omega

/-- 7. As membership in the set of `2k+1`. -/
theorem odd_iff_mem_range_two_mul_add_one (n : ℕ) :
    Odd n ↔ n ∈ Set.range (fun k : ℕ => 2 * k + 1) := by
  simp [Odd]

/-- 8. As parity after lifting to the integers. -/
theorem odd_iff_int (n : ℕ) : Odd n ↔ Odd (n : ℤ) := by
  constructor
  · rintro ⟨r, h⟩; exact ⟨r, by exact_mod_cast h⟩
  · rintro ⟨k, hk⟩
    have hw : 0 ≤ k := by
      have hn : (0:ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
      have h2 : 2 * k + 1 = (n:ℤ) := by omega
      linarith
    have hw' : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hw
    refine ⟨k.toNat, ?_⟩
    omega

/-- 9. As "not of the form `2k`". -/
theorem odd_iff_ne_two_mul (n : ℕ) : Odd n ↔ ∀ k : ℕ, n ≠ 2 * k := by
  constructor
  · rintro ⟨k, hk⟩ j hj; omega
  · intro h
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨j, hj⟩ := he
      exact (h j (by omega)).elim
    · exact ho

/-- 10. As "halving loses a unit". -/
theorem odd_iff_div_mul_ne (n : ℕ) : Odd n ↔ n / 2 * 2 ≠ n := by
  have h := Nat.div_add_mod n 2
  rw [Nat.odd_iff]
  constructor
  · intro hn; omega
  · intro hne; omega

end Equiv.Odd
