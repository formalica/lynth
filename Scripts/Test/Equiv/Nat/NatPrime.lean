import Mathlib

/-!
# `Nat.Prime` — ten equivalent definitions

At the pinned Mathlib rev (`v4.34.0`) `Nat.Prime p` is **defined** as
`Irreducible p`:

```
structure Irreducible (p : M) : Prop where
  not_isUnit       : ¬ IsUnit p
  isUnit_or_isUnit : ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
```

so #1 below is the definition itself, and there is no `Nat.prime_iff` bridge to
a separate `Prime` class.  Everything else is a recasting of the same predicate.

## Proof structure

Everything is organised around the **divisor form**

```
DivisorForm n  =  n > 1 ∧ ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n
```

Statements 1 and 2 tie it (and the factorisation form) to `Nat.Prime` directly,
using `Irreducible.not_isUnit` and `Irreducible.isUnit_or_isUnit`.
Statements 3–10 relate the divisor form to the other shapes.  A small set of
arithmetic lemmas (`dvd_pos`, `dvd_le_self`, `dvd_lt_of_ne`, `dvd_gcd_of_dvd`,
`eq_one_of_mul_eq`, `eq_n_of_mul_eq`) does all the shared lifting work, which is
why each individual statement is only a few lines.
-/

namespace Equiv.NatPrime

variable (n : ℕ)

/-! ## Arithmetic helpers shared by the characterisations -/

/-- `1 < m` rules out the only unit of `ℕ`. -/
theorem notUnit {m : ℕ} (h : 1 < m) : ¬ IsUnit m := by
  intro hu
  have h2 := Nat.isUnit_iff.mp hu
  omega

/-- A divisor of a number `> 1` is nonzero, hence positive. -/
theorem dvd_pos {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) : 0 < d := by
  have hne : d ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha⟩ := hd
    omega
  exact Nat.pos_of_ne_zero hne

/-- `d ∣ n` and `0 < n` give `d ≤ n`. -/
theorem dvd_le_self {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) : d ≤ n := by
  obtain ⟨a, ha⟩ := hd
  rw [Nat.mul_comm] at ha
  rcases Nat.eq_zero_or_pos a with hz | hp
  · rw [hz] at ha; omega
  · have hle : d ≤ a * d := Nat.le_mul_of_pos_left (m := d) (n := a) (by omega)
    omega

/-- `d ∣ n`, `0 < n`, and `d ≠ n` give `d < n`. -/
theorem dvd_lt_of_ne {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) (hne : d ≠ n) : d < n :=
  Nat.lt_of_not_ge (fun h => hne (Nat.le_antisymm (dvd_le_self hn hd) h))

/-- A divisor `d` of `n > 1` that is not `1` is at least `2`. -/
theorem dvd_two_le {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) (hd1 : d ≠ 1) : 2 ≤ d :=
  lt_of_le_of_ne (Nat.succ_le_of_lt (dvd_pos hn hd)) hd1.symm

/-- If `n = d * a` with `2 ≤ d` and `a ≥ 1`, then `a < n`: the cofactor of a
nontrivial factorisation is strictly smaller than the product. -/
theorem cofactor_lt {d a n : ℕ} (hd2 : 2 ≤ d) (ha0 : 1 ≤ a) (ha : n = d * a) : a < n := by
  have h1 : a * 2 ≤ a * d := Nat.mul_le_mul_left a hd2
  rw [Nat.mul_comm] at ha
  have h3 : a < a * 2 := by
    have := Nat.succ_le_of_lt (Nat.zero_lt_of_lt ha0)
    omega
  omega

/-- A common divisor of `m` and `n` divides `m.gcd n`. -/
theorem dvd_gcd_of_dvd {m n : ℕ} (hm : m ∣ m) (hn : m ∣ n) : m ∣ m.gcd n :=
  Nat.dvd_gcd hm hn

/-- Under the divisor form, a product `a * b = n` with `1 < a` forces `b = 1`. -/
theorem eq_one_of_mul_eq {n a b : ℕ} (h1 : 1 < n)
    (h : ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n) (ha : 1 < a) (hab : a * b = n) : b = 1 := by
  rcases h a ⟨b, hab.symm⟩ with hq1 | hq2
  · omega
  · have heq : a * b = a * 1 := hab.trans (hq2.symm.trans (Nat.mul_one a).symm)
    exact Nat.mul_left_cancel (by omega) heq

/-- And then also forces `a = n`. -/
theorem eq_n_of_mul_eq {n a b : ℕ} (h1 : 1 < n)
    (h : ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n) (ha : 1 < a) (hab : a * b = n) : a = n := by
  have h1b := eq_one_of_mul_eq h1 h ha hab
  rw [h1b] at hab
  omega

/-! ## 1 and 2: the two characterisations tied to `Nat.Prime` proper -/

/-- **#2.** The divisor form. -/
theorem dvdForm_iff_prime (n : ℕ) :
    Nat.Prime n ↔ (n > 1 ∧ ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n) := by
  constructor
  · intro hp
    have hl := hp.one_lt
    refine ⟨by omega, fun d hd => ?_⟩
    obtain ⟨a, ha⟩ := hd
    rcases hp.isUnit_or_isUnit (a := d) (b := a) ha with h | h
    · exact Or.inl (Nat.isUnit_iff.mp h)
    · have h3 : a = 1 := Nat.isUnit_iff.mp h
      exact Or.inr (by rw [h3] at ha; omega)
  · rintro ⟨h1, h⟩
    refine ⟨fun hu => ?_, fun a b hab => ?_⟩
    · have h2 := Nat.isUnit_iff.mp hu; omega
    · rcases h a ⟨b, hab⟩ with ha | ha
      · exact Or.inl (by rw [ha]; exact isUnit_one)
      · refine Or.inr ?_
        have heq : a * b = a * 1 := hab.symm.trans (ha.symm.trans (Nat.mul_one a).symm)
        rw [Nat.mul_left_cancel (by rw [ha]; omega) heq]
        exact isUnit_one

/-- **#1.** The factorisation form.  On this Mathlib rev this *is* the
definition; the informative content is the `2 ≤ n` conjunct. -/
theorem prime_iff_factorization (n : ℕ) :
    Nat.Prime n ↔ (2 ≤ n ∧ ∀ a b : ℕ, a * b = n → a = 1 ∨ b = 1) := by
  constructor
  · intro hp
    have hl := hp.one_lt
    refine ⟨by omega, fun a b hab => ?_⟩
    rcases hp.isUnit_or_isUnit (a := a) (b := b) hab.symm with h | h
    · exact Or.inl (Nat.isUnit_iff.mp h)
    · exact Or.inr (Nat.isUnit_iff.mp h)
  · rintro ⟨h1, h⟩
    refine ⟨fun hu => ?_, fun a b hab => ?_⟩
    · have h2 := Nat.isUnit_iff.mp hu; omega
    · rcases h a b hab.symm with ha | hb
      · exact Or.inl (by rw [ha]; exact isUnit_one)
      · exact Or.inr (by rw [hb]; exact isUnit_one)

/-! ## 3–10: the divisor form against every other shape -/

/-- **#3.** Absence of a factorisation into two factors `> 1`. -/
theorem dvdForm_iff_no_factorization (n : ℕ) :
    (n > 1 ∧ ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n) ↔
      (n > 1 ∧ ¬ ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = n) := by
  constructor
  · rintro ⟨h1, h⟩
    refine ⟨h1, fun hx => ?_⟩
    obtain ⟨a, b, ha, hb, hab⟩ := hx
    refine absurd (eq_n_of_mul_eq h1 h ha hab) ?_
    have h1b := eq_one_of_mul_eq h1 h ha hab
    omega
  · rintro ⟨h1, h⟩
    refine ⟨h1, fun d hd => ?_⟩
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    · refine Or.inr ?_
      have hd2 : 2 ≤ d := dvd_two_le (by omega) hd hd1
      obtain ⟨a, ha⟩ := hd
      by_cases ha1 : a = 1
      · rw [ha1, Nat.mul_one] at ha
        exact ha.symm
      · have ha0 : 1 < a := by
          rcases Nat.eq_zero_or_pos a with hz | hp
          · rw [hz] at ha; omega
          · omega
        exact (h ⟨d, a, hd2, ha0, ha.symm⟩).elim

/-- **#4.** Absence of a proper divisor. -/
theorem dvdForm_iff_no_proper_divisor (n : ℕ) :
    (n > 1 ∧ ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n) ↔
      (n > 1 ∧ ∀ m : ℕ, 1 < m → m < n → ¬ m ∣ n) := by
  constructor
  · rintro ⟨h1, h⟩
    refine ⟨h1, fun m hm1 hmn hd => ?_⟩
    rcases h m hd with hq1 | hq2
    · omega
    · omega
  · rintro ⟨h1, h⟩
    refine ⟨h1, fun d hd => ?_⟩
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    · refine Or.inr ?_
      by_contra hdn
      have hd0 : 0 < d := dvd_pos (by omega) hd
      exact h d (by omega) (dvd_lt_of_ne (by omega) hd hdn) hd

/-- **#5.** Non-factorisability with a `≠`, and `2 ≤ n` rather than `n > 1`. -/
theorem dvdForm_iff_no_two_factors (n : ℕ) :
    (n > 1 ∧ ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n) ↔
      (2 ≤ n ∧ ∀ a b : ℕ, 1 < a → 1 < b → a * b ≠ n) := by
  constructor
  · rintro ⟨h1, h⟩
    refine ⟨by omega, fun a b ha hb heq => ?_⟩
    refine absurd (eq_n_of_mul_eq h1 h ha heq) ?_
    have h1b := eq_one_of_mul_eq h1 h ha heq
    omega
  · rintro ⟨h1, h⟩
    have h1' : 1 < n := by omega
    refine ⟨h1', fun d hd => ?_⟩
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    · refine Or.inr ?_
      have hd2 : 2 ≤ d := dvd_two_le (by omega) hd hd1
      obtain ⟨a, ha⟩ := hd
      by_cases ha1 : a = 1
      · rw [ha1, Nat.mul_one] at ha
        exact ha.symm
      · have ha0 : 1 < a := by
          rcases Nat.eq_zero_or_pos a with hz | hp
          · rw [hz] at ha; omega
          · omega
        exact (h d a hd2 ha0 ha.symm).elim

/-- **#6.** Vanishing remainder modulo every proper divisor. -/
theorem dvdForm_iff_mod_ne_zero (n : ℕ) :
    (n > 1 ∧ ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n) ↔
      (n > 1 ∧ ∀ m : ℕ, 1 < m → m < n → n % m ≠ 0) := by
  constructor
  · rintro ⟨h1, h⟩
    refine ⟨h1, fun m hm1 hmn hz => ?_⟩
    have hd : m ∣ n := Nat.dvd_of_mod_eq_zero hz
    rcases h m hd with hq1 | hq2
    · omega
    · omega
  · rintro ⟨h1, h⟩
    refine ⟨h1, fun d hd => ?_⟩
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    · refine Or.inr ?_
      by_contra hdn
      have hd0 : 0 < d := dvd_pos (by omega) hd
      exact h d (by omega) (dvd_lt_of_ne (by omega) hd hdn)
        ((Nat.dvd_iff_mod_eq_zero (m := d) (n := n)).mp hd)

/-- **#7.** Coprimality with every proper divisor. -/
theorem dvdForm_iff_gcd_eq_one (n : ℕ) :
    (n > 1 ∧ ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n) ↔
      (n > 1 ∧ ∀ m : ℕ, 1 < m → m < n → m.gcd n = 1) := by
  constructor
  · rintro ⟨h1, h⟩
    refine ⟨h1, fun m hm1 hmn => ?_⟩
    -- `g = m.gcd n` divides `n`, so it is `1` or `n`; the latter is excluded
    -- because `g ∣ m` would give `n ∣ m` against `0 < m < n`
    have hg : m.gcd n ∣ n := Nat.gcd_dvd_right m n
    rcases h (m.gcd n) hg with hq1 | hq2
    · exact hq1
    · -- `m.gcd n = n` would give `n ∣ m`, contradicting `0 < m < n`
      have hgm : m.gcd n ∣ m := Nat.gcd_dvd_left m n
      rw [hq2] at hgm
      have hle : n ≤ m := dvd_le_self (by omega) hgm
      omega
  · rintro ⟨h1, h⟩
    refine ⟨h1, fun d hd => ?_⟩
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    · refine Or.inr ?_
      by_contra hdn
      have hd0 : 0 < d := dvd_pos (by omega) hd
      have hlt : d < n := dvd_lt_of_ne (by omega) hd hdn
      have hgc : d.gcd n = 1 := h d (by omega) hlt
      have hdvd : d ∣ d.gcd n := dvd_gcd_of_dvd dvd_rfl hd
      rw [hgc] at hdvd
      exact absurd (Nat.dvd_one.mp hdvd) (by omega)

/-- **#8.** The `2`-or-odd split, with the proper-divisor test on the odd branch. -/
theorem dvdForm_iff_two_or_odd (n : ℕ) :
    (n > 1 ∧ ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n) ↔
      (n > 1 ∧ (n = 2 ∨ (Odd n ∧ ∀ m : ℕ, 1 < m → m < n → ¬ m ∣ n))) := by
  constructor
  · rintro ⟨h1, h⟩
    rcases Nat.even_or_odd n with he | ho
    · refine ⟨h1, Or.inl ?_⟩
      have hd2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero (Nat.even_iff.mp he)
      rcases h 2 hd2 with hq1 | hq2
      · omega
      · exact hq2.symm
    · refine ⟨h1, Or.inr ⟨ho, fun m hm1 hmn hd => ?_⟩⟩
      rcases h m hd with hq1 | hq2
      · omega
      · omega
  · rintro ⟨h1, h⟩
    rcases h with hn2 | hrest
    · refine ⟨h1, fun d hd => ?_⟩
      by_cases hd1 : d = 1
      · exact Or.inl hd1
      · refine Or.inr ?_
        by_contra hdn
        rw [hn2] at hd
        have h2 : 2 ≤ d := dvd_two_le (by omega) hd hd1
        have hle : d ≤ 2 := dvd_le_self (by omega) hd
        omega
    · obtain ⟨hodd, hnoproper⟩ := hrest
      refine ⟨h1, fun d hd => ?_⟩
      by_cases hd1 : d = 1
      · exact Or.inl hd1
      · refine Or.inr ?_
        by_contra hdn
        have h2 : 2 ≤ d := dvd_two_le (by omega) hd hd1
        have hlt : d < n := dvd_lt_of_ne (by omega) hd hdn
        exact hnoproper d h2 hlt hd

/-- **#9.** Euclid's lemma: `n` is prime exactly when it divides a product only
via one of the factors. -/
theorem dvdForm_iff_euclid (n : ℕ) :
    (n > 1 ∧ ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n) ↔
      (n > 1 ∧ ∀ a b : ℕ, n ∣ a * b → (n ∣ a ∨ n ∣ b)) := by
  constructor
  · -- the divisor form is equivalent to `Nat.Prime` (#2), and Euclid's lemma
    -- is `Nat.Prime.dvd_mul`
    intro hd
    have hp : Nat.Prime n := (dvdForm_iff_prime n).mpr hd
    refine ⟨hd.1, fun a b hab => ?_⟩
    exact hp.dvd_mul.mp hab
  · rintro ⟨h1, h⟩
    refine ⟨h1, fun d hd => ?_⟩
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    · -- suppose `d` is a nontrivial proper divisor: `n = d * a` with `1 < d`,
      -- `1 ≤ a`, and then `a < n`; Euclid applied to `n ∣ d * a` is contradictory
      refine Or.inr ?_
      by_contra hdn
      have hd2 : 2 ≤ d := dvd_two_le (by omega) hd hd1
      have hlt : d < n := dvd_lt_of_ne (by omega) hd hdn
      obtain ⟨a, ha⟩ := hd
      have ha0 : 1 ≤ a := by
        rcases Nat.eq_zero_or_pos a with hz | hp
        · rw [hz] at ha; omega
        · exact hp
      have halt : a < n := cofactor_lt hd2 ha0 ha
      rcases h a d ⟨1, by rw [Nat.mul_one, Nat.mul_comm a d, ha]⟩ with hda | hda
      · -- `n ∣ a`, impossible since `1 ≤ a < n`
        have hle : n ≤ a := dvd_le_self (by omega) hda
        omega
      · -- `n ∣ d`, impossible since `0 < d < n`
        have hle : n ≤ d := dvd_le_self (by omega) hda
        omega

/-- **#10.** Divisors inside `Finset.range n` are trivial. -/
theorem dvdForm_iff_finset_range (n : ℕ) :
    (n > 1 ∧ ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n) ↔
      (n > 1 ∧ ∀ d ∈ Finset.range n, d ∣ n → d = 1) := by
  constructor
  · rintro ⟨h1, h⟩
    refine ⟨h1, ?_⟩
    intro d hin hdn
    rcases h d hdn with hq1 | hq2
    · exact hq1
    · exfalso
      have hlt : d < n := by simpa using hin
      rw [hq2] at hlt
      omega
  · rintro ⟨h1, h⟩
    refine ⟨h1, ?_⟩
    intro d hd
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    · refine Or.inr ?_
      by_contra hdn
      have hlt : d < n := dvd_lt_of_ne (by omega) hd hdn
      exact hd1 (h d (by simp [hlt]) hd)

end Equiv.NatPrime
