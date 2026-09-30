import Mathlib

/-!
# Alternative definitions: `Nat.sub`

`Nat.sub` is *truncated* subtraction, so every alternative has to reproduce the
`a ≤ b → 0` convention rather than a predecessor iteration that would run off
the bottom of `ℕ`.
-/

namespace Alt.Nat.sub

/-- The original. -/
def orig (a b : ℕ) : ℕ := a - b

/-- Recursion on the subtrahend, which is how `Nat.sub` is itself built. -/
def recOnSecond : ℕ → ℕ → ℕ
  | a, 0 => a
  | a, b + 1 => (recOnSecond a b) - 1

/-- Recursion on *both* arguments, saturating as soon as either runs out. -/
def recBoth : ℕ → ℕ → ℕ
  | 0, _ => 0
  | a, 0 => a
  | a + 1, b + 1 => recBoth a b

/-- The plain "peel a successor" recursion, isolated in a helper so the
truncation strategies below stay visible side by side. -/
def plain : ℕ → ℕ → ℕ
  | a, 0 => a
  | a, b + 1 => (plain a b) - 1

/-- Truncation applied *first*, by clamping the subtrahend with `Nat.min`, and
only then running the plain recursion.  Opposite order to `recOnSecond`. -/
def viaMin (a b : ℕ) : ℕ := plain a (min a b)

/-- Counting up from zero until the addition equation `c + b = a` holds.  No
`Nat.sub` in the definition at all. -/
def viaAddCount (a b : ℕ) : ℕ := go 0 a
where
  go : ℕ → ℕ → ℕ
  | c, 0 => if c + b = a then c else 0
  | c, fuel + 1 => if c + b = a then c else go (c + 1) fuel
termination_by _ fuel => fuel

end Alt.Nat.sub
