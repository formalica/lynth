import Mathlib

/-!
# Alternative definitions: `Nat.mul`

Multiplication is addition repeated.  The alternatives differ in *which*
argument drives the repetition, in the order the factors are consumed, and in
whether the repetition is materialised as a list.
-/

namespace Alt.Nat.mul

/-- The original. -/
def orig (a b : ℕ) : ℕ := a * b

/-- Recursion on the second factor, accumulating with `+`.  This is the shape of
`Nat.mul`'s own definition. -/
def recOnSecond : ℕ → ℕ → ℕ
  | _, 0 => 0
  | a, b + 1 => a + recOnSecond a b

/-- Recursion on the *first* factor instead.  Same function, opposite scheme. -/
def recOnFirst : ℕ → ℕ → ℕ
  | 0, _ => 0
  | a + 1, b => b + recOnFirst a b

/-- `List.range` over the *second* factor: add the multiplicand `b` times. -/
def viaRangeOnB (a b : ℕ) : ℕ :=
  (List.range b).foldl (fun acc _ => acc + a) 0

/-- `List.range` over the *first* factor: add the multiplier `a` times.  The
factors are consumed in the opposite order from `viaRangeOnB`. -/
def viaRangeOnA (a b : ℕ) : ℕ :=
  (List.range a).foldl (fun acc _ => acc + b) 0

/-- Materialise the repeated summands as an actual list of `a`s and `sum` it. -/
def viaReplicateSum (a b : ℕ) : ℕ := (List.replicate b a).sum

/-- Materialise the *other* repeated summand instead: a list of `b`s, summed. -/
def viaReplicateSum' (a b : ℕ) : ℕ := (List.replicate a b).sum

end Alt.Nat.mul
