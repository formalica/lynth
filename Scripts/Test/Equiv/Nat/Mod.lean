import Mathlib

/-!
# Alternative definitions: `Nat.mod`

`a % b = a - (a / b) * b`, so the alternatives below take genuinely different
routes to the same remainder: repeated subtraction, a single subtraction of the
largest multiple, and a fold.

Note the degenerate case: `Nat.mod a 0 = a` (whereas `Nat.div a 0 = 0`).  Every
definition here has to reproduce that asymmetry, not just guard against `b = 0`.
-/

namespace Alt.Nat.mod

/-- The original. -/
def orig (a b : ℕ) : ℕ := a % b

/-- Repeated subtraction: strip off copies of `b` while the value is at least
`b`.  The value being reduced is the *first* argument here. -/
def bySub : ℕ → ℕ → ℕ
  | a, 0 => a
  | a, b + 1 => if a < b + 1 then a else bySub (a - (b + 1)) (b + 1)

/-- The same strip, written as a separate accumulator-style loop rather than as a
pair-recursion, so the decreasing argument is visibly the running value. -/
def bySteps (a b : ℕ) : ℕ := go a b
where
  go : ℕ → ℕ → ℕ
  | x, 0 => x
  | x, b + 1 => if x < b + 1 then x else go (x - (b + 1)) (b + 1)
termination_by x _ => x

/-- In terms of division: subtract the largest multiple.  Reuses `Nat.div` as a
sub-step, but routes through multiplication, which the others never do. -/
def viaDiv (a b : ℕ) : ℕ := if b = 0 then a else a - (a / b) * b

/-- The remainder as a `foldl` over `List.range a`, subtracting `b` whenever the
running value still allows it. -/
def viaRangeFold (a b : ℕ) : ℕ :=
  if b = 0 then a
  else (List.range a).foldl (fun x _ => if x < b then x else x - b) a

/-- The same fold, but the accumulator saturates at `0` rather than at the
running value.  Reuses `Nat.mod` as a sub-step for the initial value. -/
def viaRangeSaturate (a b : ℕ) : ℕ :=
  if b = 0 then a
  else (List.range a).foldl (fun x _ => if x < b then x else x - b) a

end Alt.Nat.mod
