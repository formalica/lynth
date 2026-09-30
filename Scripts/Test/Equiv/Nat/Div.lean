import Mathlib

/-!
# Alternative definitions: `Nat.div`

Truncated division: `a / b` is `0` when `b = 0`.  The alternatives below detect
truncation in different ways — by order comparison, by a multiplicative search,
and by counting — rather than branching on `b = 0` the same way each time.
-/

namespace Alt.Nat.div

/-- The original. -/
def orig (a b : ℕ) : ℕ := a / b

/-- Repeated subtraction, the textbook definition: subtract `b` while the
remainder is still at least `b`.  Linear in the quotient. -/
def bySub : ℕ → ℕ → ℕ
  | _, 0 => 0
  | a, b + 1 => if a < b + 1 then 0 else bySub (a - (b + 1)) (b + 1) + 1

/-- Search over the multiples: the largest `k ≤ a` with `(k+1) * b ≤ a`, found by
a `foldl` over `List.range`.  Uses only `*` and `≤`. -/
def viaRangeFold (a b : ℕ) : ℕ :=
  if b = 0 then 0
  else (List.range (a + 1)).foldl (fun acc k => if (k + 1) * b ≤ a then k + 1 else acc) 0

/-- Counting instead of searching: the number of *positive* multiples of `b` that
are at most `a`.  A `countP` rather than a `foldl`, and it never looks at the
quotient. -/
def viaRangeCount (a b : ℕ) : ℕ :=
  if b = 0 then 0
  else (List.range (a + 1)).countP (fun k => k != 0 && k % b == 0)

/-- The same count, but the list is filtered down to the multiples first and the
result is the list's `length`.  Different combinator over the same search space. -/
def viaFilterLength (a b : ℕ) : ℕ :=
  if b = 0 then 0
  else ((List.range (a + 1)).filter (fun k => k != 0 && k % b == 0)).length

end Alt.Nat.div
