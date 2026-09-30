import Mathlib

/-!
# Alternative definitions: `Nat.lcm`

`lcm 0 b = 0`, which is the opposite degenerate case from `Nat.gcd 0 b = b`.
Several of the definitions below route through `Nat.gcd` and therefore have to
be careful not to divide by it.
-/

namespace Alt.Nat.lcm

/-- The original. -/
def orig (a b : ℕ) : ℕ := Nat.lcm a b

/-- From the identity `lcm a b * gcd a b = a * b`, inverting it.  Needs the zero
case handled up front, since `gcd 0 b = b` and the quotient is only meaningful
when the gcd is nonzero. -/
def viaGcdProduct (a b : ℕ) : ℕ :=
  if a = 0 ∨ b = 0 then 0 else (a * b) / Nat.gcd a b

/-- Search over the multiples of `a` up to `b * a`, taking the first that `b`
divides.  Restricted to a bounded range, so it needs no termination argument. -/
def viaRangeScan (a b : ℕ) : ℕ :=
  if a = 0 ∨ b = 0 then 0
  else
    let cands := (List.range (b + 1)).map (fun k => k * a)
    ((cands.filter (fun m => m != 0 && m % b == 0)).head?).getD 0

/-- Least common multiple as the least positive element of the set of common
multiples, obtained as the `head?` of the filtered increasing range of multiples
of `a`. -/
def viaHeadOfCommonMultiples (a b : ℕ) : ℕ :=
  if a = 0 ∨ b = 0 then 0
  else
    ((List.range (a * b + 1)).filter (fun m => m != 0 && m % a == 0 && m % b == 0)).head?
      |>.getD 0

/-- The same search as `viaRangeScan` but over the *full* set of common
multiples up to `a * b`, and folded rather than searched. -/
def viaFoldFirstCommon (a b : ℕ) : ℕ :=
  if a = 0 ∨ b = 0 then 0
  else
    (List.range (a * b + 1)).foldl (fun acc m =>
      if acc != 0 then acc
      else if m != 0 && m % a == 0 && m % b == 0 then m else 0) 0

end Alt.Nat.lcm
