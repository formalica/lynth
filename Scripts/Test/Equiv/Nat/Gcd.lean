import Mathlib

/-!
# Alternative definitions: `Nat.gcd`

Reference file for this directory.  The brief: for each widely used function,
give several *computable* definitions computing the same result.  No lemmas, no
`theorem`s — the deliverable is `def`s that evaluate to the right values.
Equivalence with the original is proved separately, in the `Proofs/` directory
next door, so that these files stay pure `def`.

Rules followed by every file here:

* one `def` per alternative, all inside `namespace Alt.<fn>`;
* every `def` is genuinely computable — no `Classical`, no `sorry`, no
  hand-rolled `Decidable`;
* an alternative may reuse the original function as a substep, but must add
  something new: a different algorithm, a different decomposition, or a
  different recursion scheme.  Not a renamed copy;
* `def` only — never `theorem`/`lemma`;
* file is `Alt<Fn>.lean`, namespace is `Alt.<fn>`.

## A trap worth recording

`Nat.gcd 0 5 = 5`, not `0`.  So every definition here that works over
`List.range` has to special-case a zero argument, and any definition built from
`a * b / lcm a b` has to special-case it *before* the division, since
`lcm 0 5 = 0` and the quotient would be `0`.  Getting this wrong is the
difference between "computes the right answer" and "computes *a* answer".
-/

namespace Alt.Nat.gcd

/-- The original, kept as the reference point. -/
def orig (a b : ℕ) : ℕ := Nat.gcd a b

/-- Euclidean algorithm written out.  The baseline "obvious" alternative:
recursive on the pair, decreasing on the second argument (which strictly
shrinks because `a % b < b`). -/
def euclid (a b : ℕ) : ℕ :=
  if b = 0 then a else euclid b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

/-- The common divisors of `a` and `b`, ascending.  A shared building block for
the three list-driven definitions below. -/
def commonDivisors (a b : ℕ) : List ℕ :=
  (List.range (min a b + 1)).filter (fun d => (a % d = 0) && (b % d = 0))

/-- GCD by linear scan: fold over `1 … min a b` and keep the most recent
candidate.  No recursion on the arguments at all. -/
def byScan (a b : ℕ) : ℕ :=
  if a = 0 then b else if b = 0 then a
  else (List.range (min a b + 1)).foldl
    (fun acc d => if (a % d = 0) && (b % d = 0) then d else acc) 0

/-- GCD as a search rather than a scan: `head?` of the *descending* candidate
list.  Same search space as `byScan`, different combinator and opposite
traversal direction. -/
def byFind (a b : ℕ) : ℕ :=
  if a = 0 then b else if b = 0 then a
  else (commonDivisors a b).reverse.head?.getD 0

/-- GCD as a `foldr`, which visits the candidate list from the small end and
keeps the first non-zero it meets. -/
def byFoldr (a b : ℕ) : ℕ :=
  if a = 0 then b else if b = 0 then a
  else (commonDivisors a b).foldr (fun d acc => if acc = 0 then d else acc) 0

/-- GCD from the product/lcm identity `gcd a b * lcm a b = a * b`.  Reuses
`Nat.lcm` (and hence `Nat.gcd`) as a substep but inverts the relationship. -/
def byProductLcm (a b : ℕ) : ℕ :=
  if a = 0 then b else if b = 0 then a else (a * b) / Nat.lcm a b

end Alt.Nat.gcd
