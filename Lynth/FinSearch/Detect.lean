/-!
Finite-domain detector + router (TASKS.md#Q6 parent procedure).

`estimate` computes the search-space size of a finite-function domain
(product of binder cardinalities = number of board positions).
`route` decides whether the SAT child may attempt it: scalars are
never ours (they belong to `Witness`, which owns enumeration), and
estimates over `maxCells` yield gracefully (one-hot blowup guard).
Thresholds are named constants so tests can land on each side.
-/
namespace Lynth.FinSearch.Detect

/-- Max distinct cells the SAT child will encode (one-hot blowup guard).
Counts board cells plus auxiliary Tseitin-style cells introduced when
flattening suspended branches (one aux per `ite`/`nite` node). -/
def maxCells : Nat := 16384

/-- Max CNF variables the encoder may allocate (`none` = yield).
Sized for 9x9 Sudoku (~40k vars with pairwise-distinct Tseitin gates);
symbolic list computation (`eraseDups`-style ite trees, aux cells +
one-hot mutexes) needs headroom (~4M). -/
def maxSatVars : Nat := 4194304

/-- CDCL fuel for the SAT child (9x9 needs ~1M decisions). -/
def solveFuel : Nat := 2000000

/-- Max domain width unrolled by the counting recognizer (`cardSide`).
Unrolling is linear tactic work (one predicate evaluation per value);
subset blowup is guarded separately by `maxExactKCombos`, so this can
be generous (covers through 32×32 boards). -/
def maxCountUnroll : Nat := 1024

/-- Cap on `exactK` subset expansion, in combinations (per node).
`exactKNaive` builds C(n,k+1)+C(n-k+1,n) gates; hundreds are routine
(10-wide k=2 counts need ~130), while unpruned wide counts need
hundreds of thousands. Counted pre-encode with early exit, so
over-budget shapes yield gracefully instead of hanging the build. -/
def maxExactKCombos : Nat := 20000

/-- min(C(n,k), cap): binomial coefficient with early exit (exact
division at every step, so no fractions ever appear). -/
def chooseCap.go (n : Nat) (cap : Nat) : Nat → Nat → Nat → Nat
  | 0, _, r => r
  | f + 1, j, r =>
    if r >= cap then cap
    else chooseCap.go n cap f (j + 1) ((r * (n - j)) / (j + 1))
def chooseCap (n k : Nat) (cap : Nat) : Nat :=
  if cap == 0 then 0
  else if k > n then 0
  else chooseCap.go n cap (min k (n - k)) 0 1

/-- Combinatorial cost guard for one `exactK` node over `n` live
members targeting `k`: mirrors `exactKNaive` (skips the side it
would skip), refused when the families exceed the budget. -/
def exactKCostOk (n k : Nat) : Bool :=
  let atMost := if k < n then chooseCap n (k + 1) maxExactKCombos else 0
  let atLeast := if 0 < k then chooseCap n (n - k + 1) maxExactKCombos else 0
  atMost + atLeast < maxExactKCombos

/-- Search-space estimate: number of board positions. -/
def estimate (dims : List Nat) : Nat :=
  dims.foldl (· * ·) 1

/-- Route decision: attempt SAT iff function-typed (`isFun`) and within
the cell budget. Scalars yield to `Witness`. -/
def route (isFun : Bool) (nCells : Nat) : Bool :=
  isFun && decide (nCells ≤ maxCells)

end Lynth.FinSearch.Detect
