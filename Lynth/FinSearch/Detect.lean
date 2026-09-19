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

/-- Search-space estimate: number of board positions. -/
def estimate (dims : List Nat) : Nat :=
  dims.foldl (· * ·) 1

/-- Route decision: attempt SAT iff function-typed (`isFun`) and within
the cell budget. Scalars yield to `Witness`. -/
def route (isFun : Bool) (nCells : Nat) : Bool :=
  isFun && decide (nCells ≤ maxCells)

end Lynth.FinSearch.Detect
