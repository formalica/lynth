-- Finite-domain pilot: positional lookups (by value + by predicate).
-- Spec: `l.idxOf? 9 = some 2 ∧ l.findIdx? (· % 2 = 0) = some 0 ∧
-- l.length = 4 ∧ l.sum = 22 ∧ l.Nodup`.
-- `lynth` must combine: idxOf? pins l[2] = 9 (length > 2 inferred),
-- findIdx? pins head even AND minimality of the index (no earlier even
-- — trivially true at 0, but forces head parity), sum + nodup + stated
-- length pin the rest. Solution: [4, 1, 9, 8].
-- TODO: failing until multi-property list synthesis lands in the pipeline.
import Lynth

/-- Target property: value lookup, predicate lookup, length, sum, nodup. -/
def ifValid (l : List Nat) : Prop :=
  l.idxOf? 9 = some 2 ∧ l.findIdx? (· % 2 = 0) = some 0 ∧
  l.length = 4 ∧ l.sum = 22 ∧ l.Nodup

/-- Computable check (mirrors `ifValid`). -/
def ifCheck (l : List Nat) : Bool :=
  decide (l.idxOf? 9 = some 2) &&
  decide (l.findIdx? (· % 2 = 0) = some 0) &&
  decide (l.length = 4) && decide (l.sum = 22) && decide l.Nodup

/-- The goal `lynth` must fill: the indexed list. -/
def ifSol : { l : List Nat // ifValid l } := by
  lynth

/-- Etalon: [4, 1, 9, 8] — idxOf 9 = 2 ✓, first even at 0 ✓,
    length 4 ✓, sum 22 ✓, nodup ✓. -/
def etalon : List Nat := [4, 1, 9, 8]

-- The value computed by `lynth`:
#eval (ifSol : List Nat)

-- The etalon:
#eval etalon

-- Runtime check: witness satisfies the lookup properties.
#guard ifCheck (ifSol : List Nat)

/-- info: 'ifSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ifSol
