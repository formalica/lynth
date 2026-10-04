-- Finite-domain pilot: positional lookups (by value + by predicate).
-- Spec: `l.idxOf? 9 = some 2 ∧ l.findIdx? (· % 2 = 0) = some 0 ∧
-- l.length = 4 ∧ l.sum = 22 ∧ l.Nodup`.
-- `lynth` must combine: idxOf? pins l[2] = 9 (length > 2 inferred),
-- findIdx? pins head even AND minimality of the index (no earlier even
-- — trivially true at 0, but forces head parity), sum + nodup + stated
-- length pin the rest. Solution: [4, 1, 9, 8].
-- TODO: failing until multi-property list synthesis lands in the pipeline.
import Lynth

set_option maxHeartbeats 273 in
/-- Target property: value lookup, predicate lookup, length, sum, nodup. -/
def ifValid (l : List Nat) : Prop :=
  l.idxOf? 9 = some 2 ∧ l.findIdx? (· % 2 = 0) = some 0 ∧
  l.length = 4 ∧ l.sum = 22 ∧ l.Nodup

set_option maxHeartbeats 403 in
/-- Computable check (mirrors `ifValid`). -/
def ifCheck (l : List Nat) : Bool :=
  decide (l.idxOf? 9 = some 2) &&
  decide (l.findIdx? (· % 2 = 0) = some 0) &&
  decide (l.length = 4) && decide (l.sum = 22) && decide l.Nodup

set_option maxHeartbeats 1452 in
/-- The goal `lynth` must fill: the indexed list. -/
def ifSol : { l : List Nat // ifValid l } := by
  lynth
/-- info: 'ifSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ifSol

set_option maxHeartbeats 34 in
/-- Etalon: [4, 1, 9, 8] — idxOf 9 = 2 ✓, first even at 0 ✓,
    length 4 ✓, sum 22 ✓, nodup ✓. -/
def idxFindFromValues_etalon : List Nat := [4, 1, 9, 8]

-- The value computed by `lynth`:
#eval (ifSol : List Nat)

-- The idxFindFromValues_etalon:
#eval idxFindFromValues_etalon

-- Runtime check: witness satisfies the lookup properties.
#guard ifCheck (ifSol : List Nat)

