-- Finite-domain pilot: filter-split + global bound + distinctness.
-- Spec: evens of `l` number 2, odds of `l` sum to 8, all elements < 6,
-- `l` nodup. Total length is NOT stated: it falls out of 2 evens +
-- odd-sum 8 with distinct odds < 6 (forces odds = {3, 5}, hence 2 odds,
-- hence length 2 + 2 = 4, all inferred).
-- TODO: failing until multi-property list synthesis lands in the pipeline.
import Lynth

/-- Target property: even-count, odd-sum, element bound, nodup. -/
def fpcValid (l : List Nat) : Prop :=
  (l.filter (· % 2 = 0)).length = 2 ∧
  (l.filter (· % 2 = 1)).sum = 8 ∧
  l.all (· < 6) ∧ l.Nodup

/-- Computable check (mirrors `fpcValid`). -/
def fpcCheck (l : List Nat) : Bool :=
  decide ((l.filter (· % 2 = 0)).length = 2) &&
  decide ((l.filter (· % 2 = 1)).sum = 8) &&
  decide (l.all (· < 6)) && decide l.Nodup

/-- The goal `lynth` must fill: the mixed list. -/
def fpcSol : { l : List Nat // fpcValid l } := by
  lynth

/-- Etalon: [0, 2, 3, 5] — evens {0,2} (count 2), odds {3,5} (sum 8),
    all < 6, nodup. -/
def etalon : List Nat := [0, 2, 3, 5]

-- The value computed by `lynth`:
#eval (fpcSol : List Nat)

-- The etalon:
#eval etalon

-- Runtime check: witness satisfies the filter-split properties.
#guard fpcCheck (fpcSol : List Nat)

/-- info: 'fpcSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fpcSol
