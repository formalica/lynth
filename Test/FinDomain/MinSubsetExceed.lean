-- Finite-domain pilot: select the FEWEST elements of a fixed list
-- whose sum exceeds the target.
-- Instance [8, 3, 12, 5, 9, 4], target 20. E.g. [12, 9] (two elements,
-- sum 21) is optimal; no single element exceeds 20.
-- NOTE: `lynth` should infer finiteness: every candidate is a
-- subsequence of a known finite literal, so the search space is finite
-- (2^n subsets) and brute-force enumeration applies.
-- TODO: failing until list-based finite search lands in the pipeline.
import Lynth

/-- The problem instance: a fixed list of numbers. -/
def msInput : List Nat := [8, 3, 12, 5, 9, 4]

/-- Target threshold (strictly exceeded). -/
def msTarget : Nat := 20

/-- Goal: valid (subsequence, sum exceeds target) and minimal in length. -/
def msSol : { l : List Nat //
    l.Sublist msInput ∧ msTarget < l.sum ∧
    ∀ m : List Nat, m.Sublist msInput → msTarget < m.sum → l.length ≤ m.length } := by
  lynth

/-- Etalon: [12, 9] — two elements summing to 21 > 20. -/
def etalon : List Nat := [12, 9]

-- The value computed by `lynth`:
#eval (msSol : List Nat)

-- The etalon:
#eval etalon

-- Runtime checks: witness is valid and optimal.
#guard (msSol : List Nat).Sublist msInput ∧ msTarget < (msSol : List Nat).sum
#guard (msSol : List Nat).length = 2

/-- info: 'msSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms msSol
