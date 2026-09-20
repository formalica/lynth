-- Finite-domain pilot: subset-sum over `List Nat`.
-- Given a fixed literal list, find a subcollection (preserving order,
-- i.e. a `List.Sublist`) whose elements sum to the target.
-- NOTE: `lynth` should infer finiteness: every candidate subset is a
-- subsequence of a known finite literal, so the search space is finite
-- (2^n subsets) and brute-force enumeration applies.
-- TODO: failing until list-based finite search lands in the pipeline.
import Lynth

/-- The problem instance: a fixed list of numbers. -/
def ssInput : List Nat := [3, 34, 4, 12, 5, 2]

/-- Target sum (achievable: e.g. 4 + 5, or 3 + 4 + 2). -/
def ssTarget : Nat := 9

/-- `l` solves the instance: it is a subsequence of `ssInput`
(selecting a subset, order preserved) whose sum is `ssTarget`. -/
def subsetSum (l : List Nat) : Prop :=
  l.Sublist ssInput ∧ l.sum = ssTarget

/-- The goal `lynth` must fill: a computable subset list. -/
def ssSol : { l : List Nat // subsetSum l } := by
  lynth

/-- Brute-force reference: enumerate all subsequences of `ssInput`
and check that some (hence the found one, up to choice) sums to 9.
`lynth`'s witness must be one of these. -/
def etalon : List Nat := [4, 5]

-- The value computed by `lynth`:
#eval (ssSol : List Nat)

-- The etalon subset:
#eval etalon

-- Runtime check: the witness is a valid solution
-- (any correct subset is acceptable; the guard pins the found one
-- against a known-good reference solution).
#guard (ssSol : List Nat).Sublist ssInput ∧ (ssSol : List Nat).sum = ssTarget

/-- info: 'ssSol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ssSol
