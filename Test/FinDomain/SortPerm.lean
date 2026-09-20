-- Finite-domain pilot: given a fixed list of numbers, find (via
-- `lynth` + Subtype) a new list that is a permutation of the original
-- AND sorted. Then sort the original with the library `mergeSort` and
-- guard that `lynth`'s computed witness equals the etalon.
--
-- NOTE: `lynth` should be able to infer that `l` has the same length
-- as `input` (since `l.Perm input` forces equal lengths), and the
-- original list is a known finite literal — so the search space
-- (permutations of `input`) is finite too and the witness can be
-- found by brute-force enumeration over that finite space.
import Lynth

/-- The problem instance: a fixed list of "random" numbers. -/
def input : List Nat := [42, 7, 19, 3, 25, 11, 8, 30, 15, 2]

/-- Target property: `l` is a permutation of `xs` and sorted
non-decreasingly. -/
def sortedPerm (xs l : List Nat) : Prop :=
  l.Perm xs ∧ l.Pairwise (· ≤ ·)

/-- The goal `lynth` must fill: a computable list that is a
permutation of `input` and sorted. Expect the witness to be the
sorted list, as computable data. -/
def sortedInput : { l : List Nat // sortedPerm input l } := by
  lynth

/-- Etalon: sort the original with the library merge sort. -/
def etalon : List Nat := input.mergeSort

-- The value computed by `lynth`:
#eval (sortedInput : List Nat)  -- expect [2, 3, 7, 8, 11, 15, 19, 25, 30, 42]

-- The etalon:
#eval etalon                    -- expect [2, 3, 7, 8, 11, 15, 19, 25, 30, 42]

-- Runtime check: `lynth`'s witness equals the etalon.
#guard (sortedInput : List Nat) = etalon

/-- info: 'sortedInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sortedInput
