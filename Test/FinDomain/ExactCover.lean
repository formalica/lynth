-- Finite-domain pilot: exact cover (set partition into equal-sum groups).
-- Items [4, 5, 6, 4, 5, 6] (sum 30) must split into 2 groups of 15 with
-- each item used EXACTLY once. SubsetSum picks ONE subset; this is
-- covering with multiplicity-one — witness is a labeling `Fin 6 → Bool`.
-- NOTE: 2^6 = 64 labelings — finite; brute-force applies.
-- TODO: failing until covering-style synthesis lands in the pipeline.
import Lynth

/-- Item values. -/
def items : List Nat := [4, 5, 6, 4, 5, 6]

/-- Sum of values labeled `b`. -/
def groupSum (g : Fin 6 → Bool) (b : Bool) : Nat :=
  (List.finRange 6).foldl (fun acc i =>
    if g i == b then acc + (items[i.val]! : Nat) else acc) 0

/-- Valid labeling: both groups sum to 15. -/
def coverValid (g : Fin 6 → Bool) : Prop :=
  groupSum g true = 15 ∧ groupSum g false = 15

/-- Computable check (mirrors `coverValid`). -/
def coverCheck (g : Fin 6 → Bool) : Bool :=
  (groupSum g true == 15) && (groupSum g false == 15)

/-- The goal `lynth` must fill: the group labeling. -/
def coverSol : { g : Fin 6 → Bool // coverValid g } := by
  lynth

/-- Etalon: indices {0,1,2} vs {3,4,5} — 4+5+6 = 15 each side. -/
def etalon : Fin 6 → Bool := fun i => decide (i.val < 3)

-- The value computed by `lynth`:
#eval (coverSol : Fin 6 → Bool)

-- The etalon group sums:
#eval (groupSum etalon true, groupSum etalon false)

-- Runtime check: witness partitions into equal sums.
#guard coverCheck (coverSol : Fin 6 → Bool)

/-- info: 'coverSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms coverSol
