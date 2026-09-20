-- Finite-domain pilot: take/drop windows + map/count coupling.
-- Spec: `l.take 2 = [7, 1] ∧ l.drop 2 = [1, 7] ∧ (l.map (· % 3)).count 1 = 4`.
-- Total length is NOT stated: take-2 ++ drop-2 reconstructs `l`, so length
-- 4 is inferred from complementary windows; the map/count conjunct couples
-- all 4 elements ([7,1,1,7] maps mod 3 to [1,1,1,1], count of 1 = 4).
-- TODO: failing until multi-property list synthesis lands in the pipeline.
import Lynth

/-- Target property: take/drop windows + mapped-value count. -/
def tdValid (l : List Nat) : Prop :=
  l.take 2 = [7, 1] ∧ l.drop 2 = [1, 7] ∧ (l.map (· % 3)).count 1 = 4

/-- Computable check (mirrors `tdValid`). -/
def tdCheck (l : List Nat) : Bool :=
  decide (l.take 2 = [7, 1]) &&
  decide (l.drop 2 = [1, 7]) &&
  decide ((l.map (· % 3)).count 1 = 4)

/-- The goal `lynth` must fill: the windowed list. -/
def tdSol : { l : List Nat // tdValid l } := by
  lynth

/-- Etalon: [7, 1, 1, 7]. -/
def etalon : List Nat := [7, 1, 1, 7]

-- The value computed by `lynth`:
#eval (tdSol : List Nat)

-- The etalon:
#eval etalon

-- Runtime check: witness satisfies the window + count properties.
#guard tdCheck (tdSol : List Nat)

/-- info: 'tdSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms tdSol
