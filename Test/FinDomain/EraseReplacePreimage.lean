-- Finite-domain pilot: erase + replace preimages + nodup.
-- Spec: `l.erase 5 = [2, 7] ∧ (l.replace 2 8).sum = 20 ∧ l.Nodup`.
-- `lynth` must jointly invert two mutating ops: erase removes the first 5
-- (length = 3 inferred, never stated), replace shifts the sum by +6
-- (pins the replaced element to 2), nodup disambiguates positions.
-- Solution: [5, 2, 7] (erase first 5 → [2,7] ✓; replace 2→8 → [5,8,7]
-- sum 20 ✓; nodup ✓).
-- TODO: failing until multi-property list synthesis lands in the pipeline.
import Lynth

/-- Target property: erase-image, replace-sum, nodup. -/
def erValid (l : List Nat) : Prop :=
  l.erase 5 = [2, 7] ∧ (l.replace 2 8).sum = 20 ∧ l.Nodup

/-- Computable check (mirrors `erValid`). -/
def erCheck (l : List Nat) : Bool :=
  decide (l.erase 5 = [2, 7]) &&
  decide ((l.replace 2 8).sum = 20) && decide l.Nodup

/-- The goal `lynth` must fill: the preimage list. -/
def erSol : { l : List Nat // erValid l } := by
  lynth

/-- Etalon: [5, 2, 7]. -/
def etalon : List Nat := [5, 2, 7]

-- The value computed by `lynth`:
#eval (erSol : List Nat)

-- The etalon:
#eval etalon

-- Runtime check: witness satisfies both preimage properties.
#guard erCheck (erSol : List Nat)

/-- info: 'erSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms erSol
