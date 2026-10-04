-- Finite-domain pilot: erase + replace preimages + nodup.
-- Spec: `l.erase 5 = [2, 7] ∧ (l.replace 2 8).sum = 20 ∧ l.Nodup`.
-- `lynth` must jointly invert two mutating ops: erase removes the first 5
-- (length = 3 inferred, never stated), replace shifts the sum by +6
-- (pins the replaced element to 2), nodup disambiguates positions.
-- Solution: [5, 2, 7] (erase first 5 → [2,7] ✓; replace 2→8 → [5,8,7]
-- sum 20 ✓; nodup ✓).
-- TODO: failing until multi-property list synthesis lands in the pipeline.
import Lynth

set_option maxHeartbeats 46 in
/-- Target property: erase-image, replace-sum, nodup. -/
def erValid (l : List Nat) : Prop :=
  l.erase 5 = [2, 7] ∧ (l.replace 2 8).sum = 20 ∧ l.Nodup

set_option maxHeartbeats 135 in
/-- Computable check (mirrors `erValid`). -/
def erCheck (l : List Nat) : Bool :=
  decide (l.erase 5 = [2, 7]) &&
  decide ((l.replace 2 8).sum = 20) && decide l.Nodup

set_option maxHeartbeats 312 in
/-- The goal `lynth` must fill: the preimage list. -/
def erSol : { l : List Nat // erValid l } := by
  lynth
/-- info: 'erSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms erSol

set_option maxHeartbeats 27 in
/-- Etalon: [5, 2, 7]. -/
def eraseReplacePreimage_etalon : List Nat := [5, 2, 7]

-- The value computed by `lynth`:
#eval (erSol : List Nat)

-- The eraseReplacePreimage_etalon:
#eval eraseReplacePreimage_etalon

-- Runtime check: witness satisfies both preimage properties.
#guard erCheck (erSol : List Nat)

