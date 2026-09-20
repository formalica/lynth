-- Finite-domain pilot: knight's tour on a 5x5 board, asked as ONE
-- goal with the Answer type unfolded.
-- The tour is a function `pos : Fin 5 → Fin 5 → Fin 25` giving each
-- square its visit number; a valid tour visits every square exactly
-- once (bijective numbering) and each consecutive pair of squares is
-- a knight move apart.
-- This instance is SAT (an open knight's tour on 5x5 exists).
-- TODO: failing until `Answer` goals are recognized by the pipeline;
--       also the deepest search-guidance stress test in this suite.
import Lynth

/-- Absolute difference on `Nat`. -/
def adiff (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- Squares `(r1,c1)` and `(r2,c2)` are a knight move apart:
coordinate deltas are {1,2} in some order. -/
def knightMove (r1 c1 r2 c2 : Nat) : Prop :=
  (adiff r1 r2 = 1 ∧ adiff c1 c2 = 2) ∨
  (adiff r1 r2 = 2 ∧ adiff c1 c2 = 1)

/-- A valid open knight's tour: visit numbers are pairwise distinct
(every square visited exactly once) and the squares with consecutive
visit numbers are knight moves apart. -/
def tourValid (pos : Fin 5 → Fin 5 → Fin 25) : Prop :=
  (∀ r1 c1 r2 c2 : Fin 5, (r1, c1) ≠ (r2, c2) →
    pos r1 c1 ≠ pos r2 c2) ∧
  (∀ r1 c1 r2 c2 : Fin 5,
    (pos r1 c1 : Nat) + 1 = (pos r2 c2 : Nat) →
    knightMove (r1 : Nat) (c1 : Nat) (r2 : Nat) (c2 : Nat))

/-- One `lynth` run decides: expect `.inl` (a tour exists). -/
def knightsTour :
    let p := tourValid
    { w // p w } ⊕' (∀ x, ¬ p x) := by
  lynth

/-- info: 'knightsTour' depends on axioms: [propext] -/
#guard_msgs in
#print axioms knightsTour
