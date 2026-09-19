-- Alternative formalizations of the same finite-domain puzzle class.
-- Point: `lynth` is goal-directed (recognize → SAT → decode → kernel
-- verify), so the *shape* of the Lean definition should not matter as
-- long as it is a decidable finite-domain statement. Each block below
-- states 4x4 Sudoku rules in a different style.
import Lynth
import Mathlib.Data.Fintype.Card

open Lynth.FinSearch

-- Style A: rules as quantified implications with `Ne` bodies
-- (`∀ i j, i < j → g r i ≠ g r j`), no explicit Pairwise lists.
def altRows (g : Fin 4 → Fin 4 → Fin 4) : Prop :=
  ∀ (r i j : Fin 4), i < j → g r i ≠ g r j

def altCols (g : Fin 4 → Fin 4 → Fin 4) : Prop :=
  ∀ (c i j : Fin 4), i < j → g i c ≠ g j c

-- Style B: counting constraints (`Fintype.card { x // P x } = k`)
-- saying each column holds exactly one `2`.
def altTwos (g : Fin 4 → Fin 4 → Fin 4) : Prop :=
  ∀ c : Fin 4, Fintype.card { r : Fin 4 // g r c = 2 } = 1

-- Style C: propositional links between cells (`Iff`) plus a named
-- helper predicate unfolded by the reconstructor.
def rowDistinct (g : Fin 4 → Fin 4 → Fin 4) (r : Fin 4) : Prop :=
  g r 0 ≠ g r 1 ∧ g r 0 ≠ g r 2 ∧ g r 0 ≠ g r 3 ∧
    g r 1 ≠ g r 2 ∧ g r 1 ≠ g r 3 ∧ g r 2 ≠ g r 3

def altLinks (g : Fin 4 → Fin 4 → Fin 4) : Prop :=
  (g 0 0 = 1 ↔ g 1 3 = 2) ∧ (g 2 1 = 0 ↔ g 3 2 = 3) ∧
    ∀ r : Fin 4, rowDistinct g r

-- Three clues only — the solver must place the remaining 13 values.
def altClues (g : Fin 4 → Fin 4 → Fin 4) : Prop :=
  g 0 0 = 0 ∧ g 1 1 = 3 ∧ g 3 2 = 1

set_option maxHeartbeats 1000000 in
def altSudoku : { g : Fin 4 → Fin 4 → Fin 4 //
    altRows g ∧ altCols g ∧ altTwos g ∧ altLinks g ∧ altClues g } := by
  lynth

/-- info: 'altSudoku' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms altSudoku
