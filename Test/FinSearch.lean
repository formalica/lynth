-- FinSearch pilots: 4x4 mini-Sudoku + 4x4 Towers end to end,
-- plus router checks (each side of the threshold).
import Lynth
import Mathlib.Data.Fintype.Card

open Lynth.FinSearch

/-- 4x4 Sudoku validity: rows/cols distinct, 2x2 boxes distinct. -/
def miniValid (g : Fin 4 → Fin 4 → Fin 4) : Prop :=
  (∀ r : Fin 4, ∀ c1 : Fin 4, ∀ c2 : Fin 4,
    c1 ≠ c2 → g r c1 ≠ g r c2) ∧
  (∀ c : Fin 4, ∀ r1 : Fin 4, ∀ r2 : Fin 4,
    r1 ≠ r2 → g r1 c ≠ g r2 c) ∧
  List.Pairwise (· ≠ ·) [g 0 0, g 0 1, g 1 0, g 1 1] ∧
  List.Pairwise (· ≠ ·) [g 0 2, g 0 3, g 1 2, g 1 3] ∧
  List.Pairwise (· ≠ ·) [g 2 0, g 2 1, g 3 0, g 3 1] ∧
  List.Pairwise (· ≠ ·) [g 2 2, g 2 3, g 3 2, g 3 3]

/-- A solvable clue set (witnessed by rows 0123/2301/1032/3210). -/
def miniClues (g : Fin 4 → Fin 4 → Fin 4) : Prop :=
  g 0 0 = 0 ∧ g 0 1 = 1 ∧ g 1 2 = 0 ∧ g 1 3 = 1 ∧
  g 2 0 = 1 ∧ g 2 3 = 2 ∧ g 3 1 = 2 ∧ g 3 2 = 1

def miniSudoku : { g : Fin 4 → Fin 4 → Fin 4 // miniValid g ∧ miniClues g } := by
  lynth

#print axioms miniSudoku

/-- 4x4 Towers board: Latin rows/cols (heights 0..3, all different). -/
def towersLatin (g : Fin 4 → Fin 4 → Fin 4) : Prop :=
  (∀ r : Fin 4, ∀ c1 : Fin 4, ∀ c2 : Fin 4,
    c1 ≠ c2 → g r c1 ≠ g r c2) ∧
  (∀ c : Fin 4, ∀ r1 : Fin 4, ∀ r2 : Fin 4,
    r1 ≠ r2 → g r1 c ≠ g r2 c)

/-- Towers clues: row 0 increases (4 visible from the left), row 3
starts tallest (1 visible), column 0 increases top-down, column 3
starts tallest, and row 1 shows exactly 2 from the left (counting
via `Fintype.card`, witnessed by rows 0123/1302/2031/3210). -/
def towersClues (g : Fin 4 → Fin 4 → Fin 4) : Prop :=
  (g 0 0 < g 0 1 ∧ g 0 1 < g 0 2 ∧ g 0 2 < g 0 3) ∧
  (g 3 1 < g 3 0 ∧ g 3 2 < g 3 0 ∧ g 3 3 < g 3 0) ∧
  (g 0 0 < g 1 0 ∧ g 1 0 < g 2 0 ∧ g 2 0 < g 3 0) ∧
  (g 1 3 < g 0 3 ∧ g 2 3 < g 0 3 ∧ g 3 3 < g 0 3) ∧
  Fintype.card { j : Fin 4 // ∀ i : Fin 4, i < j → g 1 i < g 1 j } = 2

def towersSol : { g : Fin 4 → Fin 4 → Fin 4 // towersLatin g ∧ towersClues g } := by
  lynth

#print axioms towersSol

/-- Scalars still route to `Witness` (`finsearch` yields them). -/
def scalarRoute : { n : Nat // n = 42 } := by
  lynth

#print axioms scalarRoute

-- Router lands on each side of the threshold.
example : Detect.route true 16 = true := rfl
example : Detect.route true 513 = false := rfl
example : Detect.route false 16 = false := rfl
example : Detect.estimate [4, 4] = 16 := rfl
