-- 9x9 Sudoku from a PARTIAL board: `start9` gives the filled cells
-- (as `some v`) and `none` for empties; `extends9` says the solution
-- agrees with every filled cell. `lynth` must construct the completed
-- board and prove validity + extension.
import Lynth
import Mathlib.Data.Fintype.Card

/-- Validity: rows, columns, and 3x3 boxes pairwise distinct. -/
def valid9 (g : Fin 9 → Fin 9 → Fin 9) : Prop :=
  (∀ (r i j : Fin 9), i < j → g r i ≠ g r j) ∧
  (∀ (c i j : Fin 9), i < j → g i c ≠ g j c) ∧
  List.Pairwise (· ≠ ·) [g 0 0, g 0 1, g 0 2, g 1 0, g 1 1, g 1 2, g 2 0, g 2 1, g 2 2] ∧
  List.Pairwise (· ≠ ·) [g 0 3, g 0 4, g 0 5, g 1 3, g 1 4, g 1 5, g 2 3, g 2 4, g 2 5] ∧
  List.Pairwise (· ≠ ·) [g 0 6, g 0 7, g 0 8, g 1 6, g 1 7, g 1 8, g 2 6, g 2 7, g 2 8] ∧
  List.Pairwise (· ≠ ·) [g 3 0, g 3 1, g 3 2, g 4 0, g 4 1, g 4 2, g 5 0, g 5 1, g 5 2] ∧
  List.Pairwise (· ≠ ·) [g 3 3, g 3 4, g 3 5, g 4 3, g 4 4, g 4 5, g 5 3, g 5 4, g 5 5] ∧
  List.Pairwise (· ≠ ·) [g 3 6, g 3 7, g 3 8, g 4 6, g 4 7, g 4 8, g 5 6, g 5 7, g 5 8] ∧
  List.Pairwise (· ≠ ·) [g 6 0, g 6 1, g 6 2, g 7 0, g 7 1, g 7 2, g 8 0, g 8 1, g 8 2] ∧
  List.Pairwise (· ≠ ·) [g 6 3, g 6 4, g 6 5, g 7 3, g 7 4, g 7 5, g 8 3, g 8 4, g 8 5] ∧
  List.Pairwise (· ≠ ·) [g 6 6, g 6 7, g 6 8, g 7 6, g 7 7, g 7 8, g 8 6, g 8 7, g 8 8]

/-- The given (partial) board: 30 filled cells, rest empty. -/
def start9 : Fin 9 → Fin 9 → Option (Fin 9) := fun r c =>
  if r = 0 ∧ c = 0 then some 5 else if r = 0 ∧ c = 1 then some 3 else
  if r = 0 ∧ c = 4 then some 7 else if r = 1 ∧ c = 0 then some 6 else
  if r = 1 ∧ c = 3 then some 1 else if r = 1 ∧ c = 4 then some 9 else
  if r = 1 ∧ c = 5 then some 5 else if r = 2 ∧ c = 1 then some 9 else
  if r = 2 ∧ c = 2 then some 8 else if r = 2 ∧ c = 7 then some 6 else
  if r = 3 ∧ c = 0 then some 8 else if r = 3 ∧ c = 4 then some 6 else
  if r = 3 ∧ c = 8 then some 3 else if r = 4 ∧ c = 0 then some 4 else
  if r = 4 ∧ c = 3 then some 8 else if r = 4 ∧ c = 5 then some 3 else
  if r = 4 ∧ c = 8 then some 1 else if r = 5 ∧ c = 0 then some 7 else
  if r = 5 ∧ c = 4 then some 2 else if r = 5 ∧ c = 8 then some 6 else
  if r = 6 ∧ c = 1 then some 6 else if r = 6 ∧ c = 6 then some 2 else
  if r = 6 ∧ c = 7 then some 8 else if r = 7 ∧ c = 3 then some 4 else
  if r = 7 ∧ c = 4 then some 1 else if r = 7 ∧ c = 5 then some 9 else
  if r = 7 ∧ c = 8 then some 5 else if r = 8 ∧ c = 4 then some 8 else
  if r = 8 ∧ c = 7 then some 7 else if r = 8 ∧ c = 8 then some 9 else
  none

/-- The solution extends the partial board. -/
def extends9 (g : Fin 9 → Fin 9 → Fin 9) : Prop :=
  ∀ (r c : Fin 9) (x : Fin 9), start9 r c = some x → g r c = x

set_option maxHeartbeats 2000000 in
def sudoku9 : { g : Fin 9 → Fin 9 → Fin 9 // valid9 g ∧ extends9 g } := by
  lynth

#print axioms sudoku9
