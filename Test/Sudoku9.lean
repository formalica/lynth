-- Scale pilot: full 9x9 Sudoku end-to-end (classic easy puzzle).
-- Needs the watched-literal engine plus raised heartbeat limits for the
-- large `decide` side proof (a few minutes).
import Lynth

def valid9 (g : Fin 9 → Fin 9 → Fin 9) : Prop :=
  (∀ r : Fin 9, ∀ c1 : Fin 9, ∀ c2 : Fin 9,
    c1 ≠ c2 → g r c1 ≠ g r c2) ∧
  (∀ c : Fin 9, ∀ r1 : Fin 9, ∀ r2 : Fin 9,
    r1 ≠ r2 → g r1 c ≠ g r2 c) ∧
  List.Pairwise (· ≠ ·) [g 0 0, g 0 1, g 0 2, g 1 0, g 1 1, g 1 2, g 2 0, g 2 1, g 2 2] ∧
  List.Pairwise (· ≠ ·) [g 0 3, g 0 4, g 0 5, g 1 3, g 1 4, g 1 5, g 2 3, g 2 4, g 2 5] ∧
  List.Pairwise (· ≠ ·) [g 0 6, g 0 7, g 0 8, g 1 6, g 1 7, g 1 8, g 2 6, g 2 7, g 2 8] ∧
  List.Pairwise (· ≠ ·) [g 3 0, g 3 1, g 3 2, g 4 0, g 4 1, g 4 2, g 5 0, g 5 1, g 5 2] ∧
  List.Pairwise (· ≠ ·) [g 3 3, g 3 4, g 3 5, g 4 3, g 4 4, g 4 5, g 5 3, g 5 4, g 5 5] ∧
  List.Pairwise (· ≠ ·) [g 3 6, g 3 7, g 3 8, g 4 6, g 4 7, g 4 8, g 5 6, g 5 7, g 5 8] ∧
  List.Pairwise (· ≠ ·) [g 6 0, g 6 1, g 6 2, g 7 0, g 7 1, g 7 2, g 8 0, g 8 1, g 8 2] ∧
  List.Pairwise (· ≠ ·) [g 6 3, g 6 4, g 6 5, g 7 3, g 7 4, g 7 5, g 8 3, g 8 4, g 8 5] ∧
  List.Pairwise (· ≠ ·) [g 6 6, g 6 7, g 6 8, g 7 6, g 7 7, g 7 8, g 8 6, g 8 7, g 8 8]

def clues9 (g : Fin 9 → Fin 9 → Fin 9) : Prop :=
  g 0 0 = 5 ∧ g 0 1 = 3 ∧ g 0 4 = 7 ∧
  g 1 0 = 6 ∧ g 1 3 = 1 ∧ g 1 4 = 9 ∧ g 1 5 = 5 ∧
  g 2 1 = 9 ∧ g 2 2 = 8 ∧ g 2 7 = 6 ∧
  g 3 0 = 8 ∧ g 3 4 = 6 ∧ g 3 8 = 3 ∧
  g 4 0 = 4 ∧ g 4 3 = 8 ∧ g 4 5 = 3 ∧ g 4 8 = 1 ∧
  g 5 0 = 7 ∧ g 5 4 = 2 ∧ g 5 8 = 6 ∧
  g 6 1 = 6 ∧ g 6 6 = 2 ∧ g 6 7 = 8 ∧
  g 7 3 = 4 ∧ g 7 4 = 1 ∧ g 7 5 = 9 ∧ g 7 8 = 5 ∧
  g 8 4 = 8 ∧ g 8 7 = 7 ∧ g 8 8 = 9

set_option maxHeartbeats 2000000 in
def sudoku9 : { g : Fin 9 → Fin 9 → Fin 9 // valid9 g ∧ clues9 g } := by
  lynth

#print axioms sudoku9
