import Lynth
import Mathlib.Data.Fintype.Card

namespace FinDomain.Meta

def Board := Fin 9 → Fin 9 → Fin 9

def PartialBoard := Fin 9 → Fin 9 → Option (Fin 9)

def box_idx (r c : Fin 9) : Fin 9 :=
  (r / 3) * 3 + (c / 3)

def valid_rows (b : Board) : Prop :=
  ∀ r c₁ c₂, b r c₁ = b r c₂ → c₁ = c₂

def valid_cols (b : Board) : Prop :=
  ∀ c r₁ r₂, b r₁ c = b r₂ c → r₁ = r₂

def valid_boxes (b : Board) : Prop :=
  ∀ r₁ c₁ r₂ c₂,
    box_idx r₁ c₁ = box_idx r₂ c₂ →
    b r₁ c₁ = b r₂ c₂ →
    r₁ = r₂ ∧ c₁ = c₂

def matches_partial (p : PartialBoard) (b : Board) : Prop :=
  ∀ r c v, p r c = some v → b r c = v

def ValidSolution (p : PartialBoard) (b : Board) : Prop :=
  valid_rows b ∧
  valid_cols b ∧
  valid_boxes b ∧
  matches_partial p b

def CorrectSudokuSolver
    (solver : PartialBoard → Option Board) : Prop :=
  (∀ p b, solver p = some b → ValidSolution p b) ∧
  (∀ p, (∃ b, ValidSolution p b) →
    ∃ b, solver p = some b) ∧
  (∀ p, solver p = none ↔
    ¬∃ b, ValidSolution p b)

/-- Synthesize a solver function, not merely one completed board. -/
set_option maxHeartbeats 10000000 in
def sudokuInkalaSolver :
    { solver : PartialBoard → Option Board //
      CorrectSudokuSolver solver } := by
  lynth

/-- Arto Inkala's 2012 Sudoku instance. -/
def example_partial (r c : Fin 9) : Option (Fin 9) :=
  match r.val, c.val with
  | 0, 2 => some 5
  | 0, 3 => some 3
  | 1, 0 => some 8
  | 1, 7 => some 2
  | 2, 1 => some 7
  | 2, 4 => some 1
  | 2, 6 => some 5
  | 3, 0 => some 4
  | 3, 5 => some 5
  | 3, 6 => some 3
  | 4, 1 => some 1
  | 4, 4 => some 7
  | 4, 8 => some 6
  | 5, 2 => some 3
  | 5, 3 => some 2
  | 5, 7 => some 8
  | 6, 1 => some 6
  | 6, 3 => some 5
  | 6, 8 => some 9
  | 7, 2 => some 4
  | 7, 7 => some 3
  | 8, 5 => some 9
  | 8, 6 => some 7
  | _, _ => none

/-- An initial board with two equal values forced into the same row. -/
def contradictoryPartial (r c : Fin 9) : Option (Fin 9) :=
  if r = 0 then
    if c = 0 then
      some 1
    else if c = 1 then
      some 1
    else
      none
  else
    none

/-- Benchmark the synthesized solver on the satisfiable instance. -/
#guard (sudokuInkalaSolver.1 example_partial).isSome

/-- Benchmark the synthesized solver on the unsatisfiable instance. -/
#guard (sudokuInkalaSolver.1 contradictoryPartial).isNone

/-- info: 'FinDomain.Meta.sudokuInkalaSolver' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sudokuInkalaSolver

end FinDomain.Meta
