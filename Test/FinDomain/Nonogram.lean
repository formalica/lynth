-- Finite-domain pilot: 4×4 Nonogram from row/column run projections.
-- Witness is a Bool GRID; constraints are GLOBAL run-length projections,
-- not local adjacency/≠ like queens/tours.
-- NOTE: 2^16 = 65536 grids — finite; brute-force applies.
-- TODO: failing until projection-style synthesis lands in the pipeline.
import Lynth

set_option maxHeartbeats 168 in
/-- Run-length encoding of a row/column (lengths of `true` blocks). -/
def runs : List Bool → List Nat
  | [] => []
  | false :: rest => runs rest
  | true :: rest => countRun rest 1
where
  /-- Count a `true`-run starting at length `n` (structurally shrinking). -/
  countRun : List Bool → Nat → List Nat
    | [], n => [n]
    | false :: rest, n => n :: runs rest
    | true :: rest, n => countRun rest (n + 1)

set_option maxHeartbeats 54 in
/-- Row clues: rows must be [2], [1,1], [], [3]. -/
def rowClues : List (List Nat) := [[2], [1, 1], [], [3]]

set_option maxHeartbeats 53 in
/-- Column clues: cols must be [1], [1,1], [2,1], [1]. -/
def colClues : List (List Nat) := [[1], [1, 1], [2, 1], [1]]

set_option maxHeartbeats 69 in
/-- Valid grid: every row/column matches its run clue. -/
def nonoValid (g : Fin 4 → Fin 4 → Bool) : Prop :=
  (∀ r : Fin 4, runs [g r 0, g r 1, g r 2, g r 3] = rowClues[r.val]!) ∧
  (∀ c : Fin 4, runs [g 0 c, g 1 c, g 2 c, g 3 c] = colClues[c.val]!)

set_option maxHeartbeats 52 in
/-- All indices, for computable checks. -/
def idx : List (Fin 4) := [0, 1, 2, 3]

set_option maxHeartbeats 201 in
/-- Computable check (mirrors `nonoValid`). -/
def nonoCheck (g : Fin 4 → Fin 4 → Bool) : Bool :=
  (idx.all fun r => decide (runs [g r 0, g r 1, g r 2, g r 3] = rowClues[r.val]!)) &&
  (idx.all fun c => decide (runs [g 0 c, g 1 c, g 2 c, g 3 c] = colClues[c.val]!))

set_option maxHeartbeats 135925 in
/-- The goal `lynth` must fill: the picture grid. -/
def nonoSol : { g : Fin 4 → Fin 4 → Bool // nonoValid g } := by
  lynth
/-- info: 'nonoSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms nonoSol

set_option maxHeartbeats 161 in
/-- Etalon grid.
    Row 0: · █ █ ·     Row 1: █ · █ ·     Row 2: · · · ·     Row 3: · █ █ █ -/
def nonogram_etalon : Fin 4 → Fin 4 → Bool := fun r c =>
  match r.val, c.val with
  | 0, 1 => true | 0, 2 => true
  | 1, 0 => true | 1, 2 => true
  | 3, 1 => true | 3, 2 => true | 3, 3 => true
  | _, _ => false

-- The value computed by `lynth`:
#eval (nonoSol : Fin 4 → Fin 4 → Bool)

-- The nonogram_etalon row runs:
#eval idx.map fun r => runs [nonogram_etalon r 0, nonogram_etalon r 1, nonogram_etalon r 2, nonogram_etalon r 3]

-- Runtime check: witness matches all run clues.
#guard nonoCheck (nonoSol : Fin 4 → Fin 4 → Bool)

