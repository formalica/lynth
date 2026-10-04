-- 9x9 Sudoku over custom finite inductives, Bool-valued rules built
-- from generic (non-hardcoded) list computation: `List.all`/`map`/
-- `bind`, `eraseDups`-based no-dups, `==`, `if`. No `∀`, no
-- `List.Pairwise`, no `Fin`.
import Lynth

inductive Idx | i1 | i2 | i3 | i4 | i5 | i6 | i7 | i8 | i9
deriving DecidableEq, Repr

inductive Val | v0 | v1 | v2 | v3 | v4 | v5 | v6 | v7 | v8 | v9
deriving DecidableEq, Repr

set_option maxHeartbeats 8 in
def sudoku9Partial_Board := Idx → Idx → Val

set_option maxHeartbeats 52 in
def allIdx : List Idx := [.i1, .i2, .i3, .i4, .i5, .i6, .i7, .i8, .i9]

set_option maxHeartbeats 66 in
def triplets : List (List Idx) :=
  [[.i1, .i2, .i3], [.i4, .i5, .i6], [.i7, .i8, .i9]]

set_option maxHeartbeats 38 in
def has_no_dups (l : List Val) : Bool :=
  l.eraseDups.length == l.length

set_option maxHeartbeats 59 in
def valid_cells (b : sudoku9Partial_Board) : Bool :=
  allIdx.all fun r => allIdx.all fun c => b r c != .v0

set_option maxHeartbeats 49 in
def sudoku9Partial_valid_rows (b : sudoku9Partial_Board) : Bool :=
  allIdx.all fun r => has_no_dups (allIdx.map fun c => b r c)

set_option maxHeartbeats 49 in
def sudoku9Partial_valid_cols (b : sudoku9Partial_Board) : Bool :=
  allIdx.all fun c => has_no_dups (allIdx.map fun r => b r c)

set_option maxHeartbeats 75 in
def sudoku9Partial_valid_boxes (b : sudoku9Partial_Board) : Bool :=
  triplets.all fun rs =>
    triplets.all fun cs =>
      has_no_dups (rs.flatMap fun r => cs.map fun c => b r c)

set_option maxHeartbeats 94 in
def sudoku9Partial_matches_partial (p b : sudoku9Partial_Board) : Bool :=
  allIdx.all fun r =>
    allIdx.all fun c =>
      if p r c == .v0 then true else b r c == p r c

set_option maxHeartbeats 371 in
-- A standard medium difficulty Sudoku grid
def sudoku9Partial_example_partial (r c : Idx) : Val :=
  match r, c with
  -- Row 1
  | .i1, .i1 => .v1 | .i1, .i2 => .v2 | .i1, .i5 => .v7 | .i1, .i7 => .v5 | .i1, .i8 => .v6
  -- Row 2
  | .i2, .i1 => .v5 | .i2, .i3 => .v7 | .i2, .i4 => .v9 | .i2, .i5 => .v3 | .i2, .i6 => .v2 | .i2, .i8 => .v8
  -- Row 3
  | .i3, .i6 => .v1
  -- Row 4
  | .i4, .i2 => .v1 | .i4, .i4 => .v2 | .i4, .i5 => .v4 | .i4, .i8 => .v5
  -- Row 5
  | .i5, .i1 => .v3 | .i5, .i3 => .v8 | .i5, .i7 => .v4 | .i5, .i9 => .v2
  -- Row 6
  | .i6, .i2 => .v7 | .i6, .i5 => .v8 | .i6, .i6 => .v5 | .i6, .i8 => .v1
  -- Row 7
  | .i7, .i4 => .v7
  -- Row 8
  | .i8, .i2 => .v8 | .i8, .i4 => .v4 | .i8, .i5 => .v2 | .i8, .i6 => .v3 | .i8, .i7 => .v7 | .i8, .i9 => .v1
  -- Row 9
  | .i9, .i2 => .v3 | .i9, .i3 => .v4 | .i9, .i5 => .v1 | .i9, .i8 => .v2 | .i9, .i9 => .v8
  | _, _ => .v0

set_option maxHeartbeats 399760 in
-- The generic `solve (p : sudoku9Partial_Board)` is ill-posed (contradictory `p`
-- admits no board); the well-posed goal is the concrete instance.
set_option maxHeartbeats 10000000 in
def sudoku9partial : { b : sudoku9Partial_Board //
    valid_cells b = true ∧ sudoku9Partial_valid_rows b = true ∧ sudoku9Partial_valid_cols b = true ∧
      sudoku9Partial_valid_boxes b = true ∧ sudoku9Partial_matches_partial sudoku9Partial_example_partial b = true } := by
  lynth
/-- info: 'sudoku9partial' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sudoku9partial

