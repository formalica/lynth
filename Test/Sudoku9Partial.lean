-- 9x9 Sudoku over custom finite inductives, Bool-valued rules built
-- from generic (non-hardcoded) list computation: `List.all`/`map`/
-- `bind`, `eraseDups`-based no-dups, `==`, `if`. No `∀`, no
-- `List.Pairwise`, no `Fin`.
import Lynth

inductive Idx | i1 | i2 | i3 | i4 | i5 | i6 | i7 | i8 | i9
deriving DecidableEq, Repr

inductive Val | v0 | v1 | v2 | v3 | v4 | v5 | v6 | v7 | v8 | v9
deriving DecidableEq, Repr

def Board := Idx → Idx → Val

def allIdx : List Idx := [.i1, .i2, .i3, .i4, .i5, .i6, .i7, .i8, .i9]

def triplets : List (List Idx) :=
  [[.i1, .i2, .i3], [.i4, .i5, .i6], [.i7, .i8, .i9]]

def has_no_dups (l : List Val) : Bool :=
  l.eraseDups.length == l.length

def valid_cells (b : Board) : Bool :=
  allIdx.all fun r => allIdx.all fun c => b r c != .v0

def valid_rows (b : Board) : Bool :=
  allIdx.all fun r => has_no_dups (allIdx.map fun c => b r c)

def valid_cols (b : Board) : Bool :=
  allIdx.all fun c => has_no_dups (allIdx.map fun r => b r c)

def valid_boxes (b : Board) : Bool :=
  triplets.all fun rs =>
    triplets.all fun cs =>
      has_no_dups (rs.flatMap fun r => cs.map fun c => b r c)

def matches_partial (p b : Board) : Bool :=
  allIdx.all fun r =>
    allIdx.all fun c =>
      if p r c == .v0 then true else b r c == p r c

-- A standard medium difficulty Sudoku grid
def example_partial (r c : Idx) : Val :=
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

-- The generic `solve (p : Board)` is ill-posed (contradictory `p`
-- admits no board); the well-posed goal is the concrete instance.
set_option maxHeartbeats 10000000 in
def sudoku9partial : { b : Board //
    valid_cells b = true ∧ valid_rows b = true ∧ valid_cols b = true ∧
      valid_boxes b = true ∧ matches_partial example_partial b = true } := by
  lynth

#print axioms sudoku9partial
