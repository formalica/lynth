-- Finite-domain pilot: 8-queens over `Fin 8`, asked as ONE goal with
-- the Answer type unfolded: `lynth` decides solvability and fills
-- either the computable data branch (`.inl`) or the refutation
-- branch (`.inr`).
-- This instance is SAT: a valid 8-queens board exists.
-- TODO: failing until this goal shape is recognized by the pipeline.
import Lynth

/-- Column of row `r` as a plain `Nat` (for diagonal arithmetic). -/
def qcol (g : Fin 8 → Fin 8) (r : Fin 8) : Nat := (g r : Nat)

/-- 8-queens validity: columns pairwise distinct (one queen per
column) and no shared diagonal in either direction
(`col + row` and `col + (7 - row)` invariants). -/
def queensValid (g : Fin 8 → Fin 8) : Prop :=
  (∀ r1 : Fin 8, ∀ r2 : Fin 8, r1 ≠ r2 → g r1 ≠ g r2) ∧
  (∀ r1 : Fin 8, ∀ r2 : Fin 8, r1 ≠ r2 →
    qcol g r1 + (r1 : Nat) ≠ qcol g r2 + (r2 : Nat)) ∧
  (∀ r1 : Fin 8, ∀ r2 : Fin 8, r1 ≠ r2 →
    qcol g r1 + (7 - (r1 : Nat)) ≠ qcol g r2 + (7 - (r2 : Nat)))

/-- One `lynth` run decides: expect `.inl` (a board exists). -/
def queens8 :
    let p := queensValid
    { w // p w } ⊕' (∀ x, ¬ p x) := by
  lynth

/-- info: 'queens8' depends on axioms: [propext] -/
#guard_msgs in
#print axioms queens8
