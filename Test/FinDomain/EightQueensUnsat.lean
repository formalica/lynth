-- Finite-domain pilot: 8-queens over `Fin 8`, asked as ONE goal with
-- the Answer type unfolded. This instance is UNSAT: rows 0 and 1 are
-- forced into columns 0 and 1 (`g 0 = 0 ∧ g 1 = 1`), which share an
-- anti-diagonal (`0 + 7 = 7 = 1 + 6`), so no board satisfies all
-- constraints — `lynth` must fill the `.inr` branch.
-- TODO: failing until this goal shape is recognized by the pipeline.
import Lynth

/-- Column of row `r` as a plain `Nat` (for diagonal arithmetic). -/
def qcol (g : Fin 8 → Fin 8) (r : Fin 8) : Nat := (g r : Nat)

/-- 8-queens validity: columns pairwise distinct (one queen per
column) and no shared diagonal in either direction. -/
def queensValid (g : Fin 8 → Fin 8) : Prop :=
  (∀ r1 : Fin 8, ∀ r2 : Fin 8, r1 ≠ r2 → g r1 ≠ g r2) ∧
  (∀ r1 : Fin 8, ∀ r2 : Fin 8, r1 ≠ r2 →
    qcol g r1 + (r1 : Nat) ≠ qcol g r2 + (r2 : Nat)) ∧
  (∀ r1 : Fin 8, ∀ r2 : Fin 8, r1 ≠ r2 →
    qcol g r1 + (7 - (r1 : Nat)) ≠ qcol g r2 + (7 - (r2 : Nat)))

/-- Forced placements on a shared anti-diagonal: rows 0 and 1 in
columns 0 and 1, conflicting with the diagonal rule. -/
def queensValidClash (g : Fin 8 → Fin 8) : Prop :=
  queensValid g ∧ g 0 = 0 ∧ g 1 = 1

/-- One `lynth` run decides: expect `.inr` (no such board). -/
def queens8No :
    let p := queensValidClash
    { w // p w } ⊕' (∀ x, ¬ p x) := by
  lynth

/-- info: 'queens8No' depends on axioms: [propext] -/
#guard_msgs in
#print axioms queens8No
