-- Finite-domain pilot: graph 3-coloring over `Fin 3`, asked as ONE
-- `Answer` goal: `lynth` decides solvability and fills either the
-- computable data branch (`.inl`) or the refutation branch (`.inr`).
-- This instance is SAT: triangle (0,1,2) + pendant edge (0,3) is
-- 3-colorable (triangle uses all three colors; vertex 3 avoids
-- vertex 0's color).
-- TODO: failing until `Answer` goals are recognized by the pipeline.
import Lynth

/-- One-goal SAT-or-UNSAT question: data + proof, or unsat proof. -/
def Answer (α : Type) (p : α → Prop) : Type :=
  { w : α // p w } ⊕' (∀ x : α, ¬ p x)

/-- Triangle edges (0,1),(0,2),(1,2) plus pendant edge (0,3). -/
def triPendantColoring (g : Fin 4 → Fin 3) : Prop :=
  g 0 ≠ g 1 ∧ g 0 ≠ g 2 ∧ g 1 ≠ g 2 ∧ g 0 ≠ g 3

/-- One `lynth` run decides: expect `.inl` (coloring exists). -/
def triPendant3Col : Answer (Fin 4 → Fin 3) triPendantColoring := by
  lynth

/-- info: 'triPendant3Col' depends on axioms: [propext] -/
#guard_msgs in
#print axioms triPendant3Col
