-- Finite-domain pilot: graph 3-coloring over `Fin 3`, asked as ONE
-- `Answer` goal. This instance is UNSAT: K4 needs 4 pairwise-distinct
-- colors (pigeonhole), so `lynth` must fill the `.inr` branch with a
-- proof that no 3-coloring exists.
-- TODO: failing until `Answer` goals are recognized by the pipeline.
import Lynth

/-- One-goal SAT-or-UNSAT question: data + proof, or unsat proof. -/
def Answer (α : Type) (p : α → Prop) : Type :=
  { w : α // p w } ⊕' (∀ x : α, ¬ p x)

/-- K4: every pair of the 4 vertices is adjacent. -/
def k4Coloring (g : Fin 4 → Fin 3) : Prop :=
  g 0 ≠ g 1 ∧ g 0 ≠ g 2 ∧ g 0 ≠ g 3 ∧
  g 1 ≠ g 2 ∧ g 1 ≠ g 3 ∧ g 2 ≠ g 3

/-- One `lynth` run decides: expect `.inr` (K4 is not 3-colorable). -/
def k4No3Col : Answer (Fin 4 → Fin 3) k4Coloring := by
  lynth

/-- info: 'k4No3Col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms k4No3Col
