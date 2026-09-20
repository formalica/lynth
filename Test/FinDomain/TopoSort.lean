-- Finite-domain pilot: topological sort of a small DAG over `Fin 6`,
-- asked as ONE goal with the Answer type unfolded.
-- Edges: 0<1, 0<2, 1<3, 2<3, 3<4 (vertex 5 isolated).
-- A solution is an injective rank function with every edge going
-- strictly up in rank.
-- This instance is SAT.
-- TODO: failing until `Answer` goals are recognized by the pipeline.
import Lynth

/-- DAG edges: `u < v` (precedence). -/
def edge (u v : Fin 6) : Prop :=
  (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 3) ∨
  (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 4)

/-- A topological ranking: injective, and ranks increase along
every edge. -/
def topoValid (r : Fin 6 → Fin 6) : Prop :=
  (∀ u v : Fin 6, edge u v → r u < r v) ∧
  (∀ u v : Fin 6, u ≠ v → r u ≠ r v)

/-- One `lynth` run decides: expect `.inl` (a topo order exists). -/
def topoRank :
    let p := topoValid
    { w // p w } ⊕' (∀ x, ¬ p x) := by
  lynth

/-- info: 'topoRank' depends on axioms: [propext] -/
#guard_msgs in
#print axioms topoRank
