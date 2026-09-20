-- Finite-domain pilot: graph isomorphism.
-- Two explicit 4-vertex graphs (a path 0-1-2-3 vs the permuted edges
-- 2-0, 0-3, 3-1): witness is a BIJECTION π preserving edges BOTH ways
-- (u~v ↔ π u ~' π v). Relational preservation, not inequality/injection alone.
-- NOTE: 4! = 24 bijections over Fin 4 — finite; brute-force applies.
-- TODO: failing until bijection-with-preservation synthesis lands in the pipeline.
import Lynth

/-- Path graph edges: 0-1-2-3 (symmetric, as a check). -/
def edgeA (u v : Fin 4) : Bool :=
  (u.val == 0 && v.val == 1) || (u.val == 1 && v.val == 0) ||
  (u.val == 1 && v.val == 2) || (u.val == 2 && v.val == 1) ||
  (u.val == 2 && v.val == 3) || (u.val == 3 && v.val == 2)

/-- Image of the path under π = [2,0,3,1]: edges (2,0),(0,3),(3,1). -/
def edgeB (u v : Fin 4) : Bool :=
  (u.val == 2 && v.val == 0) || (u.val == 0 && v.val == 2) ||
  (u.val == 0 && v.val == 3) || (u.val == 3 && v.val == 0) ||
  (u.val == 3 && v.val == 1) || (u.val == 1 && v.val == 3)

/-- π is an isomorphism: bijective and edge-preserving both ways. -/
def isoValid (f : Fin 4 → Fin 4) : Prop :=
  (∀ u v : Fin 4, u ≠ v → f u ≠ f v) ∧
  (∀ u v : Fin 4, edgeA u v = edgeB (f u) (f v))

/-- All vertices, for computable checks. -/
def verts : List (Fin 4) := [0, 1, 2, 3]

/-- Computable check (mirrors `isoValid`). -/
def isoCheck (f : Fin 4 → Fin 4) : Bool :=
  (verts.all fun u => verts.all fun v =>
    (u == v) || (f u != f v)) &&
  (verts.all fun u => verts.all fun v =>
    (edgeA u v == edgeB (f u) (f v)))

/-- The goal `lynth` must fill: the isomorphism map. -/
def isoSol : { f : Fin 4 → Fin 4 // isoValid f } := by
  lynth

/-- Etalon: π = [2,0,3,1] mapping path 0-1-2-3 onto 2-0-3-1. -/
def etalon : Fin 4 → Fin 4 := fun v =>
  match v.val with
  | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1

-- The value computed by `lynth`:
#eval (isoSol : Fin 4 → Fin 4)

-- The etalon images:
#eval verts.map fun v => (etalon v).val

-- Runtime check: witness is a valid isomorphism.
#guard isoCheck (isoSol : Fin 4 → Fin 4)

/-- info: 'isoSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms isoSol
