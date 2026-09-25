-- Finite-domain pilot: shortest path in a small undirected graph.
-- Vertices: Fin 6. Edges (symmetric): 0-1, 0-2, 1-3, 2-3, 2-4, 3-5, 4-5.
-- Source 0, target 5. Witness is a duplicate-free vertex list with
-- consecutive vertices adjacent, plus "no shorter valid path exists"
-- (length minimality), so the witness must be a shortest path.
-- NOTE: `lynth` should infer finiteness: every candidate path is a
-- duplicate-free list over a known finite vertex type, so the search
-- space is finite and brute-force enumeration applies.
-- TODO: failing until path-style relational search lands in the pipeline.
import Lynth

/-- Undirected adjacency as a computable check. -/
def adj (u v : Fin 6) : Bool :=
  (u.val == 0 && v.val == 1) || (u.val == 1 && v.val == 0) ||
  (u.val == 0 && v.val == 2) || (u.val == 2 && v.val == 0) ||
  (u.val == 1 && v.val == 3) || (u.val == 3 && v.val == 1) ||
  (u.val == 2 && v.val == 3) || (u.val == 3 && v.val == 2) ||
  (u.val == 2 && v.val == 4) || (u.val == 4 && v.val == 2) ||
  (u.val == 3 && v.val == 5) || (u.val == 5 && v.val == 3) ||
  (u.val == 4 && v.val == 5) || (u.val == 5 && v.val == 4)

/-- Consecutive vertices are pairwise adjacent (chain check). -/
def chainAdj : List (Fin 6) → Bool
  | [] => true
  | [_] => true
  | u :: v :: rest => adj u v && chainAdj (v :: rest)

/-- Valid path: starts at 0, ends at 5, no vertex repeats,
consecutive vertices adjacent. -/
def validPath (p : List (Fin 6)) : Prop :=
  p.head? = some 0 ∧ p.getLast? = some 5 ∧
  p.Nodup ∧ chainAdj p = true

/-- Computable validity check (mirrors `validPath`). -/
def validPathCheck (p : List (Fin 6)) : Bool :=
  match p.head?, p.getLast? with
  | some s, some t =>
    s.val == 0 && t.val == 5 && ((p.map Fin.val).eraseDups.length == p.length) && chainAdj p
  | _, _ => false

/-- Goal: a shortest path — valid, and no shorter valid path exists. -/
def spSol : { p : List (Fin 6) //
    validPath p ∧ ∀ q : List (Fin 6), validPath q → p.length ≤ q.length } := by
  lynth

/-- Etalon: the shortest path 0-2-4-5 (3 edges).
    (0-1-3-5 is the other shortest one; any valid shortest path
    passes the guards.) -/
def etalon : List (Fin 6) := [0, 2, 4, 5]

-- The value computed by `lynth`:
#eval (spSol : List (Fin 6))

-- The etalon:
#eval etalon

-- Runtime checks: witness is a valid shortest path.
#guard validPathCheck (spSol : List (Fin 6))
#guard (spSol : List (Fin 6)).length == 4

/-- info: 'spSol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spSol
