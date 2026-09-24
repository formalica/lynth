-- Finite-domain pilot: inductive safety invariant.
-- Counter 0..3, init 0, step +1 capped at 2 (state 3 is unreachable),
-- unsafe state 3.
-- Witness is a PREDICATE `inv : Fin 4 → Bool`: holds at init,
-- preserved by step, implies safety. A property, not data reaching
-- a goal — unlike every other pilot.
-- NOTE: `lynth` should infer finiteness: 2^4 = 16 predicates, each
-- checked by ∀ over `Fin 4` — brute-force applies.
-- TODO: failing until predicate-with-implications synthesis lands in the pipeline.
import Lynth

/-- Step: increment, capped at 2 (state 3 stays unreachable). -/
def step (s : Fin 4) : Fin 4 :=
  ⟨Nat.min (s.val + 1) 2, Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)⟩

/-- `inv` is a safety invariant: init, preservation, safety. -/
def invValid (inv : Fin 4 → Bool) : Prop :=
  inv 0 = true ∧
  (∀ s : Fin 4, inv s = true → inv (step s) = true) ∧
  (∀ s : Fin 4, inv s = true → s ≠ 3)

/-- All states, for computable checks. -/
def states : List (Fin 4) := [0, 1, 2, 3]

/-- Computable check (mirrors `invValid`). -/
def invCheck (inv : Fin 4 → Bool) : Bool :=
  (inv 0) &&
  (states.all fun s => (!inv s) || inv (step s)) &&
  (states.all fun s => (!inv s) || (s.val != 3))

/-- The goal `lynth` must fill: the invariant predicate. -/
def invSol : { inv : Fin 4 → Bool // invValid inv } := by
  lynth

/-- Etalon: the reachable safe states 0,1,2 (state 3 is unreachable
    and excluded; closure holds since step caps at 2). -/
def etalon : Fin 4 → Bool := fun s => s.val < 3

-- The value computed by `lynth`:
#eval (invSol : Fin 4 → Bool)

-- The etalon (reachable safe states):
#eval states.map etalon

-- Runtime check: witness is a valid invariant.
#guard invCheck (invSol : Fin 4 → Bool)

/-- info: 'invSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms invSol
