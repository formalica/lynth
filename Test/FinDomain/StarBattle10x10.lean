import Lynth
import Mathlib.Data.Fintype.Card

abbrev Board := Fin 10 → Fin 10 → Bool

-- 1. Region Map: Maps each cell in the 10x10 grid to one of 10 regions (0 to 9)
--    Puzzle: 10x10 2-star Star Battle by 2557_letters
--    (puzz.link / PZPRV3 id: starbattle/10/10/2/0g4hi22n1j9ln2ccgi1oq84f3ol68m6870fi)
--    Uniqueness of the solution checked with Z3 (z3/solve_starbattle.py).
def regionID : Fin 10 → Fin 10 → Fin 10
  | 0, c => if c.val < 6 then 0 else 1
  | 1, c => if c.val < 4 then 0 else if c.val < 7 then 2 else 1
  | 2, c => if c.val < 2 then 3 else if c.val < 3 then 0 else if c.val < 6 then 2 else 1
  | 3, c => if c.val < 2 then 3 else if c.val < 7 then 2 else if c.val < 9 then 4 else 5
  | 4, c => if c.val < 2 then 3 else if c.val < 3 then 2 else if c.val < 4 then 3 else if c.val < 9 then 4 else 5
  | 5, c => if c.val < 1 then 6 else if c.val < 4 then 3 else if c.val < 5 then 7 else if c.val < 7 then 4 else 5
  | 6, c => if c.val < 1 then 6 else if c.val < 2 then 8 else if c.val < 4 then 3 else if c.val < 6 then 7 else if c.val < 7 then 4 else if c.val < 9 then 9 else 5
  | 7, c => if c.val < 1 then 6 else if c.val < 2 then 8 else if c.val < 6 then 7 else if c.val < 9 then 9 else 5
  | 8, c => if c.val < 1 then 6 else if c.val < 5 then 8 else if c.val < 6 then 7 else if c.val < 9 then 9 else 5
  | 9, c => if c.val < 5 then 6 else if c.val < 8 then 9 else 5

-- 2. Formal rules for 10x10 2-Star Battle
def valid10x10 (s : Board) : Prop :=
  -- Exactly 2 stars per Row
  (∀ r : Fin 10, Fintype.card { c : Fin 10 // s r c = true } = 2) ∧
  -- Exactly 2 stars per Column
  (∀ c : Fin 10, Fintype.card { r : Fin 10 // s r c = true } = 2) ∧
  -- Exactly 2 stars per Region
  (∀ k : Fin 10, Fintype.card { p : Fin 10 × Fin 10 // regionID p.1 p.2 = k ∧ s p.1 p.2 = true } = 2) ∧
  -- Non-adjacency constraint (no horizontal, vertical, or diagonal contact)
  (∀ r1 c1 r2 c2 : Fin 10, (r1, c1) ≠ (r2, c2) →
    (r1.val : Int) - r2.val ∈ ([-1, 0, 1] : List Int) →
    (c1.val : Int) - c2.val ∈ ([-1, 0, 1] : List Int) →
    ¬(s r1 c1 ∧ s r2 c2))

-- 3. Solved board synthesis & verification using lynth
set_option maxHeartbeats 10000000 in
def solveStarBattle10x10 : { s : Board // valid10x10 s } := by
  lynth

/-- info: 'solveStarBattle10x10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solveStarBattle10x10
