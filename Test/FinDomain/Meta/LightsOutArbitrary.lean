import Lynth

namespace FinDomain.Meta

/-- An arbitrary square Lights Out board. -/
def LightsBoard (n : ℕ) := Fin n → Fin n → Bool

def adjDiff (a b : ℕ) : ℕ :=
  if a ≤ b then b - a else a - b

/-- Whether pressing `(i, j)` toggles the cell `(r, c)`. -/
def toggles (n : ℕ) (i j r c : Fin n) : Bool :=
  (r = i ∧ c = j) ∨
  (r = i ∧ adjDiff c.val j.val = 1) ∨
  (c = j ∧ adjDiff r.val i.val = 1)

/-- Apply a complete press pattern to an input board. -/
def applyAll
    (input presses : LightsBoard n) : LightsBoard n :=
  fun i j =>
    (List.finRange n).foldl
      (fun acc r =>
        (List.finRange n).foldl
          (fun acc c =>
            acc != (presses r c && toggles n r c i j))
          acc)
      (input i j)

/-- A press pattern solves the board when every final light is off. -/
def LightsOutSolved
    (input presses : LightsBoard n) : Prop :=
  ∀ i j, applyAll input presses i j = false

/-- Correctness of a total Lights Out solver. -/
def CorrectLightsOutSolver
    (n : ℕ) (solver : LightsBoard n → Option (LightsBoard n)) : Prop :=
  (∀ input presses,
    solver input = some presses →
    LightsOutSolved input presses) ∧
  (∀ input,
    (∃ presses, LightsOutSolved input presses) →
    ∃ presses, solver input = some presses) ∧
  (∀ input,
    solver input = none ↔
    ¬∃ presses, LightsOutSolved input presses)

/-- Synthesize a solver for every square board size. -/
set_option maxHeartbeats 10000000 in
def lightsOutSolver :
    (n : ℕ) →
      { solver : LightsBoard n → Option (LightsBoard n) //
        CorrectLightsOutSolver n solver } := by
  lynth

def emptyBoard (n : ℕ) : LightsBoard n :=
  fun _ _ => false

def onePress (n : ℕ) : LightsBoard n :=
  fun i j => i.val = 0 && j.val = 0

/-- A guaranteed-solvable board generated from a known press pattern. -/
def solvableInput (n : ℕ) : LightsBoard n :=
  applyAll (emptyBoard n) (onePress n)

#guard ((lightsOutSolver 5).1 (solvableInput 5)).isSome
#guard ((lightsOutSolver 8).1 (solvableInput 8)).isSome

/-- info: 'FinDomain.Meta.lightsOutSolver' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lightsOutSolver

end FinDomain.Meta
