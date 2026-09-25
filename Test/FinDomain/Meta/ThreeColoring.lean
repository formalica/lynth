import Lynth

namespace FinDomain.Meta

/-- An arbitrary graph on eight vertices. -/
def Graph := Fin 8 → Fin 8 → Bool

/-- A candidate three-coloring. -/
def Coloring := Fin 8 → Fin 3

def ColoringValid (g : Graph) (c : Coloring) : Prop :=
  ∀ i j, g i j = true → c i ≠ c j

def CorrectColoringSolver
    (solver : Graph → Option Coloring) : Prop :=
  (∀ g c, solver g = some c → ColoringValid g c) ∧
  (∀ g, (∃ c, ColoringValid g c) →
    ∃ c, solver g = some c) ∧
  (∀ g, solver g = none ↔
    ¬∃ c, ColoringValid g c)

def emptyGraph : Graph :=
  fun _ _ => false

def completeGraph : Graph :=
  fun i j => i ≠ j

def oddCycle : Graph :=
  fun i j =>
    (i.val < 7 ∧ j.val = (i.val + 1) % 7) ∨
    (j.val < 7 ∧ i.val = (j.val + 1) % 7)

def pathGraph : Graph :=
  fun i j =>
    j.val = i.val + 1 ∨ i.val = j.val + 1

def starGraph : Graph :=
  fun i j =>
    i ≠ j ∧ (i = 0 ∨ j = 0)

def oddWheel : Graph :=
  fun i j =>
    (i.val = 5 ∧ j.val < 5 ∧ i ≠ j) ∨
    (j.val = 5 ∧ i.val < 5 ∧ i ≠ j) ∨
    (i.val < 5 ∧ j.val < 5 ∧ i ≠ j ∧
      (j.val = (i.val + 1) % 5 ∨
        i.val = (j.val + 1) % 5))

/-- Synthesize a coloring solver for arbitrary input graphs. -/
set_option maxHeartbeats 10000000 in
def coloringSolver :
    { solver : Graph → Option Coloring //
      CorrectColoringSolver solver } := by
  lynth

#guard (coloringSolver.1 emptyGraph).isSome
#guard (coloringSolver.1 completeGraph).isNone
#guard (coloringSolver.1 oddCycle).isSome
#guard (coloringSolver.1 pathGraph).isSome
#guard (coloringSolver.1 starGraph).isSome
#guard (coloringSolver.1 oddWheel).isNone

/-- info: 'FinDomain.Meta.coloringSolver' depends on axioms: [propext] -/
#guard_msgs in
#print axioms coloringSolver

end FinDomain.Meta
