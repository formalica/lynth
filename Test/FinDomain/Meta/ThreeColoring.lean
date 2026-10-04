import Lynth

namespace FinDomain.Meta

set_option maxHeartbeats 10 in
/-- An arbitrary graph on eight vertices. -/
def threeColoring_Graph := Fin 8 → Fin 8 → Bool

set_option maxHeartbeats 10 in
/-- A candidate three-coloring. -/
def Coloring := Fin 8 → Fin 3

set_option maxHeartbeats 13 in
def ColoringValid (g : threeColoring_Graph) (c : Coloring) : Prop :=
  ∀ i j, g i j = true → c i ≠ c j

set_option maxHeartbeats 35 in
def CorrectColoringSolver
    (solver : threeColoring_Graph → Option Coloring) : Prop :=
  (∀ g c, solver g = some c → ColoringValid g c) ∧
  (∀ g, (∃ c, ColoringValid g c) →
    ∃ c, solver g = some c) ∧
  (∀ g, solver g = none ↔
    ¬∃ c, ColoringValid g c)

set_option maxHeartbeats 13 in
def threeColoring_emptyGraph : threeColoring_Graph :=
  fun _ _ => false

set_option maxHeartbeats 27 in
def completeGraph : threeColoring_Graph :=
  fun i j => i ≠ j

set_option maxHeartbeats 155 in
def oddCycle : threeColoring_Graph :=
  fun i j =>
    (i.val < 7 ∧ j.val = (i.val + 1) % 7) ∨
    (j.val < 7 ∧ i.val = (j.val + 1) % 7)

set_option maxHeartbeats 72 in
def pathGraph : threeColoring_Graph :=
  fun i j =>
    j.val = i.val + 1 ∨ i.val = j.val + 1

set_option maxHeartbeats 87 in
def starGraph : threeColoring_Graph :=
  fun i j =>
    i ≠ j ∧ (i = 0 ∨ j = 0)

set_option maxHeartbeats 351 in
def oddWheel : threeColoring_Graph :=
  fun i j =>
    (i.val = 5 ∧ j.val < 5 ∧ i ≠ j) ∨
    (j.val = 5 ∧ i.val < 5 ∧ i ≠ j) ∨
    (i.val < 5 ∧ j.val < 5 ∧ i ≠ j ∧
      (j.val = (i.val + 1) % 5 ∨
        i.val = (j.val + 1) % 5))

set_option maxHeartbeats 146 in
set_option maxHeartbeats 10000000 in
/-- Synthesize a coloring solver for arbitrary input graphs. -/
def coloringSolver :
    { solver : threeColoring_Graph → Option Coloring //
      CorrectColoringSolver solver } := by
  lynth
/-- info: 'FinDomain.Meta.coloringSolver' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lynth.Sat.cdcl_correct,
 Lynth.Sat.cdcl_fuel_suffices] -/
#guard_msgs in
#print axioms coloringSolver

#guard (coloringSolver.1 threeColoring_emptyGraph).isSome
#guard (coloringSolver.1 completeGraph).isNone
#guard (coloringSolver.1 oddCycle).isSome
#guard (coloringSolver.1 pathGraph).isSome
#guard (coloringSolver.1 starGraph).isSome
#guard (coloringSolver.1 oddWheel).isNone


end FinDomain.Meta
