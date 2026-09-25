import Lynth

namespace FinDomain.Meta

/-- An arbitrary directed graph on `n` vertices. -/
def Graph (n : ℕ) := Fin n → Fin n → Bool

/-- A candidate successor tour on `Fin n`. -/
def Tour (n : ℕ) := Fin n → Fin n

/-- A valid tour is an injective successor map whose edges belong to the graph. -/
def TourValid (n : ℕ) (g : Graph n) (t : Tour n) : Prop :=
  Function.Injective t ∧
  ∀ i : Fin n, g i (t i) = true

/-- Correctness of a total solver specialized to `Fin n`. -/
def CorrectTourSolver
    (n : ℕ) (solver : Graph n → Option (Tour n)) : Prop :=
  (∀ g t, solver g = some t → TourValid n g t) ∧
  (∀ g, (∃ t, TourValid n g t) →
    ∃ t, solver g = some t) ∧
  (∀ g, solver g = none ↔
    ¬∃ t, TourValid n g t)

/-- A directed cycle on `n` vertices. -/
def cycleGraph (n : ℕ) : Graph n :=
  fun i j =>
    if n = 0 then
      false
    else
      j.val = (i.val + 1) % n

/-- A graph with no edges. -/
def emptyGraph (n : ℕ) : Graph n :=
  fun _ _ => false

/-- Synthesize a solver for every finite size. -/
set_option maxHeartbeats 10000000 in
def tourSolver :
    (n : ℕ) →
      { solver : Graph n → Option (Tour n) //
        CorrectTourSolver n solver } := by
  lynth

#guard ((tourSolver 12).1 (cycleGraph 12)).isSome
#guard ((tourSolver 8).1 (emptyGraph 8)).isNone

/-- info: 'FinDomain.Meta.tourSolver' depends on axioms: [propext] -/
#guard_msgs in
#print axioms tourSolver

end FinDomain.Meta
