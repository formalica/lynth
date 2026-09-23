-- Synquid List-Intersection.sq (`coincidence`), translated:
-- synthesize the list of elements common to both inputs.
-- TODO: failing until function synthesis over inductive domains lands.
import Lynth

/-- Intersection: exactly the elements present in both lists. -/
def intersection
    : { f : List Nat → List Nat → List Nat //
        ∀ xs ys, ∀ y, y ∈ f xs ys ↔ y ∈ xs ∧ y ∈ ys } := by
  lynth

/-- info: 'intersection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms intersection
