-- Set-union twin of Synquid List-Intersection.sq: synthesize the
-- union of two element sets.
-- TODO: failing until function synthesis over inductive domains lands.
import Lynth

/-- Union: exactly the elements present in either list. -/
def union
    : { f : List Nat → List Nat → List Nat //
        ∀ xs ys, ∀ y, y ∈ f xs ys ↔ y ∈ xs ∨ y ∈ ys } := by
  lynth

/-- info: 'union' depends on axioms: [propext] -/
#guard_msgs in
#print axioms union
