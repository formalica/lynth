-- Sorted-union problem: synthesize a sorted list holding exactly the
-- elements of either input.
-- TODO: failing until function synthesis over inductive domains lands.
import Lynth

/-- Ascending order (property predicate, in the role of `noAdjDup`). -/
def sortedAsc : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: ys => x ≤ y && sortedAsc (y :: ys)

/-- Sorted union: ascending, containing exactly the elements of `xs` or `ys`. -/
def sortedUnion
    : { f : List Nat → List Nat → List Nat //
        ∀ xs ys, sortedAsc (f xs ys) ∧
          ∀ y, y ∈ f xs ys ↔ y ∈ xs ∨ y ∈ ys } := by
  lynth

/-- info: 'sortedUnion' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sortedUnion
