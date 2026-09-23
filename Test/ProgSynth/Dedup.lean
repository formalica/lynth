-- Synquid List-Nub.sq, translated: synthesize `dedup` — a
-- duplicate-free list with the same elements as the input.
-- TODO: failing until function synthesis over inductive domains lands.
import Lynth

/-- Dedup: duplicate-free, holding exactly the elements of `xs`
(order unconstrained, Synquid set semantics). -/
def dedup
    : { f : List Nat → List Nat //
        ∀ xs, (f xs).Nodup ∧ ∀ y, y ∈ f xs ↔ y ∈ xs } := by
  lynth

/-- info: 'dedup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms dedup
