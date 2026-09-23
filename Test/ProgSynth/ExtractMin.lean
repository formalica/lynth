-- Synquid List-ExtractMin.sq, translated: synthesize `extractMin`.
-- TODO: failing until function synthesis over inductive domains lands.
import Lynth

/-- Extract the minimum of a nonempty list: the pair holds the same
multiset as `xs`, and every remaining element is ≥ the minimum. -/
def extractMin
    : { f : { xs : List Nat // xs ≠ [] } → Nat × List Nat //
        ∀ xs, xs.val.Perm ((f xs).1 :: (f xs).2) ∧
          ∀ y ∈ (f xs).2, (f xs).1 ≤ y } := by
  lynth

/-- info: 'extractMin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms extractMin
