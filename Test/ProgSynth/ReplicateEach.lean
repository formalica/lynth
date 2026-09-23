-- Synquid List-Replicate.sq flavor, translated: synthesize
-- `replicateEach` — every element of the list repeated `k` times.
-- TODO: failing until function synthesis over inductive domains lands.
import Lynth

/-- Replicate each: the result multiset is `k` copies of `xs`'s
(one count clause pins multiplicities exactly). -/
def replicateEach
    : { f : Nat → List Nat → List Nat //
        ∀ k xs, ∀ y, (f k xs).count y = k * xs.count y } := by
  lynth

/-- info: 'replicateEach' depends on axioms: [propext] -/
#guard_msgs in
#print axioms replicateEach
