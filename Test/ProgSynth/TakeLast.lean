-- Take-last problem (Synquid List-Take/Drop flavor): synthesize
-- `takeLast` — the last `k` elements of a list.
-- TODO: failing until function synthesis over inductive domains lands.
import Lynth

/-- Take last: a suffix of `xs` of length `min k xs.length`. -/
def takeLast
    : { f : Nat → List Nat → List Nat //
        ∀ k xs, ∃ zs, xs = zs ++ f k xs ∧ (f k xs).length = min k xs.length } := by
  lynth

/-- info: 'takeLast' depends on axioms: [propext] -/
#guard_msgs in
#print axioms takeLast
