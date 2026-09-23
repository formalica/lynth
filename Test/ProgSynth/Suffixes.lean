-- Suffixes problem (Synquid list-suite flavor): synthesize `suffixes`,
-- the list of all suffixes of the input.
-- TODO: failing until function synthesis over inductive domains lands.
import Lynth

/-- Suffixes: exactly the suffixes of `xs` (set membership, order of
the outer list unconstrained). -/
def suffixes
    : { f : List Nat → List (List Nat) //
        ∀ xs ys, ys ∈ f xs ↔ ∃ zs, xs = zs ++ ys } := by
  lynth

/-- info: 'suffixes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms suffixes
