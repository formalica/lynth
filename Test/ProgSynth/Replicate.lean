-- Synquid demo/List-Replicate.sq, translated: synthesize `replicate`.
-- TODO: failing until function synthesis over inductive domains lands.
import Lynth

/-- For every type `α`, a function returning `n` copies of `x`. -/
def replicate
    : { rep : (α : Type) → Nat → α → List α //
        ∀ (α : Type) (n : Nat) (x : α),
          (rep α n x).length = n ∧ ∀ y ∈ rep α n x, y = x } := by
  lynth

-- 100 copies of `7`; the 91st element (index 90, `getD` default `0`)
-- must be `7`.
#guard ((replicate.1 Nat 100 7).getD 90 0) = 7

/-- info: 'replicate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms replicate
