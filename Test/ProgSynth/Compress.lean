-- Synquid List-Compress.sq, translated: synthesize `compress`.
-- TODO: failing until function synthesis over inductive domains lands.
import Lynth

/-- No two adjacent elements equal. -/
def noAdjDup : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: ys => x != y && noAdjDup (y :: ys)

/-- Compress: same elements as `xs`, with adjacent elements pairwise distinct. -/
def compress
    : { f : List Nat → List Nat //
        ∀ xs, noAdjDup (f xs) ∧ ∀ y, y ∈ f xs ↔ y ∈ xs } := by
  lynth

/-- info: 'compress' depends on axioms: [propext] -/
#guard_msgs in
#print axioms compress
