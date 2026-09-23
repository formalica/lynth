-- Synquid List-Split.sq, translated: synthesize `split` — halve a
-- list into two near-equal halves holding the same multiset.
-- TODO: failing until function synthesis over inductive domains lands.
import Lynth

/-- Split: the halves rebuild `xs` as a permutation, and their lengths
halve `xs`'s (Synquid's `abs (len xs - 2 * len (fst _v)) <= 1`). -/
def split
    : { f : List Nat → List Nat × List Nat //
        ∀ xs, xs.Perm ((f xs).1 ++ (f xs).2) ∧
          (2 * (f xs).1.length = xs.length ∨ 2 * (f xs).1.length + 1 = xs.length) } := by
  lynth

/-- info: 'split' depends on axioms: [propext] -/
#guard_msgs in
#print axioms split
