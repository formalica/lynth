-- Finite-domain pilot: reverse + map + sum + nodup chain.
-- Spec: `l.reverse.map (· + 1) = [4, 3, 2] ∧ l.sum = 6 ∧ l.Nodup`.
-- `lynth` must combine: reverse is length-preserving + order-flipping,
-- map image inversion (`· + 1` ⇒ preimage values), sum coupling, and
-- nodup finiteness. No length or element is stated anywhere.
-- The length-preservation baseline of this batch (covered once only).
-- TODO: failing until multi-property list synthesis lands in the pipeline.
import Lynth

/-- Target property: reversed+incremented image, sum, nodup. -/
def rmcValid (l : List Nat) : Prop :=
  l.reverse.map (· + 1) = [4, 3, 2] ∧ l.sum = 6 ∧ l.Nodup

/-- Computable check (mirrors `rmcValid`). -/
def rmcCheck (l : List Nat) : Bool :=
  decide (l.reverse.map (· + 1) = [4, 3, 2]) &&
  decide (l.sum = 6) && decide l.Nodup

/-- The goal `lynth` must fill: the preimage list. -/
def rmcSol : { l : List Nat // rmcValid l } := by
  lynth

/-- Etalon: [1, 2, 3] — reverse gives [3,2,1], +1 gives [4,3,2]. -/
def etalon : List Nat := [1, 2, 3]

-- The value computed by `lynth`:
#eval (rmcSol : List Nat)

-- The etalon:
#eval etalon

-- Runtime check: witness satisfies the chained properties.
#guard rmcCheck (rmcSol : List Nat)

/-- info: 'rmcSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms rmcSol
