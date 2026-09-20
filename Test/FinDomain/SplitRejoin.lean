-- Finite-domain pilot: split pair with reverse-equality + sum + nodup halves.
-- Spec over `(p.1, p.2)`: halves are reverses of each other, join sums to
-- 10, each half nodup. Neither half-length is stated: `p.1.reverse = p.2`
-- forces equal half-lengths (inferred, never given); `++` element-union +
-- sum + per-half nodup then pin the values (finiteness falls out of
-- sum = 10 with distinct elements per half — no explicit length anywhere).
-- TODO: failing until multi-property list synthesis lands in the pipeline.
import Lynth

/-- Target property: reverse-equal halves, total sum, nodup halves. -/
def srValid (p : List Nat × List Nat) : Prop :=
  p.1.reverse = p.2 ∧ (p.1 ++ p.2).sum = 10 ∧ p.1.Nodup ∧ p.2.Nodup

/-- Computable check (mirrors `srValid`). -/
def srCheck (p : List Nat × List Nat) : Bool :=
  decide (p.1.reverse = p.2) &&
  decide ((p.1 ++ p.2).sum = 10) &&
  decide p.1.Nodup && decide p.2.Nodup

/-- The goal `lynth` must fill: the split pair. -/
def srSol : { p : List Nat × List Nat // srValid p } := by
  lynth

/-- Etalon: halves [1, 4] / [4, 1]; join sums to 10, halves nodup. -/
def etalon : List Nat × List Nat := ([1, 4], [4, 1])

-- The value computed by `lynth`:
#eval (srSol : List Nat × List Nat)

-- The etalon:
#eval etalon

-- Runtime check: witness satisfies the split properties.
#guard srCheck (srSol : List Nat × List Nat)

/-- info: 'srSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms srSol
