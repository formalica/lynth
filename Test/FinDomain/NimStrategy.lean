-- Finite-domain pilot: winning Nim move with opponent quantification.
-- Pile of 4 stones; a move takes 1 or 2; last taker wins.
-- Spec is ∃∀∃: EXISTS a first move such that FOR ALL opponent replies
-- there EXISTS a finishing take. No existing test has alternating
-- quantifiers — all are single-∃ (or PSum).
-- NOTE: every quantifier ranges over the fixed list [1,2] — finite,
-- so the whole spec expands to a finite check; brute-force applies.
-- TODO: failing until alternating-quantifier synthesis lands in the pipeline.
import Lynth

set_option maxHeartbeats 25 in
/-- Legal takes. -/
def takes : List Nat := [1, 2]

set_option maxHeartbeats 57 in
/-- `m` is a winning first move from a pile of 4. -/
def nimValid (m : Nat) : Prop :=
  m ∈ takes ∧ m ≤ 4 ∧ ∀ r ∈ takes, r ≤ 4 - m → ∃ f ∈ takes, f = 4 - m - r

set_option maxHeartbeats 159 in
/-- Computable check (mirrors `nimValid`). -/
def nimCheck (m : Nat) : Bool :=
  (m == 1 || m == 2) && decide (m ≤ 4) &&
  (takes.all fun r => (!decide (r ≤ 4 - m)) || takes.any fun f => decide (f = 4 - m - r))

set_option maxHeartbeats 361 in
/-- The goal `lynth` must fill: the winning first move. -/
def nimSol : { m : Nat // nimValid m } := by
  lynth
/-- info: 'nimSol' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nimSol

set_option maxHeartbeats 11 in
/-- Etalon: take 1 (leaves 3, a losing position for the opponent). -/
def nimStrategy_etalon : Nat := 1

-- The value computed by `lynth`:
#eval (nimSol : Nat)

-- The nimStrategy_etalon:
#eval nimStrategy_etalon

-- Runtime checks: witness is winning and equals the nimStrategy_etalon (unique). 
#guard nimCheck (nimSol : Nat)
#guard (nimSol : Nat) = nimStrategy_etalon

