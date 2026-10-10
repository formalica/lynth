import Mathlib
import Lynth

open Lynth.Interval
open Lynth.Interval.Fns

-- Hypergeometric interval checks run native (per-declaration native axioms),
-- as in `Test/Interval/Zeta.lean`: analytic bounds are `sorry`'d and the
-- enclosures are wide enough that kernel certification recurses too deep.
set_option lynth.interval.trust "native"

/-! # Generalized hypergeometric `pFq` (H1–H14).

General engine (`Fns/Hypgeom.lean`): term recurrence + tail widening.
Ground truths are closed forms (`₂F₁(1,1;2;z) = -ln(1-z)/z`,
`₁F₁(2;3;1) = 2`, `₀F₁(;1/2;1/4) = cosh 1`), parameter
cancellation (`₃F₂(1,1,2;2,2;z) = ₂F₁(1,1;2;z)`), terminating prefixes
(`₇/₁₂`, `₇/₉`), and direct-series cross-checks in Python (`H9`, `H11`,
`H12`, `H13`).  Analytic bounds are `sorry`'d (mirrored Mathlib-only in
`/tmp/pfq_thm.lean` for the external prover).
-/

set_option maxHeartbeats 1476 in
-- H1: ₂F₁(1,1;2;-1/2) = 2ln(3/2). 0.8109302162
def hyp_2f1_neg : { x : Rat //
    abs (pfq21 1 1 2 (-1 / 2) - x) < 1 / 1000000 } := by
  lynth
#print axioms hyp_2f1_neg
#eval! hyp_2f1_neg.1

set_option maxHeartbeats 1348 in
-- H2: ₂F₁(1,1;2;1/2) = 2ln2. 1.3862943611
def hyp_2f1_pos : { x : Rat //
    abs (pfq21 1 1 2 (1 / 2) - x) < 1 / 1000000 } := by
  lynth
#print axioms hyp_2f1_pos
#eval! hyp_2f1_pos.1

set_option maxHeartbeats 1273 in
-- H3: ₂F₁(-2,1;2;1/2) = 7/12, terminating. 0.583333
def hyp_2f1_term : { x : Rat //
    abs (pfq21 (-2) 1 2 (1 / 2) - x) < 1 / 1000000 } := by
  lynth
#print axioms hyp_2f1_term
#eval! hyp_2f1_term.1

set_option maxHeartbeats 1117 in
-- H4: ₂F₁(1,2;3;0) = 1.
def hyp_2f1_zero : { x : Rat //
    abs (pfq21 1 2 3 0 - x) < 1 / 1000000 } := by
  lynth
#print axioms hyp_2f1_zero
#eval! hyp_2f1_zero.1

set_option maxHeartbeats 1263 in
-- H5: ₁F₁(1;2;1/2) = 2(√e-1). 1.2974425414
def hyp_1f1 : { x : Rat //
    abs (pfq11 1 2 (1 / 2) - x) < 1 / 1000000 } := by
  lynth
#print axioms hyp_1f1
#eval! hyp_1f1.1

set_option maxHeartbeats 1267 in
-- H6: ₀F₁(;1/2;1/4) = cosh 1. 1.5430806348
def hyp_0f1 : { x : Rat //
    abs (pfq01 (1 / 2) (1 / 4) - x) < 1 / 1000000 } := by
  lynth
#print axioms hyp_0f1
#eval! hyp_0f1.1

set_option maxHeartbeats 1485 in
-- H7: ₂F₂(1,3;2,3;1/2) = ₁F₁(1;2;1/2), 5-arg cancellation. 1.2974425414
def hyp_2f2_cancel : { x : Rat //
    abs (pfq22 1 3 2 3 (1 / 2) - x) < 1 / 1000000 } := by
  lynth
#print axioms hyp_2f2_cancel
#eval! hyp_2f2_cancel.1

set_option maxHeartbeats 1520 in
-- H8: ₃F₂(1,1,2;2,2;1/2) = ₂F₁(1,1;2;1/2), 6-arg cancellation. 1.3862943611
def hyp_3f2_cancel : { x : Rat //
    abs (pfq32 1 1 2 2 2 (1 / 2) - x) < 1 / 1000000 } := by
  lynth
#print axioms hyp_3f2_cancel
#eval! hyp_3f2_cancel.1

set_option maxHeartbeats 1815 in
-- H9: ₃F₂(-1/2,1,1;2,2;1/2), 6-arg direct. 0.9334086350
def hyp_3f2_direct : { x : Rat //
    abs (pfq32 (-1 / 2) 1 1 2 2 (1 / 2) - x) < 1 / 1000000 } := by
  lynth
#print axioms hyp_3f2_direct
#eval! hyp_3f2_direct.1

set_option maxHeartbeats 1400 in
-- H10: ₃F₂(-2,1,1;2,2;1/2) = 7/9, terminating. 0.777778
def hyp_3f2_term : { x : Rat //
    abs (pfq32 (-2) 1 1 2 2 (1 / 2) - x) < 1 / 1000000 } := by
  lynth
#print axioms hyp_3f2_term
#eval! hyp_3f2_term.1

set_option maxHeartbeats 1280 in
-- H11: ₀F₂(;1,3;1/2), direct. 1.1719331726
def hyp_0f2 : { x : Rat //
    abs (pfq02 1 3 (1 / 2) - x) < 1 / 1000000 } := by
  lynth
#print axioms hyp_0f2
#eval! hyp_0f2.1

set_option maxHeartbeats 1399 in
-- H12: ₁F₂(1;2,3;1/2), direct. 1.0868938252
def hyp_1f2 : { x : Rat //
    abs (pfq12 1 2 3 (1 / 2) - x) < 1 / 1000000 } := by
  lynth
#print axioms hyp_1f2
#eval! hyp_1f2.1

set_option maxHeartbeats 1538 in
-- H13: ₂F₂(1,2;3,4;1/2), 5-arg direct. 1.0900261978
def hyp_2f2_direct : { x : Rat //
    abs (pfq22 1 2 3 4 (1 / 2) - x) < 1 / 1000000 } := by
  lynth
#print axioms hyp_2f2_direct
#eval! hyp_2f2_direct.1

set_option maxHeartbeats 1002 in
-- H14: ₁F₁(2;3;1) = 2, larger `z`.
def hyp_1f1_two : { x : Rat //
    abs (pfq11 2 3 1 - x) < 1 / 1000000 } := by
  lynth
#print axioms hyp_1f1_two
#eval! hyp_1f1_two.1
