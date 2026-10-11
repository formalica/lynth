import Mathlib
import Lynth

open Lynth.Interval
open Lynth.Interval.Fns

-- Hypergeometric interval checks run native (per-declaration native axioms),
-- as in `Test/Interval/Zeta.lean`: analytic bounds are `sorry`'d and the
-- enclosures are wide enough that kernel certification recurses too deep.
set_option lynth.interval.trust "native"

/-! # Generalized hypergeometric `pFq` via multiset `Complex.HGFun` (H1–H14).

Single engine (`Fns/Hypgeom.lean`, `HGFunL` entry): goals write
`Complex.HGFun` over multisets; the reifier normalizes literal spines to
lists. Ground truths are closed forms, parameter cancellation, terminating
prefixes, and direct-series cross-checks in Python.  Analytic bounds are
`sorry`'d (pure analysis mirrored Mathlib-only in `/tmp/pfq_thm_proof.lean`).
-/

set_option maxHeartbeats 2872 in
-- H1: ₂F₁(1,1;2;-1/2) = 2ln(3/2). 0.8109302162
def hyp_2f1_neg : { x : Rat //
    abs ((Complex.HGFun {1, 1} {2} (-1 / 2 : ℂ)).re - x) < 1 / 1000000 } := by
  lynth
/-- info: 'hyp_2f1_neg' depends on axioms: [propext, Classical.choice, Quot.sound, hyp_2f1_neg._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms hyp_2f1_neg
#eval! hyp_2f1_neg.1

set_option maxHeartbeats 2725 in
-- H2: ₂F₁(1,1;2;1/2) = 2ln2. 1.3862943611
def hyp_2f1_pos : { x : Rat //
    abs ((Complex.HGFun {1, 1} {2} (1 / 2 : ℂ)).re - x) < 1 / 1000000 } := by
  lynth
/-- info: 'hyp_2f1_pos' depends on axioms: [propext, Classical.choice, Quot.sound, hyp_2f1_pos._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms hyp_2f1_pos
#eval! hyp_2f1_pos.1

set_option maxHeartbeats 2822 in
-- H3: ₂F₁(-2,1;2;1/2) = 7/12, terminating. 0.583333
def hyp_2f1_term : { x : Rat //
    abs ((Complex.HGFun {-2, 1} {2} (1 / 2 : ℂ)).re - x) < 1 / 1000000 } := by
  lynth
/-- info: 'hyp_2f1_term' depends on axioms: [propext, Classical.choice, Quot.sound, hyp_2f1_term._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms hyp_2f1_term
#eval! hyp_2f1_term.1

set_option maxHeartbeats 2402 in
-- H4: ₂F₁(1,2;3;0) = 1.
def hyp_2f1_zero : { x : Rat //
    abs ((Complex.HGFun {1, 2} {3} (0 : ℂ)).re - x) < 1 / 1000000 } := by
  lynth
/-- info: 'hyp_2f1_zero' depends on axioms: [propext, Classical.choice, Quot.sound, hyp_2f1_zero._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms hyp_2f1_zero
#eval! hyp_2f1_zero.1

set_option maxHeartbeats 2601 in
-- H5: ₁F₁(1;2;1/2) = 2(√e-1). 1.2974425414
def hyp_1f1 : { x : Rat //
    abs ((Complex.HGFun {1} {2} (1 / 2 : ℂ)).re - x) < 1 / 1000000 } := by
  lynth
/-- info: 'hyp_1f1' depends on axioms: [propext, Classical.choice, Quot.sound, hyp_1f1._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms hyp_1f1
#eval! hyp_1f1.1

set_option maxHeartbeats 2589 in
-- H6: ₀F₁(;1/2;1/4) = cosh 1, empty tops. 1.5430806348
def hyp_0f1 : { x : Rat //
    abs ((Complex.HGFun {} {(1 / 2 : ℂ)} (1 / 4 : ℂ)).re - x) < 1 / 1000000 } := by
  lynth
/-- info: 'hyp_0f1' depends on axioms: [propext, Classical.choice, Quot.sound, hyp_0f1._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms hyp_0f1
#eval! hyp_0f1.1

set_option maxHeartbeats 3026 in
-- H7: ₂F₂(1,3;2,3;1/2) = ₁F₁(1;2;1/2), cancellation. 1.2974425414
def hyp_2f2_cancel : { x : Rat //
    abs ((Complex.HGFun {1, 3} {2, 3} (1 / 2 : ℂ)).re - x) < 1 / 1000000 } := by
  lynth
/-- info: 'hyp_2f2_cancel' depends on axioms: [propext, Classical.choice, Quot.sound, hyp_2f2_cancel._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms hyp_2f2_cancel
#eval! hyp_2f2_cancel.1

set_option maxHeartbeats 2952 in
-- H8: ₃F₂(1,1,2;2,2;1/2) = ₂F₁(1,1;2;1/2), cancellation. 1.3862943611
def hyp_3f2_cancel : { x : Rat //
    abs ((Complex.HGFun {1, 1, 2} {2, 2} (1 / 2 : ℂ)).re - x) < 1 / 1000000 } := by
  lynth
/-- info: 'hyp_3f2_cancel' depends on axioms: [propext, Classical.choice, Quot.sound, hyp_3f2_cancel._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms hyp_3f2_cancel
#eval! hyp_3f2_cancel.1

set_option maxHeartbeats 3561 in
-- H9: ₃F₂(-1/2,1,1;2,2;1/2), direct. 0.9334086350
def hyp_3f2_direct : { x : Rat //
    abs ((Complex.HGFun {(-1 / 2 : ℂ), 1, 1} {2, 2} (1 / 2 : ℂ)).re - x) < 1 / 1000000 } := by
  lynth
/-- info: 'hyp_3f2_direct' depends on axioms: [propext, Classical.choice, Quot.sound, hyp_3f2_direct._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms hyp_3f2_direct
#eval! hyp_3f2_direct.1

set_option maxHeartbeats 3017 in
-- H10: ₃F₂(-2,1,1;2,2;1/2) = 7/9, terminating. 0.777778
def hyp_3f2_term : { x : Rat //
    abs ((Complex.HGFun {-2, 1, 1} {2, 2} (1 / 2 : ℂ)).re - x) < 1 / 1000000 } := by
  lynth
/-- info: 'hyp_3f2_term' depends on axioms: [propext, Classical.choice, Quot.sound, hyp_3f2_term._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms hyp_3f2_term
#eval! hyp_3f2_term.1

set_option maxHeartbeats 2649 in
-- H11: ₀F₂(;1,3;1/2), empty tops, direct. 1.1719331726
def hyp_0f2 : { x : Rat //
    abs ((Complex.HGFun {} {1, 3} (1 / 2 : ℂ)).re - x) < 1 / 1000000 } := by
  lynth
/-- info: 'hyp_0f2' depends on axioms: [propext, Classical.choice, Quot.sound, hyp_0f2._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms hyp_0f2
#eval! hyp_0f2.1

set_option maxHeartbeats 2919 in
-- H12: ₁F₂(1;2,3;1/2), direct. 1.0868938252
def hyp_1f2 : { x : Rat //
    abs ((Complex.HGFun {1} {2, 3} (1 / 2 : ℂ)).re - x) < 1 / 1000000 } := by
  lynth
/-- info: 'hyp_1f2' depends on axioms: [propext, Classical.choice, Quot.sound, hyp_1f2._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms hyp_1f2
#eval! hyp_1f2.1

set_option maxHeartbeats 3237 in
-- H13: ₂F₂(1,2;3,4;1/2), direct. 1.0900261978
def hyp_2f2_direct : { x : Rat //
    abs ((Complex.HGFun {1, 2} {3, 4} (1 / 2 : ℂ)).re - x) < 1 / 1000000 } := by
  lynth
/-- info: 'hyp_2f2_direct' depends on axioms: [propext, Classical.choice, Quot.sound, hyp_2f2_direct._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms hyp_2f2_direct
#eval! hyp_2f2_direct.1

set_option maxHeartbeats 2108 in
-- H14: ₁F₁(2;3;1) = 2, larger `z`.
def hyp_1f1_two : { x : Rat //
    abs ((Complex.HGFun {2} {3} (1 : ℂ)).re - x) < 1 / 1000000 } := by
  lynth
/-- info: 'hyp_1f1_two' depends on axioms: [propext, Classical.choice, Quot.sound, hyp_1f1_two._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms hyp_1f1_two
#eval! hyp_1f1_two.1
