import Mathlib
import Lynth

open Lynth.Interval
open Lynth.Interval.Fns

-- Complex `arctan` runs native (per-declaration native axioms):
-- its soundness goes through `logBox`, resting on the sorry'd helpers
-- (`/tmp/complex/batch2_handoff.lean`), as in `Test/Interval/Zeta.lean`.
set_option lynth.interval.trust "native"

/-! # Complex arctan values.

Ground truths are closed forms (`arctan (1/2)`, `arctan (1+I)` via the
log formula).  Witnesses are `Rat × Rat` pairs; distance is `Complex.abs`.
-/

set_option maxHeartbeats 2249 in
-- CA1: `arctan (1/2) = 0.4636476090`. (0.463648, 0)
def cx_arctan_half : { p : Rat × Rat //
    ‖Complex.arctan ((1 : ℝ) / 2 : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_arctan_half' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_arctan_half._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_arctan_half
#eval! cx_arctan_half.1

set_option maxHeartbeats 2104 in
-- CA2: `arctan (1+I) = 1.0172219679 + 0.4023594781·I`.
def cx_arctan_one_add_I : { p : Rat × Rat //
    ‖Complex.arctan (1 + Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000 } := by
  lynth
/-- info: 'cx_arctan_one_add_I' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_arctan_one_add_I._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_arctan_one_add_I
#eval! cx_arctan_one_add_I.1

set_option maxHeartbeats 1698 in
-- CC3: `cot 1 = 0.6420926159`. (0.642093, 0)
def cx_cot_one : { p : Rat × Rat //
    ‖Complex.cot 1 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_cot_one' depends on axioms: [propext, Classical.choice, Quot.sound, cx_cot_one._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_cot_one
#eval! cx_cot_one.1
