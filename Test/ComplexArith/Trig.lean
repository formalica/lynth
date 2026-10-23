module
import Mathlib
public import Lynth

open Lynth.Interval
open Lynth.Interval.Fns

-- Complex `arctan` runs native (per-declaration native axioms):
-- its soundness goes through `logBox`, resting on the proved helpers
-- (`Complex.arg_of_pos`, …).
set_option lynth.interval.trust "native"

/-! # Complex arctan values.

Ground truths are closed forms (`arctan (1/2)`, `arctan (1+I)` via the
log formula).  Witnesses are `Rat × Rat` pairs; distance is `Complex.abs`.
-/

set_option maxHeartbeats 2249 in
-- CA1: `arctan (1/2) = 0.4636476090`. (0.463648, 0)
public def cx_arctan_half : { p : Rat × Rat //
    ‖Complex.arctan ((1 : ℝ) / 2 : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_arctan_half' depends on axioms: [propext, Classical.choice, Quot.sound, cx_arctan_half._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_arctan_half
#eval! cx_arctan_half.1

set_option maxHeartbeats 2104 in
-- CA2: `arctan (1+I) = 1.0172219679 + 0.4023594781·I`.
public def cx_arctan_one_add_I : { p : Rat × Rat //
    ‖Complex.arctan (1 + Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000 } := by
  lynth
/-- info: 'cx_arctan_one_add_I' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cx_arctan_one_add_I._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_arctan_one_add_I
#eval! cx_arctan_one_add_I.1

set_option maxHeartbeats 1698 in
-- CC3: `cot 1 = 0.6420926159`. (0.642093, 0)
public def cx_cot_one : { p : Rat × Rat //
    ‖Complex.cot 1 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_cot_one' depends on axioms: [propext, Classical.choice, Quot.sound, cx_cot_one._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_cot_one
#eval! cx_cot_one.1

set_option maxHeartbeats 2151 in
-- CT1 (own, complex argument): `tan (1+I) = 0.2717525853 + 1.0839233273·I`.
public def cx_tan_one_add_I : { p : Rat × Rat //
    ‖Complex.tan (1 + Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_tan_one_add_I' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cx_tan_one_add_I._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_tan_one_add_I
#eval! cx_tan_one_add_I.1

set_option maxHeartbeats 2200 in
-- CT2 (own, complex argument): `cot (1+I) = 0.2176215619 - 0.8680141429·I`.
public def cx_cot_one_add_I : { p : Rat × Rat //
    ‖Complex.cot (1 + Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_cot_one_add_I' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cx_cot_one_add_I._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_cot_one_add_I
#eval! cx_cot_one_add_I.1

set_option maxHeartbeats 2116 in
-- CT3 (own, complex argument): `arctan (2+I) = 1.1780972451 + 0.1732867951·I`.
public def cx_arctan_two_add_I : { p : Rat × Rat //
    ‖Complex.arctan (2 + Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_arctan_two_add_I' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cx_arctan_two_add_I._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_arctan_two_add_I
#eval! cx_arctan_two_add_I.1
