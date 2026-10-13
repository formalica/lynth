import Mathlib
import Lynth

open Lynth.Interval
open Lynth.Interval.Fns

-- Complex `log`/`sqrt` run native (per-declaration native axioms):
-- their soundness rests on the proved quadrant/cut helpers
-- (`Complex.arg_of_pos`, `Complex.sqrt_components_of_pos`, …).
set_option lynth.interval.trust "native"

/-! # Complex log, sqrt, arg, pi (batch 2).

Ground truths are closed forms (`log e = 1`, `sqrt 4 = 2`,
`sqrt (3+4I) = 2+I`, `log (1+I)`) and the constants.  Witnesses are
`Rat × Rat` pairs; distance is `Complex.abs` (`‖·‖`).
-/

set_option maxHeartbeats 1701 in
-- CL1: `log e = 1`. (1, 0)
def cx_log_e : { p : Rat × Rat //
    ‖Complex.log ((Real.exp 1 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_log_e' depends on axioms: [propext, Classical.choice, Quot.sound, cx_log_e._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_log_e
#eval! cx_log_e.1

set_option maxHeartbeats 2123 in
-- CL2: `log (1+I) = 0.3465735903 + 0.7853981634·I`.
def cx_log_one_add_I : { p : Rat × Rat //
    ‖Complex.log (1 + Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_log_one_add_I' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cx_log_one_add_I._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_log_one_add_I
#eval! cx_log_one_add_I.1

set_option maxHeartbeats 1537 in
-- CS1: `sqrt 4 = 2`. (2, 0)
def cx_sqrt_four : { p : Rat × Rat //
    ‖Complex.sqrt 4 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_sqrt_four' depends on axioms: [propext, Classical.choice, Quot.sound, cx_sqrt_four._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_sqrt_four
#eval! cx_sqrt_four.1

set_option maxHeartbeats 2326 in
-- CS2: `sqrt (3+4I) = 2+I`. (2, 1)
def cx_sqrt_3_4I : { p : Rat × Rat //
    ‖Complex.sqrt (3 + 4 * Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_sqrt_3_4I' depends on axioms: [propext, Classical.choice, Quot.sound, cx_sqrt_3_4I._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_sqrt_3_4I
#eval! cx_sqrt_3_4I.1

set_option maxHeartbeats 1396 in
-- CP1: `π` constant. (3.141593, 0)
def cx_pi_const : { p : Rat × Rat //
    ‖(Real.pi : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_pi_const' depends on axioms: [propext, Classical.choice, Quot.sound, cx_pi_const._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_pi_const
#eval! cx_pi_const.1

set_option maxHeartbeats 1447 in
-- CP2: Euler–Mascheroni constant. (0.577216, 0)
def cx_euler_const : { p : Rat × Rat //
    ‖(Real.eulerMascheroniConstant : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_euler_const' depends on axioms: [propext, Classical.choice, Quot.sound, cx_euler_const._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_euler_const
#eval! cx_euler_const.1

set_option maxHeartbeats 1476 in
-- CL3 (own, pure-imaginary arg): `log I = π/2·I`. (0, 1.570796)
def cx_log_I : { p : Rat × Rat //
    ‖Complex.log Complex.I - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_log_I' depends on axioms: [propext, Classical.choice, Quot.sound, cx_log_I._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_log_I
#eval! cx_log_I.1

set_option maxHeartbeats 2646 in
-- CL4 (own, complex argument): `log (2+3I) = 1.2824746787 + 0.9827937232·I`.
def cx_log_two_3I : { p : Rat × Rat //
    ‖Complex.log (2 + 3 * Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_log_two_3I' depends on axioms: [propext, Classical.choice, Quot.sound, cx_log_two_3I._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_log_two_3I
#eval! cx_log_two_3I.1

set_option maxHeartbeats 2619 in
-- CS3 (own, complex argument): `sqrt (2+3I) = 1.6741492280 + 0.8959774761·I`.
def cx_sqrt_two_3I : { p : Rat × Rat //
    ‖Complex.sqrt (2 + 3 * Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_sqrt_two_3I' depends on axioms: [propext, Classical.choice, Quot.sound, cx_sqrt_two_3I._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_sqrt_two_3I
#eval! cx_sqrt_two_3I.1
