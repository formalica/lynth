import Mathlib
import Lynth

open Lynth.Interval
open Lynth.Interval.Fns

-- Complex `zeta` runs native (per-declaration native axioms):
-- Euler-product kernels evaluate hundreds of `cpow` factors, and soundness
-- rests on the sorry'd Euler-tail / FE mirrors
-- (`/tmp/complex/zeta_handoff.lean`), as in `Test/Interval/Zeta.lean`.
set_option lynth.interval.trust "native"

/-! # Complex Riemann zeta values (ported from `Test/Interval/Zeta.lean`).

`ζ(2)` goes through the closed form `π²/6`; `ζ(4)`, `ζ(6)`, `ζ(7)`,
`ζ(8)` through the Euler product; `ζ(-1)`, `ζ(-3)`, `ζ(-2)` through the
functional equation.  Ground truths are the same closed forms / Python
cross-checks as the real versions.  Witnesses are `Rat × Rat` pairs;
distance is `Complex.abs` (`‖·‖`).
Real costs for comparison: all `60000` (native EM/Euler).

Covered by the complex Euler–Maclaurin evaluator: `ζ(3)`, `ζ(5)`,
`ζ(3/2)`, `ζ(5/2)`, `ζ(1/2)`, `ζ(-1/2)` (no `Complex.*` gap — the
evaluator covers them once EM lands).
-/

set_option maxHeartbeats 1703 in
-- CZ1: port of `zeta_two`: `ζ(2) = π²/6 = 1.6449340668`. (1.644934, 0)
def cx_zeta_two : { p : Rat × Rat //
    ‖riemannZeta 2 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_zeta_two' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_two._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_two
#eval! cx_zeta_two.1

set_option maxHeartbeats 6105 in
-- CZ2: port of `zeta_four`: `ζ(4) = π⁴/90 = 1.0823232337`. (1.082323, 0)
def cx_zeta_four : { p : Rat × Rat //
    ‖riemannZeta 4 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_zeta_four' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_four._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_four
#eval! cx_zeta_four.1

set_option maxHeartbeats 4880 in
-- CZ3: port of `zeta_six`: `ζ(6) = 1.0173430620`. (1.017343, 0)
def cx_zeta_six : { p : Rat × Rat //
    ‖riemannZeta 6 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_zeta_six' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_six._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_six
#eval! cx_zeta_six.1

set_option maxHeartbeats 4867 in
-- CZ4: port of `zeta_seven`: `ζ(7) = 1.0083492774`. (1.008349, 0)
def cx_zeta_seven : { p : Rat × Rat //
    ‖riemannZeta 7 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_zeta_seven' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_seven._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_seven
#eval! cx_zeta_seven.1

set_option maxHeartbeats 4864 in
-- CZ5: port of `zeta_eight`: `ζ(8) = 1.0040773562`. (1.004077, 0)
def cx_zeta_eight : { p : Rat × Rat //
    ‖riemannZeta 8 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_zeta_eight' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_eight._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_eight
#eval! cx_zeta_eight.1

set_option maxHeartbeats 2070 in
-- CZ6: port of `zeta_neg_one`: `ζ(-1) = -1/12 = -0.0833333`.
def cx_zeta_neg_one : { p : Rat × Rat //
    ‖riemannZeta (-1) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000 } := by
  lynth
/-- info: 'cx_zeta_neg_one' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_neg_one._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_neg_one
#eval! cx_zeta_neg_one.1

set_option maxHeartbeats 6483 in
-- CZ7: port of `zeta_neg_three`: `ζ(-3) = 1/120 = 0.0083333`.
def cx_zeta_neg_three : { p : Rat × Rat //
    ‖riemannZeta (-3) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000 } := by
  lynth
/-- info: 'cx_zeta_neg_three' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_neg_three._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_neg_three
#eval! cx_zeta_neg_three.1

set_option maxHeartbeats 6208 in
-- CZ8: port of `zeta_neg_two`: `ζ(-2) = 0` (trivial zero).
def cx_zeta_neg_two : { p : Rat × Rat //
    ‖riemannZeta (-2) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000 } := by
  lynth
/-- info: 'cx_zeta_neg_two' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_neg_two._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_neg_two
#eval! cx_zeta_neg_two.1

set_option maxHeartbeats 5807 in
-- CZ9 (own, complex argument): `ζ(6+I) = 1.0126728826 - 0.0115446266·I`.
def cx_zeta_six_add_I : { p : Rat × Rat //
    ‖riemannZeta (6 + Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_zeta_six_add_I' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_six_add_I._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_six_add_I
#eval! cx_zeta_six_add_I.1

set_option maxHeartbeats 7840 in
-- CZ10 (own, complex argument): `ζ(3+2I) = 0.9730419604 - 0.1476955930·I`.
def cx_zeta_three_add_2I : { p : Rat × Rat //
    ‖riemannZeta (3 + 2 * Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000 } := by
  lynth
/-- info: 'cx_zeta_three_add_2I' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_three_add_2I._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_three_add_2I
#eval! cx_zeta_three_add_2I.1

set_option maxHeartbeats 6078 in
-- CZ11: port of `zeta_three`: `ζ(3) = 1.2020569032` (Apéry, via EM).
def cx_zeta_three : { p : Rat × Rat //
    ‖riemannZeta 3 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_zeta_three' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_three._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_three
#eval! cx_zeta_three.1

set_option maxHeartbeats 6093 in
-- CZ12: port of `zeta_five`: `ζ(5) = 1.0369277551` (via EM).
def cx_zeta_five : { p : Rat × Rat //
    ‖riemannZeta 5 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_zeta_five' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_five._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_five
#eval! cx_zeta_five.1

set_option maxHeartbeats 6432 in
-- CZ13: port of `zeta_three_halves`: `ζ(3/2) = 2.6123753487` (via EM).
def cx_zeta_three_halves : { p : Rat × Rat //
    ‖riemannZeta ((3 / 2 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_zeta_three_halves' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_three_halves._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_three_halves
#eval! cx_zeta_three_halves.1

set_option maxHeartbeats 6439 in
-- CZ14: port of `zeta_five_halves`: `ζ(5/2) = 1.3414872573` (via EM).
def cx_zeta_five_halves : { p : Rat × Rat //
    ‖riemannZeta ((5 / 2 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_zeta_five_halves' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_five_halves._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_five_halves
#eval! cx_zeta_five_halves.1

set_option maxHeartbeats 6444 in
-- CZ15: port of `zeta_half`: `ζ(1/2) = -1.4603545101` (via EM).
def cx_zeta_half : { p : Rat × Rat //
    ‖riemannZeta ((1 / 2 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_zeta_half' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_half._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_half
#eval! cx_zeta_half.1

set_option maxHeartbeats 6796 in
-- CZ16: port of `zeta_neg_half`: `ζ(-1/2) = -0.2078862250` (via FE + EM).
def cx_zeta_neg_half : { p : Rat × Rat //
    ‖riemannZeta ((-1 / 2 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000 } := by
  lynth
/-- info: 'cx_zeta_neg_half' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_zeta_neg_half._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_zeta_neg_half
#eval! cx_zeta_neg_half.1
