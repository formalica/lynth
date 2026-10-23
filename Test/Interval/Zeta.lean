module
import Mathlib
public import Lynth

open Lynth.Interval
open Lynth.Interval.Fns

-- EM enclosures evaluate interval `rpow`/`log`/`exp` kernels; kernel
-- certification is minutes per test, so these run native (per-declaration
-- native axioms, cf. `docs/interval/README.md`).
set_option lynth.interval.trust "native"

/-! # Riemann zeta (Euler product for integers `n ≥ 6`, Euler–Maclaurin else).

Ground truth from first-order Euler–Maclaurin in Python (`N = 10^5`,
`~12` digits) cross-checked against `π²/6`, `π⁴/90`:
`ζ(2) = 1.644934066848226`, `ζ(3) = 1.202056903159594`,
`ζ(4) = 1.082323233711138`, `ζ(5) = 1.036927755143370`,
`ζ(6) = 1.017343061984449`, `ζ(7) = 1.008349277381923`,
`ζ(8) = 1.004077356197944`, `ζ(1.5) = 2.612375348685449`,
`ζ(2.5) = 1.341487257250917`, `ζ(0.5) = -1.460354510127246`.
Analytic bounds are proved (`Fns/ZetaEulerProd.lean`, `Fns/ZetaEM.lean`,
ported from the Mathlib-only `/tmp/zeta/` prover handoff); `#eval!`
(unsafe) is used since native trust adds per-declaration axioms.
-/

set_option maxHeartbeats 60000 in
-- Z1: ζ(2) = π²/6 via Euler–Maclaurin. 1.644934066848226
public def zeta_two : { x : Rat //
    abs (Real'.zeta 2 - x) < 1 / 1000000 } := by
  lynth
/-- info: 'zeta_two' depends on axioms: [propext, Classical.choice, Quot.sound, zeta_two._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms zeta_two
#eval! zeta_two.1

set_option maxHeartbeats 60000 in
-- Z2: ζ(3) (Apéry) via Euler–Maclaurin. 1.202056903159594
public def zeta_three : { x : Rat //
    abs (Real'.zeta 3 - x) < 1 / 1000000 } := by
  lynth
/-- info: 'zeta_three' depends on axioms: [propext, Classical.choice, Quot.sound, zeta_three._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms zeta_three
#eval! zeta_three.1

set_option maxHeartbeats 60000 in
-- Z3: ζ(4) = π⁴/90 via Euler–Maclaurin. 1.082323233711138
public def zeta_four : { x : Rat //
    abs (Real'.zeta 4 - x) < 1 / 1000000 } := by
  lynth
/-- info: 'zeta_four' depends on axioms: [propext, Classical.choice, Quot.sound, zeta_four._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms zeta_four
#eval! zeta_four.1

set_option maxHeartbeats 60000 in
-- Z4: ζ(5) via Euler–Maclaurin. 1.036927755143370
public def zeta_five : { x : Rat //
    abs (Real'.zeta 5 - x) < 1 / 1000000 } := by
  lynth
/-- info: 'zeta_five' depends on axioms: [propext, Classical.choice, Quot.sound, zeta_five._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms zeta_five
#eval! zeta_five.1

set_option maxHeartbeats 60000 in
-- Z5: ζ(6) via Euler product. 1.017343061984449
public def zeta_six : { x : Rat //
    abs (Real'.zeta 6 - x) < 1 / 1000000 } := by
  lynth
/-- info: 'zeta_six' depends on axioms: [propext, Classical.choice, Quot.sound, zeta_six._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms zeta_six
#eval! zeta_six.1

set_option maxHeartbeats 60000 in
-- Z6: ζ(7) via Euler product. 1.008349277381923
public def zeta_seven : { x : Rat //
    abs (Real'.zeta 7 - x) < 1 / 1000000 } := by
  lynth
/-- info: 'zeta_seven' depends on axioms: [propext, Classical.choice, Quot.sound, zeta_seven._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms zeta_seven
#eval! zeta_seven.1

set_option maxHeartbeats 60000 in
-- Z7: ζ(8) via Euler product. 1.004077356197944
public def zeta_eight : { x : Rat //
    abs (Real'.zeta 8 - x) < 1 / 1000000 } := by
  lynth
/-- info: 'zeta_eight' depends on axioms: [propext, Classical.choice, Quot.sound, zeta_eight._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms zeta_eight
#eval! zeta_eight.1

set_option maxHeartbeats 60000 in
-- Z8: ζ(1.5) via Euler–Maclaurin. 2.612375348685449
public def zeta_three_halves : { x : Rat //
    abs (Real'.zeta 1.5 - x) < 1 / 1000000 } := by
  lynth
/-- info: 'zeta_three_halves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 zeta_three_halves._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms zeta_three_halves
#eval! zeta_three_halves.1

set_option maxHeartbeats 60000 in
-- Z9: ζ(2.5) via Euler–Maclaurin. 1.341487257250917
public def zeta_five_halves : { x : Rat //
    abs (Real'.zeta 2.5 - x) < 1 / 1000000 } := by
  lynth
/-- info: 'zeta_five_halves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 zeta_five_halves._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms zeta_five_halves
#eval! zeta_five_halves.1

set_option maxHeartbeats 60000 in
-- Z10: ζ(0.5) < 0 via Euler–Maclaurin on `(0, 1)`. -1.460354510127246
public def zeta_half : { x : Rat //
    abs (Real'.zeta 0.5 - x) < 1 / 1000000 } := by
  lynth
/-- info: 'zeta_half' depends on axioms: [propext, Classical.choice, Quot.sound, zeta_half._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms zeta_half
#eval! zeta_half.1

set_option maxHeartbeats 60000 in
-- Z11: ζ(-1) = -1/12 via functional equation. -0.0833333333
public def zeta_neg_one : { x : Rat //
    abs (Real'.zeta (-1) - x) < 1 / 1000 } := by
  lynth
/-- info: 'zeta_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound, zeta_neg_one._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms zeta_neg_one
#eval! zeta_neg_one.1

set_option maxHeartbeats 60000 in
-- Z12: ζ(-3) = 1/120 via functional equation. 0.0083333333
public def zeta_neg_three : { x : Rat //
    abs (Real'.zeta (-3) - x) < 1 / 1000 } := by
  lynth
/-- info: 'zeta_neg_three' depends on axioms: [propext, Classical.choice, Quot.sound, zeta_neg_three._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms zeta_neg_three
#eval! zeta_neg_three.1

set_option maxHeartbeats 60000 in
-- Z13: ζ(-2) = 0 (trivial zero) via functional equation.
public def zeta_neg_two : { x : Rat //
    abs (Real'.zeta (-2) - x) < 1 / 1000 } := by
  lynth
/-- info: 'zeta_neg_two' depends on axioms: [propext, Classical.choice, Quot.sound, zeta_neg_two._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms zeta_neg_two
#eval! zeta_neg_two.1

set_option maxHeartbeats 60000 in
-- Z14: ζ(-1/2) via functional equation. -0.207886224977
public def zeta_neg_half : { x : Rat //
    abs (Real'.zeta (-1 / 2) - x) < 1 / 1000 } := by
  lynth
/-- info: 'zeta_neg_half' depends on axioms: [propext, Classical.choice, Quot.sound, zeta_neg_half._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms zeta_neg_half
#eval! zeta_neg_half.1
