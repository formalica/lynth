import Mathlib
import Lynth

open Lynth.Interval
open Lynth.Interval.Fns

-- Complex `digamma` runs native (per-declaration native axioms):
-- shift/Stirling kernels evaluate dozens of `cpow`/`log` boxes, and
-- soundness rests on the sorry'd Stirling mirror
-- (`/tmp/complex/digamma_handoff.lean`), as in `Test/Interval/Zeta.lean`.
set_option lynth.interval.trust "native"

/-! # Complex digamma values (ported from `Test/Interval/Digamma.lean`).

Ground truths are the recurrence `ψ(x+1) = ψ(x) + 1/x` with
`ψ(1) = -γ`, `ψ(1/2) = -γ - 2·ln 2` (same as the real versions).
Witnesses are `Rat × Rat` pairs; distance is `Complex.abs` (`‖·‖`).
Real costs for comparison: all `60000` (native shift+Stirling).
-/

set_option maxHeartbeats 1815 in
-- CD1: port of `dig_one`: `ψ(1) = -γ = -0.5772156649`. (-0.577216, 0)
def cx_dig_one : { p : Rat × Rat //
    ‖Complex.digamma 1 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_dig_one' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, cx_dig_one._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_dig_one
#eval! cx_dig_one.1

set_option maxHeartbeats 1790 in
-- CD2: port of `dig_two`: `ψ(2) = 1-γ = 0.4227843351`. (0.422784, 0)
def cx_dig_two : { p : Rat × Rat //
    ‖Complex.digamma 2 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_dig_two' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, cx_dig_two._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_dig_two
#eval! cx_dig_two.1

set_option maxHeartbeats 2166 in
-- CD3: port of `dig_half`: `ψ(1/2) = -γ-2ln2 = -1.9635100260`.
def cx_dig_half : { p : Rat × Rat //
    ‖Complex.digamma ((1 / 2 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_dig_half' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_dig_half._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_dig_half
#eval! cx_dig_half.1

set_option maxHeartbeats 2153 in
-- CD4: port of `dig_five_halves`: `ψ(5/2) = 0.7031566407`.
def cx_dig_five_halves : { p : Rat × Rat //
    ‖Complex.digamma ((5 / 2 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_dig_five_halves' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_dig_five_halves._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_dig_five_halves
#eval! cx_dig_five_halves.1

set_option maxHeartbeats 2216 in
-- CD5: port of `dig_neg_half`: `ψ(-1/2) = 0.0364899740` (reflection).
def cx_dig_neg_half : { p : Rat × Rat //
    ‖Complex.digamma ((-1 / 2 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000 } := by
  lynth
/-- info: 'cx_dig_neg_half' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_dig_neg_half._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_dig_neg_half
#eval! cx_dig_neg_half.1

set_option maxHeartbeats 1791 in
-- CD6: port of `dig_three`: `ψ(3) = 3/2-γ = 0.9227843351`. (0.922784, 0)
def cx_dig_three : { p : Rat × Rat //
    ‖Complex.digamma 3 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_dig_three' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_dig_three._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_dig_three
#eval! cx_dig_three.1
