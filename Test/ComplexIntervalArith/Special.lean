import Mathlib
import Lynth

/-!
Ports of `Test/IntervalArith/Special.lean` Gamma/pi tests to complex functions.
Ground truth: `arb/CERTIFICATES.md` (same as the real versions).
Witnesses are `Rat × Rat` pairs; distance is `Complex.abs` (`‖·‖`).
Real costs for comparison: `gamma_quarter` 27470, `pi_rational` 2233 heartbeats.
-/

namespace ComplexIntervalArith

set_option maxHeartbeats 39735 in
/-- **CT18** — port of `T18`: `Γ(1/4) = 3.6256099082`. -/
def cx_gamma_quarter : { p : Rat × Rat //
    ‖Complex.Gamma ((1 / 4 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < (10 : ℝ) ^ (-5 : ℤ) } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_gamma_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_gamma_quarter
#eval! cx_gamma_quarter.1

set_option maxHeartbeats 3137 in
/-- **CT20** — port of `T20`: `π` to within `1/1000`. -/
def cx_pi_rational : { p : Rat × Rat //
    ‖(Real.pi : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_pi_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_pi_rational
#eval! cx_pi_rational.1

end ComplexIntervalArith
