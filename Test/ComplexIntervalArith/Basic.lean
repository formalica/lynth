import Mathlib
import Lynth

/-!
Ports of `Test/IntervalArith/Basic.lean` point values to complex functions.
Ground truth: `arb/CERTIFICATES.md` (same as the real versions).
Witnesses are `Rat × Rat` pairs; distance is `Complex.abs` (`‖·‖`).
Real costs for comparison: `cos_eight_pi_over_seventeen` 4808 heartbeats.
-/

namespace ComplexIntervalArith

set_option maxHeartbeats 7401 in
/-- **CT01** — port of `T01`: `cos (8 * pi / 17) = 0.0922683594633020`. -/
def cx_cos_eight_pi_over_seventeen : { p : Rat × Rat //
    ‖Complex.cos ((Real.pi * 8 / 17 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < (10 : ℝ) ^ (-5 : ℤ) } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_cos_eight_pi_over_seventeen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_cos_eight_pi_over_seventeen
#eval! cx_cos_eight_pi_over_seventeen.1

end ComplexIntervalArith
