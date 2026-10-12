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

set_option maxHeartbeats 7192 in
/-- **CT02** — port of `T02`: `sin (8 * pi / 17) = 0.9957341763`
(irrational tolerance `pi / 100`, as in the real version; the loose
tolerance admits the coarse witness `(1, 0)`). -/
def cx_sin_eight_pi_over_seventeen : { p : Rat × Rat //
    ‖Complex.sin ((Real.pi * 8 / 17 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < Real.pi / 100 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_sin_eight_pi_over_seventeen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_sin_eight_pi_over_seventeen
#eval! cx_sin_eight_pi_over_seventeen.1

set_option maxHeartbeats 5141 in
/-- **CT03** — port of `T03`: `exp 2 = 7.3890560989`. -/
def cx_exp_two_basic : { p : Rat × Rat //
    ‖Complex.exp 2 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_exp_two_basic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_exp_two_basic
#eval! cx_exp_two_basic.1

set_option maxHeartbeats 14472 in
/-- **CT04** — port of `T04`: `log (pi / 100) = -3.4604403001`. -/
def cx_log_pi_over_hundred : { p : Rat × Rat //
    ‖Complex.log ((Real.pi / 100 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 100000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_log_pi_over_hundred' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_log_pi_over_hundred
#eval! cx_log_pi_over_hundred.1

set_option maxHeartbeats 16121 in
/-- **CT05** — port of `T05`: `2 ^ (1/3) = 1.2599210499`
(real `rpow` becomes complex `cpow`). -/
def cx_cpow_two_one_third : { p : Rat × Rat //
    ‖(2 : ℂ) ^ (((1 / 3 : ℝ)) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_cpow_two_one_third' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_cpow_two_one_third
#eval! cx_cpow_two_one_third.1

set_option maxHeartbeats 1887 in
/-- **CT06** — port of `T06`: `sqrt 2 = 1.4142135624`. -/
def cx_sqrt_two_basic : { p : Rat × Rat //
    ‖Complex.sqrt 2 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < (10 : ℝ) ^ (-10 : ℤ) } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_sqrt_two_basic' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_sqrt_two_basic
#eval! cx_sqrt_two_basic.1

end ComplexIntervalArith
