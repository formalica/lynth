import Mathlib
import Lynth

open Lynth.Interval

/-! # Complex exponential and trigonometric values (ported from `Test/Interval/Exp.lean`).

Ground truths are closed forms (`exp (πI) = -1`), real-line values
(`exp 2 = 7.3890560989`, `exp 1 = 2.7182818285`), the Pythagorean identity,
and conjugation symmetry (no real analogue).  Witnesses are `Rat × Rat`
pairs; distance is `Complex.abs` (`‖·‖`).
Real costs for comparison: `exp_two` 2179, `e1` 1836, `e2` 3614 heartbeats.
-/

set_option maxHeartbeats 3930 in
-- CE1: Euler's identity `exp (πI) + 1 = 0`, i.e. `exp (πI) = -1`. (-1, 0)
def cx_exp_pi : { p : Rat × Rat //
    ‖Complex.exp (Real.pi * Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000 } := by
  lynth
/-- info: 'cx_exp_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_exp_pi
#eval! cx_exp_pi.1

set_option maxHeartbeats 5142 in
-- CE2: port of `exp_two`: `exp 2 = 7.3890560989`. (7.389056, 0)
def cx_exp_two : { p : Rat × Rat //
    ‖Complex.exp 2 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_exp_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_exp_two
#eval! cx_exp_two.1

set_option maxHeartbeats 5018 in
-- CE3: port of `e2` (shape): `exp 1 = 2.7182818285`. (2.718282, 0)
def cx_exp_one : { p : Rat × Rat //
    ‖Complex.exp 1 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_exp_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_exp_one
#eval! cx_exp_one.1

set_option maxHeartbeats 11691 in
-- CE4: Pythagorean identity at `1 + I`: `sin² + cos² = 1`. (1, 0)
def cx_sincos_id : { p : Rat × Rat //
    ‖Complex.sin (1 + Complex.I) * Complex.sin (1 + Complex.I)
      + Complex.cos (1 + Complex.I) * Complex.cos (1 + Complex.I)
      - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_sincos_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_sincos_id
#eval! cx_sincos_id.1

set_option maxHeartbeats 8385 in
-- CE5 (own, no real analogue): conjugation symmetry
-- `conj (exp (1+I)) = exp (conj (1+I)) = 1.4686939399 - 2.2873552872·I`.
def cx_conj_symm : { p : Rat × Rat //
    ‖(starRingEnd ℂ) (Complex.exp (1 + Complex.I))
      - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000 } := by
  lynth
/-- info: 'cx_conj_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_conj_symm
#eval! cx_conj_symm.1
