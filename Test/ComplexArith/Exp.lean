module
import Mathlib
public import Lynth

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
public def cx_exp_pi : { p : Rat × Rat //
    ‖Complex.exp (Real.pi * Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000 } := by
  lynth
/-- info: 'cx_exp_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_exp_pi
#eval! cx_exp_pi.1

set_option maxHeartbeats 5142 in
-- CE2: port of `exp_two`: `exp 2 = 7.3890560989`. (7.389056, 0)
public def cx_exp_two : { p : Rat × Rat //
    ‖Complex.exp 2 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_exp_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_exp_two
#eval! cx_exp_two.1

set_option maxHeartbeats 5018 in
-- CE3: port of `e2` (shape): `exp 1 = 2.7182818285`. (2.718282, 0)
public def cx_exp_one : { p : Rat × Rat //
    ‖Complex.exp 1 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_exp_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_exp_one
#eval! cx_exp_one.1

set_option maxHeartbeats 11691 in
-- CE4: Pythagorean identity at `1 + I`: `sin² + cos² = 1`. (1, 0)
public def cx_sincos_id : { p : Rat × Rat //
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
public def cx_conj_symm : { p : Rat × Rat //
    ‖(starRingEnd ℂ) (Complex.exp (1 + Complex.I))
      - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000 } := by
  lynth
/-- info: 'cx_conj_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_conj_symm
#eval! cx_conj_symm.1

set_option maxHeartbeats 8048 in
-- CE6 (own, complex argument): `exp (1+I) = 1.4686939399 + 2.2873552872·I`.
public def cx_exp_one_add_I : { p : Rat × Rat //
    ‖Complex.exp (1 + Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_exp_one_add_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_exp_one_add_I
#eval! cx_exp_one_add_I.1

set_option maxHeartbeats 9882 in
-- CE7 (own, complex argument): `sin (1+I) = 1.2984575814 + 0.6349639148·I`.
public def cx_sin_one_add_I : { p : Rat × Rat //
    ‖Complex.sin (1 + Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_sin_one_add_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_sin_one_add_I
#eval! cx_sin_one_add_I.1

set_option maxHeartbeats 9964 in
-- CE8 (own, complex argument): `cos (1+I) = 0.8337300251 - 0.9888977058·I`.
public def cx_cos_one_add_I : { p : Rat × Rat //
    ‖Complex.cos (1 + Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_cos_one_add_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_cos_one_add_I
#eval! cx_cos_one_add_I.1

set_option maxHeartbeats 16439 in
-- CC1: `(1+I)^(2:ℂ) = 2·I`. (0, 2)
public def cx_cpow_one_add_I : { p : Rat × Rat //
    ‖(1 + Complex.I) ^ ((2 : ℂ)) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_cpow_one_add_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_cpow_one_add_I
#eval! cx_cpow_one_add_I.1

set_option maxHeartbeats 15949 in
-- CC2: `(2:ℂ)^((4:ℂ)) = 16`. (16, 0)
public def cx_cpow_two_four : { p : Rat × Rat //
    ‖(2 : ℂ) ^ ((4 : ℂ)) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_cpow_two_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_cpow_two_four
#eval! cx_cpow_two_four.1
