module
import Mathlib
public import Lynth

open Lynth.Interval
open Lynth.Interval.Fns

-- Complex `Gamma` runs native (per-declaration native axioms):
-- Stirling kernels are slow in the kernel; soundness rests on the proved
-- Stirling expansion (`Complex.stirling_Gamma_exp`), as in
-- `Test/Interval/Zeta.lean`.
set_option lynth.interval.trust "native"

/-! # Complex Gamma values (ported from `Test/Interval/Gamma.lean`).

Ground truths are the real-line values (`Γ(1/4) = 3.6256099082`,
`Γ(1/3) = 2.6789385347`, `Γ(2) = 1`, `Γ(1/2) = √π = 1.7724538509`;
Python `math.gamma` cross-check).  Witnesses are `Rat × Rat` pairs;
distance is `Complex.abs` (`‖·‖`).
Real costs for comparison: `gamma_quarter_le` 26834, `gamma_third_ge`
26927, `gamma_quarter_approx` 27460 heartbeats.
-/

set_option maxHeartbeats 2203 in
-- CG1: port of `gamma_quarter_approx`: `Γ(1/4) = 3.6256099082`. (3.62561, 0)
public def cx_gamma_quarter : { p : Rat × Rat //
    ‖Complex.Gamma ((1 / 4 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < (10 : ℝ) ^ (-5 : ℤ) } := by
  lynth
/-- info: 'cx_gamma_quarter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cx_gamma_quarter._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_gamma_quarter
#eval! cx_gamma_quarter.1

set_option maxHeartbeats 2200 in
-- CG2: `Γ(1/3) = 2.6789385347` (via reflection, as in the real case).
public def cx_gamma_third : { p : Rat × Rat //
    ‖Complex.Gamma ((1 / 3 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < (10 : ℝ) ^ (-5 : ℤ) } := by
  lynth
/-- info: 'cx_gamma_third' depends on axioms: [propext, Classical.choice, Quot.sound, cx_gamma_third._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_gamma_third
#eval! cx_gamma_third.1

set_option maxHeartbeats 1682 in
-- CG3: `Γ(2) = 1`. (1, 0)
public def cx_gamma_two : { p : Rat × Rat //
    ‖Complex.Gamma 2 - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'cx_gamma_two' depends on axioms: [propext, Classical.choice, Quot.sound, cx_gamma_two._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_gamma_two
#eval! cx_gamma_two.1

set_option maxHeartbeats 2177 in
-- CG4: `Γ(1/2) = √π = 1.7724538509`. (1.772454, 0)
public def cx_gamma_half : { p : Rat × Rat //
    ‖Complex.Gamma ((1 / 2 : ℝ) : ℂ) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_gamma_half' depends on axioms: [propext, Classical.choice, Quot.sound, cx_gamma_half._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_gamma_half
#eval! cx_gamma_half.1

set_option maxHeartbeats 2293 in
-- CG5 (own, complex argument): `Γ(1+I) = 0.4980156681 - 0.1549498283·I`.
public def cx_gamma_one_add_I : { p : Rat × Rat //
    ‖Complex.Gamma (1 + Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖
      < 1 / 1000000 } := by
  lynth
/-- info: 'cx_gamma_one_add_I' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cx_gamma_one_add_I._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_gamma_one_add_I
#eval! cx_gamma_one_add_I.1
