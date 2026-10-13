import Mathlib
import Lynth

/-!
Ports of the transcendental `Test/IntervalArith/Compositions.lean` tests
whose functions all have `Complex.*` alternatives, evaluated on complex
embeddings of the real arguments.  Ground truths are Python `math`
cross-checks (same values as the real versions).  Witnesses are
`Rat × Rat` pairs; distance is `Complex.abs` (`‖·‖`).

Skipped (no `Complex.*` definition, per the porting rule): `arcsin`,
`arccos`, `sinc`, `arsinh`, `arcosh`, `artanh`, `logb` compositions, and
the `Chebyshev`/`bernoulli`/`bell`/`pochhammer`/`choose` polynomial tests.
-/

namespace ComplexIntervalArith

set_option maxHeartbeats 8902 in
/-- port of `exp_sin_add_cos`: `exp (sin (1/2) + cos (1/2)) = 3.8845537039`. -/
def cx_exp_sin_add_cos : { p : Rat × Rat //
    ‖Complex.exp (Complex.sin ((1 / 2 : ℝ) : ℂ) + Complex.cos ((1 / 2 : ℝ) : ℂ))
      - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_exp_sin_add_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_exp_sin_add_cos
#eval! cx_exp_sin_add_cos.1

set_option maxHeartbeats 11860 in
/-- port of `sin_exp_mul_cos`: `sin (exp (1/2) * cos (1/2)) = 0.9923333082`. -/
def cx_sin_exp_mul_cos : { p : Rat × Rat //
    ‖Complex.sin (Complex.exp ((1 / 2 : ℝ) : ℂ) * Complex.cos ((1 / 2 : ℝ) : ℂ))
      - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 10000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_sin_exp_mul_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_sin_exp_mul_cos
#eval! cx_sin_exp_mul_cos.1

set_option maxHeartbeats 43216 in
/-- port of `gamma_sin_add_two`: `Γ (sin (1/2) + 2) = 1.3103836175`. -/
def cx_gamma_sin_add_two : { p : Rat × Rat //
    ‖Complex.Gamma (Complex.sin ((1 / 2 : ℝ) : ℂ) + 2)
      - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_gamma_sin_add_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_gamma_sin_add_two
#eval! cx_gamma_sin_add_two.1

set_option maxHeartbeats 47535 in
/-- port of `log_gamma_add_sqrt`: `log (Γ (1/4) + √2) = 1.6173710558`. -/
def cx_log_gamma_add_sqrt : { p : Rat × Rat //
    ‖Complex.log (Complex.Gamma ((1 / 4 : ℝ) : ℂ) + Complex.sqrt ((2 : ℝ) : ℂ))
      - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_log_gamma_add_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_log_gamma_add_sqrt
#eval! cx_log_gamma_add_sqrt.1

set_option maxHeartbeats 12887 in
/-- port of `tan_sinh_mul_cos`: `tan (sinh (1/3) * cos (1/3)) = 0.3323343589`. -/
def cx_tan_sinh_mul_cos : { p : Rat × Rat //
    ‖Complex.tan (Complex.sinh ((1 / 3 : ℝ) : ℂ) * Complex.cos ((1 / 3 : ℝ) : ℂ))
      - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 100000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_tan_sinh_mul_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_tan_sinh_mul_cos
#eval! cx_tan_sinh_mul_cos.1

set_option maxHeartbeats 13268 in
/-- port of `cosh_sin_add_arctan`: `cosh (sin 1 + arctan 1) = 2.6422320968`. -/
def cx_cosh_sin_add_arctan : { p : Rat × Rat //
    ‖Complex.cosh (Complex.sin 1 + Complex.arctan 1)
      - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_cosh_sin_add_arctan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_cosh_sin_add_arctan
#eval! cx_cosh_sin_add_arctan.1

set_option maxHeartbeats 11113 in
/-- port of `cot_sinh_add_two`: `cot (sinh (1/2) + 2) = -1.3992665826`. -/
def cx_cot_sinh_add_two : { p : Rat × Rat //
    ‖Complex.cot (Complex.sinh ((1 / 2 : ℝ) : ℂ) + 2)
      - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_cot_sinh_add_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_cot_sinh_add_two
#eval! cx_cot_sinh_add_two.1

set_option maxHeartbeats 20163 in
/-- port of `cos_euler_add_sqrt`: `cos (γ + √2) = -0.4083382658`. -/
def cx_cos_euler_add_sqrt : { p : Rat × Rat //
    ‖Complex.cos (((Real.eulerMascheroniConstant + Real.sqrt 2 : ℝ)) : ℂ)
      - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < Real.pi / 100 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_cos_euler_add_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_cos_euler_add_sqrt
#eval! cx_cos_euler_add_sqrt.1

set_option maxHeartbeats 23302 in
/-- port of `arctan_log_ten_mul_exp`: `arctan (log 10 * exp (-1)) = 0.7027927512`. -/
def cx_arctan_log_ten_mul_exp : { p : Rat × Rat //
    ‖Complex.arctan (Complex.log 10 * Complex.exp (-1))
      - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_arctan_log_ten_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_arctan_log_ten_mul_exp
#eval! cx_arctan_log_ten_mul_exp.1

set_option maxHeartbeats 48581 in
/-- port of `log_two_gamma_div_exp`: `log 2 * Γ (1/4) / exp 1 = 0.9245109390`. -/
def cx_log_two_gamma_div_exp : { p : Rat × Rat //
    ‖Complex.log 2 * Complex.Gamma ((1 / 4 : ℝ) : ℂ) / Complex.exp 1
      - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 100000000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_log_two_gamma_div_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_log_two_gamma_div_exp
#eval! cx_log_two_gamma_div_exp.1

set_option maxHeartbeats 8434 in
/-- port of `sqrt_pi_mul_tanh`: `√π * tanh (1/2) = 0.8190813350`. -/
def cx_sqrt_pi_mul_tanh : { p : Rat × Rat //
    ‖Complex.sqrt ((Real.pi : ℝ) : ℂ) * Complex.tanh ((1 / 2 : ℝ) : ℂ)
      - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < Real.pi / (10 : ℝ) ^ 7 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_sqrt_pi_mul_tanh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cx_sqrt_pi_mul_tanh
#eval! cx_sqrt_pi_mul_tanh.1

end ComplexIntervalArith
