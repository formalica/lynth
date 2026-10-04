import Mathlib
import Lynth

/-!
The coverage layer, by **composition**: each declaration is a
single expression tree in which two or three special functions are nested
(`Real.exp (Real.sin x + Real.cos x)`, `Real.arcsin (Real.tanh a * Real.cos b)`,
...), so one Arb evaluation carries several functions at once.  29 goals of the
requested shape

  `def name : { x : Rat // |<composition> - x| < <tolerance> } := by lynth`

with tolerances `1/10000`, `1/100000`, `1/1000000`, `1/100000000` and the
irrational `Real.pi / 100`, `Real.pi / 1000`, `Real.pi / (10 : ℝ) ^ 7`.
Functions covered here: exp, log, logb, sqrt, rpow, sinc, sin, cos, tan, cot,
arcsin, arccos, arctan, sinh, cosh, tanh, arsinh, arcosh, artanh, Gamma,
riemannZeta, pi, Euler-Mascheroni, digamma, agm, Pochhammer, Chebyshev T/U,
Bernoulli numbers and polynomials, Bell numbers, binomial coefficients,
factorials, and the hypergeometric layer: `ordinaryHypergeometric` (unregularized
2F1, notation `₂F₁`), `Complex.regularizedGaussHGFun` (regularized 2F1) and
`Complex.regularizedHGFun` (the general pFq: 3F2, 2F3, 4F3 and a terminating 3F2
with an exact rational value).  The Arb kernels behind them are the *specialized*
`hypgeom_0f1` / `hypgeom_1f1` / `hypgeom_2f1` / `hypgeom_u` (zoo family D06,
including the `regularized=True` and Gauss-transformation-flag paths) and the
*general* `hypgeom` for the parameter vectors with no specialized implementation
(zoo family D14).  No function is nested inside its own inverse (never `arcsin (sin
x)`), which `arb/compositions.py:audit_no_inverse_pairs()` checks mechanically.
Ground truth: `arb/CERTIFICATES.md` (MP01-MP35).
-/

namespace IntervalArith


set_option maxHeartbeats 6480 in
/-- **MP01** — `exp_sin_add_cos`: `exp, sin, cos` composed in one expression, evaluated at `x =
1/2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `3.884553703918718792209575` /
`3.884553703918718792209575` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `48556921299/12500000000`, within
`1.28e-12` -- is recorded here only, never in the goal.

exp of a sum of two trigonometric values.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def exp_sin_add_cos : { x : Rat // abs (Real.exp (Real.sin (1 / 2) + Real.cos (1 / 2)) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.exp_sin_add_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_sin_add_cos

set_option maxHeartbeats 6747 in
/-- **MP02** — `sin_exp_mul_cos`: `sin, exp, cos` composed in one expression, evaluated at `x =
1/2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/10000`. Arb encloses the composition in `0.9923333081546303890974059` /
`0.9923333081546303890974059` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `198466661631/200000000000`, within
`3.7e-13` -- is recorded here only, never in the goal.

trigonometric function of a product of exp and cos.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def sin_exp_mul_cos : { x : Rat // abs (Real.sin (Real.exp (1 / 2) * Real.cos (1 / 2)) - x) < 1 / 10000 } := by lynth
/-- info: 'IntervalArith.sin_exp_mul_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sin_exp_mul_cos

set_option maxHeartbeats 28679 in
/-- **MP03** — `gamma_sin_add_two`: `Gamma, sin` composed in one expression, evaluated at `x = 1/2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `1.310383617530037625442674` /
`1.310383617530037625442674` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `131038361753/100000000000`, within
`3.76e-14` -- is recorded here only, never in the goal.

Gamma at an irrational argument built from sin.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def gamma_sin_add_two : { x : Rat // abs (Real.Gamma (Real.sin (1 / 2) + 2) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.gamma_sin_add_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gamma_sin_add_two

set_option maxHeartbeats 28865 in
/-- **MP04** — `log_gamma_add_sqrt`: `log, Gamma, sqrt` composed in one expression, evaluated at `x
= 1/4, 2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `1.617371055794269318894862` /
`1.617371055794269318894862` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `161737105579/100000000000`, within
`4.27e-12` -- is recorded here only, never in the goal.

log of a sum of two irrational special values.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def log_gamma_add_sqrt : { x : Rat // abs (Real.log (Real.Gamma (1 / 4) + Real.sqrt 2) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.log_gamma_add_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms log_gamma_add_sqrt

set_option maxHeartbeats 9274 in
/-- **MP05** — `tan_sinh_mul_cos`: `tan, sinh, cos` composed in one expression, evaluated at `x =
1/3`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/100000`. Arb encloses the composition in `0.3323343589143425980125812` /
`0.3323343589143425980125812` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `166167179457/500000000000`, within
`3.43e-13` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def tan_sinh_mul_cos : { x : Rat // abs (Real.tan (Real.sinh (1 / 3) * Real.cos (1 / 3)) - x) < 1 / 100000 } := by lynth
/-- info: 'IntervalArith.tan_sinh_mul_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tan_sinh_mul_cos

set_option maxHeartbeats 14432 in
/-- **MP06** — `cosh_sin_add_arctan`: `cosh, sin, arctan` composed in one expression, evaluated at
`x = 1`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `2.642232096837978438941263` /
`2.642232096837978438941263` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `66055802421/25000000000`, within
`2.02e-12` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def cosh_sin_add_arctan : { x : Rat // abs (Real.cosh (Real.sin 1 + Real.arctan 1) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.cosh_sin_add_arctan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosh_sin_add_arctan

set_option maxHeartbeats 11465 in
/-- **MP08** — `arcsin_tanh_mul_cos`: `arcsin, tanh, cos` composed in one expression, evaluated at
`x = 1/2, 1/3`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `0.4519058027980534797407586` /
`0.4519058027980534797407586` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `225952901399/500000000000`, within
`5.35e-14` -- is recorded here only, never in the goal.

arcsin of a product of an unrelated hyperbolic and trig value (deliberately not arcsin (sin _)).

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def arcsin_tanh_mul_cos : { x : Rat // abs (Real.arcsin (Real.tanh (1 / 2) * Real.cos (1 / 3)) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.arcsin_tanh_mul_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arcsin_tanh_mul_cos

set_option maxHeartbeats 13476 in
/-- **MP09** — `arccos_sinh_mul_exp`: `arccos, sinh, exp` composed in one expression, evaluated at
`x = 1/2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`pi/1000`. Arb encloses the composition in `1.249222313585256483037256` /
`1.249222313585256483037256` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `124922231359/100000000000`, within
`4.74e-12` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def arccos_sinh_mul_exp : { x : Rat // abs (Real.arccos (Real.sinh (1 / 2) * Real.exp (-(1 / 2))) - x) < Real.pi / 1000 } := by lynth
/-- info: 'IntervalArith.arccos_sinh_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arccos_sinh_mul_exp

set_option maxHeartbeats 6809 in
/-- **MP10** — `sinc_exp_mul_sin`: `sinc, exp, sin` composed in one expression, evaluated at `x =
1`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `0.9841051301542578233494396` /
`0.9841051301542578233494396` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `492052565077/500000000000`, within
`2.58e-13` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def sinc_exp_mul_sin : { x : Rat // abs (Real.sinc (Real.exp (-1) * Real.sin 1) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.sinc_exp_mul_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sinc_exp_mul_sin

set_option maxHeartbeats 8587 in
/-- **MP11** — `cot_sinh_add_two`: `cot, sinh` composed in one expression, evaluated at `x = 1/2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `-1.399266582630767086214973` /
`-1.399266582630767086214973` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `-139926658263/100000000000`, within
`7.67e-13` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def cot_sinh_add_two : { x : Rat // abs (Real.cot (Real.sinh (1 / 2) + 2) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.cot_sinh_add_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cot_sinh_add_two

set_option maxHeartbeats 8319 in
/-- **MP12** — `arsinh_cos_mul_exp`: `arsinh, cos, exp` composed in one expression, evaluated at `x
= 1/2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `1.164936849480898262143569` /
`1.164936849480898262143569` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `29123421237/25000000000`, within
`8.98e-13` -- is recorded here only, never in the goal.

arsinh fed by cos and exp -- no sinh anywhere, so no inverse pair.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def arsinh_cos_mul_exp : { x : Rat // abs (Real.arsinh (Real.cos (1 / 2) * Real.exp (1 / 2)) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.arsinh_cos_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arsinh_cos_mul_exp

set_option maxHeartbeats 6956 in
/-- **MP13** — `arcosh_exp_add_sin`: `arcosh, exp, sin` composed in one expression, evaluated at `x
= 1/2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/100000000`. Arb encloses the composition in `1.38797106553816318452732` /
`1.38797106553816318452732` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `69398553277/50000000000`, within
`1.84e-12` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def arcosh_exp_add_sin : { x : Rat // abs (Real.arcosh (Real.exp (1 / 2) + Real.sin (1 / 2)) - x) < 1 / 100000000 } := by lynth
/-- info: 'IntervalArith.arcosh_exp_add_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arcosh_exp_add_sin

set_option maxHeartbeats 7958 in
/-- **MP14** — `artanh_sin_mul_exp`: `artanh, sin, exp` composed in one expression, evaluated at `x
= 1/4`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `0.09126739995728096188631895` /
`0.09126739995728096188631895` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `912673999573/10000000000000`, within
`1.9e-14` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def artanh_sin_mul_exp : { x : Rat // abs (Real.artanh (Real.sin (1 / 4) * Real.exp (-1)) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.artanh_sin_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms artanh_sin_mul_exp

set_option maxHeartbeats 8730 in
/-- **MP15** — `logb_exp_sin`: `logb, exp, sin` composed in one expression, evaluated at `base 2, x
= 1`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `1.73108625822944350858279` /
`1.73108625822944350858279` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `173108625823/100000000000`, within
`5.56e-13` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def logb_exp_sin : { x : Rat // abs (Real.logb 2 (Real.exp (Real.sin 1) + 1) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.logb_exp_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logb_exp_sin

set_option maxHeartbeats 9646 in
/-- **MP16** — `exp_chebyshev_t_add_sin`: `Chebyshev T, exp, sin` composed in one expression,
evaluated at `n = 4, x = 1/3`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `1.992324568361183878550946` /
`1.992324568361183878550946` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `49808114209/25000000000`, within
`1.18e-12` -- is recorded here only, never in the goal.

an exact rational polynomial value fed into exp together with sin.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def exp_chebyshev_t_add_sin : { x : Rat // abs (Real.exp ((((Polynomial.Chebyshev.T ℚ 4).eval (1 / 3) : ℚ) : ℝ) + Real.sin (1 / 2)) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.exp_chebyshev_t_add_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_chebyshev_t_add_sin

set_option maxHeartbeats 6577 in
/-- **MP17** — `log_chebyshev_u_add_three`: `Chebyshev U, log` composed in one expression, evaluated
at `n = 4, x = 1/3`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `1.052288216993871206028643` /
`1.052288216993871206028643` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `105228821699/100000000000`, within
`3.87e-12` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def log_chebyshev_u_add_three : { x : Rat // abs (Real.log (3 + (((Polynomial.Chebyshev.U ℚ 4).eval (1 / 3) : ℚ) : ℝ)) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.log_chebyshev_u_add_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms log_chebyshev_u_add_three

set_option maxHeartbeats 8687 in
/-- **MP18** — `cos_euler_add_sqrt`: `cos, eulerMascheroniConstant, sqrt` composed in one
expression, evaluated at `x = gamma + sqrt 2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`pi/100`. Arb encloses the composition in `-0.4083382657824746742036837` /
`-0.4083382657824746742036837` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `-204169132891/500000000000`, within
`4.75e-13` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def cos_euler_add_sqrt : { x : Rat // abs (Real.cos (Real.eulerMascheroniConstant + Real.sqrt 2) - x) < Real.pi / 100 } := by lynth
/-- info: 'IntervalArith.cos_euler_add_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cos_euler_add_sqrt

set_option maxHeartbeats 9317 in
/-- **MP19** — `sinh_bell_over_hundred`: `sinh, Nat.bell` composed in one expression, evaluated at
`n = 5`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `0.5437535508643459580824242` /
`0.5437535508643459580824242` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `33984596929/62500000000`, within
`3.46e-13` -- is recorded here only, never in the goal.

integer-valued Bell number (52) inside a hyperbolic function.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def sinh_bell_over_hundred : { x : Rat // abs (Real.sinh (((Nat.bell 5 : ℕ) : ℝ) / 100) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.sinh_bell_over_hundred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sinh_bell_over_hundred

set_option maxHeartbeats 16266 in
/-- **MP20** — `exp_bernoulli_poly`: `Polynomial.bernoulli, exp` composed in one expression,
evaluated at `n = 2, x = 1/3`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `1.891918937813530821046015` /
`1.891918937813530821046015` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `189191893781/100000000000`, within
`3.53e-12` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def exp_bernoulli_poly : { x : Rat // abs (Real.exp ((((Polynomial.bernoulli 2).eval (1 / 3) : ℚ) : ℝ)) * 2 - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.exp_bernoulli_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_bernoulli_poly

set_option maxHeartbeats 4911 in
/-- **MP21** — `cos_bernoulli_four_add_sqrt`: `cos, bernoulli, sqrt` composed in one expression,
evaluated at `n = 4`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `0.188776501952059583278043` /
`0.188776501952059583278043` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `2949632843/15625000000`, within
`5.96e-14` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def cos_bernoulli_four_add_sqrt : { x : Rat // abs (Real.cos ((bernoulli 4 : ℝ) + Real.sqrt 2) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.cos_bernoulli_four_add_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cos_bernoulli_four_add_sqrt

set_option maxHeartbeats 10982 in
/-- **MP22** — `arctan_log_ten_mul_exp`: `arctan, log 10, exp` composed in one expression, evaluated
at `x = log 10 / e`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `0.702792751231606671602492` /
`0.702792751231606671602492` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `5490568369/7812500000`, within
`3.93e-13` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def arctan_log_ten_mul_exp : { x : Rat // abs (Real.arctan (Real.log 10 * Real.exp (-1)) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.arctan_log_ten_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arctan_log_ten_mul_exp

set_option maxHeartbeats 29195 in
/-- **MP23** — `log_two_gamma_div_exp`: `log 2, Gamma, exp` composed in one expression, evaluated at
`x = 1/4`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/100000000`. Arb encloses the composition in `0.9245109389995986859389632` /
`0.9245109389995986859389632` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `924510939/1000000000`, within
`4.01e-13` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def log_two_gamma_div_exp : { x : Rat // abs (Real.log 2 * Real.Gamma (1 / 4) / Real.exp 1 - x) < 1 / 100000000 } := by lynth
/-- info: 'IntervalArith.log_two_gamma_div_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms log_two_gamma_div_exp

set_option maxHeartbeats 6151 in
/-- **MP24** — `sqrt_pi_mul_tanh`: `sqrt, pi, tanh` composed in one expression, evaluated at `x =
1/2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`pi/10000000`. Arb encloses the composition in `0.8190813349550142286048526` /
`0.8190813349550142286048526` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `163816266991/200000000000`, within
`1.42e-14` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def sqrt_pi_mul_tanh : { x : Rat // abs (Real.sqrt Real.pi * Real.tanh (1 / 2) - x) < Real.pi / (10 : ℝ) ^ 7 } := by lynth
/-- info: 'IntervalArith.sqrt_pi_mul_tanh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqrt_pi_mul_tanh

set_option maxHeartbeats 2319 in
/-- **MP25** — `choose_div_factorial_mul_sqrt`: `Nat.choose, Nat.factorial, sqrt` composed in one
expression, evaluated at `n = 7, k = 3`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `2.062394778460763689054147` /
`2.062394778460763689054147` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `103119738923/50000000000`, within
`7.64e-13` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def choose_div_factorial_mul_sqrt : { x : Rat // abs (((Nat.choose 7 3 : ℕ) : ℝ) / ((Nat.factorial 4 : ℕ) : ℝ) * Real.sqrt 2 - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.choose_div_factorial_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choose_div_factorial_mul_sqrt

set_option maxHeartbeats 6951 in
/-- **MP28** — `pochhammer_four_third_mul_exp`: `ascPochhammer, exp` composed in one expression,
evaluated at `n = 4, x = 1/3`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `1.27168201886424503399553` /
`1.27168201886424503399553` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `63584100943/50000000000`, within
`4.25e-12` -- is recorded here only, never in the goal.

(1/3)_4 = 280/81 fed into a product with exp (-1).

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def pochhammer_four_third_mul_exp : { x : Rat // abs ((((ascPochhammer ℚ 4).eval (1 / 3) : ℚ) : ℝ) * Real.exp (-1) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.pochhammer_four_third_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pochhammer_four_third_mul_exp

set_option maxHeartbeats 6599 in
/-- **MP29** — `rpow_sin_exponent`: `rpow, sin` composed in one expression, evaluated at `base 2,
exponent sin(1/2) + 1/4`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `1.657978775744291199956137` /
`1.657978775744291199956137` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `82898938787/50000000000`, within
`4.29e-12` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def rpow_sin_exponent : { x : Rat // abs ((2 : ℝ) ^ (Real.sin (1 / 2) + 1 / 4) - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.rpow_sin_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rpow_sin_exponent
