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

/-- **MP07** — `zeta_cos_add_three`: `riemannZeta, cos` composed in one expression, evaluated at `s
= cos(1/3) + 3`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `1.086216932382800592904459` /
`1.086216932382800592904459` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `54310846619/50000000000`, within
`2.8e-12` -- is recorded here only, never in the goal.

zeta at an irrational argument off the real axis's critical strip.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def zeta_cos_add_three : { x : Rat // abs ((riemannZeta (Real.cos (1 / 3) + 3)).re - x) < 1 / 1000000 } := by lynth

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

/-- **MP26** — `sqrt_agm`: `sqrt, agm` composed in one expression, evaluated at `x = 1, y = 2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `1.2069759861102900000418` /
`1.2069759861102900000418` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `120697598611/100000000000`, within
`2.9e-13` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def sqrt_agm : { x : Rat // abs (Real.sqrt (((NNReal.agm 1 2 : NNReal) : ℝ)) - x) < 1 / 1000000 } := by lynth

/-- **MP27** — `sqrt_digamma_add_exp`: `sqrt, digamma, exp` composed in one expression, evaluated at
`x = 3`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/10000`. Arb encloses the composition in `1.136073842789239396466883` /
`1.136073842789239396466883` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `113607384279/100000000000`, within
`7.61e-13` -- is recorded here only, never in the goal.

.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def sqrt_digamma_add_exp : { x : Rat // abs (Real.sqrt ((Complex.digamma 3).re + Real.exp (-1)) - x) < 1 / 10000 } := by lynth

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

/-- **MP30** — `log_mul_hypergeometric`: `log, ordinaryHypergeometric` composed in one expression,
evaluated at `a = b = 1, c = 2, x = 1/2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `0.9609060278364028873099301` /
`0.9609060278364028873099301` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `240226506959/250000000000`, within
`4.03e-13` -- is recorded here only, never in the goal.

the Gaussian 2F1 is now a mathlib declaration (`ordinaryHypergeometric`, notation `₂F₁`); 2F1(1,
1; 2; 1/2) = 2 log 2, so the composition multiplies the series value by another log.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def log_mul_hypergeometric : { x : Rat // abs (Real.log 2 * ordinaryHypergeometric (1 : ℝ) 1 1 ((1 / 2 : ℝ)) - x) < 1 / 1000000 } := by lynth

/-- **MP31** — `regularized_gauss_hypergeometric_neg5`: `regularizedGaussHGFun` composed in one
expression, evaluated at `a = 1, b = 2, c = 3, z = -5`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `0.1283296212308777939359317` /
`0.1283296212308777939359317` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `128329621231/1000000000000`, within
`1.22e-13` -- is recorded here only, never in the goal.

the regularized Gaussian hypergeometric function (`Complex.regularizedGaussHGFun`, i.e.
2F1/Gamma(c)) evaluated outside the unit disc: the same value as the Arb specialized kernel D06
check.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def regularized_gauss_hypergeometric_neg5 : { x : Rat // abs ((Complex.regularizedGaussHGFun 1 2 3 (-5)).re - x) < 1 / 1000000 } := by lynth

/-- **MP32** — `regularized_pfq_3f2`: `regularizedHGFun` composed in one expression, evaluated at
`3F2: a = (1, 1, 1), b = (2, 2), z = 1/2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `1.164481052930024906899575` /
`1.164481052930024906899575` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `116448105293/100000000000`, within
`2.5e-14` -- is recorded here only, never in the goal.

3F2 -- five parameters, no specialized Arb kernel (the general hypgeom path is used), normalized
by Gamma(2)Gamma(2) = 1.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def regularized_pfq_3f2 : { x : Rat // abs ((Complex.regularizedHGFun {1, 1, 1} {2, 2} (1 / 2)).re - x) < 1 / 1000000 } := by lynth

/-- **MP33** — `regularized_pfq_2f3`: `regularizedHGFun` composed in one expression, evaluated at
`2F3: a = (1, 2), b = (3, 4, 5), z = 1/4`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `0.003501339116694342137175999` /
`0.003501339116694342137175999` (it is far narrower than the tolerance), which is the
certificate that such an `x` exists; the concrete witness Arb found --
`350133911669/100000000000000`, within `4.34e-15` -- is recorded here only, never in the goal.

2F3 -- the normalization divisor Gamma(3)Gamma(4)Gamma(5) = 288 is not 1, so this is the case
that actually distinguishes the regularized definition.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def regularized_pfq_2f3 : { x : Rat // abs ((Complex.regularizedHGFun {1, 2} {3, 4, 5} (1 / 4)).re - x) < 1 / 1000000 } := by lynth

/-- **MP34** — `regularized_pfq_4f3`: `regularizedHGFun` composed in one expression, evaluated at
`4F3: a = (1, 1, 1, 1), b = (2, 2, 2), z = 1/4`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `1.033845583186293159982938` /
`1.033845583186293159982938` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `103384558319/100000000000`, within
`3.71e-12` -- is recorded here only, never in the goal.

4F3 -- seven parameters, three more than any specialized form.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def regularized_pfq_4f3 : { x : Rat // abs ((Complex.regularizedHGFun {1, 1, 1, 1} {2, 2, 2} (1 / 4)).re - x) < 1 / 1000000 } := by lynth

/-- **MP35** — `regularized_pfq_terminating_3f2`: `regularizedHGFun` composed in one expression,
evaluated at `3F2: a = (-3, 1, 1), b = (2, 2), z = 1/2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Arb encloses the composition in `0.7005208333333333703407675` /
`0.7005208333333333703407675` (it is far narrower than the tolerance), which is the certificate
that such an `x` exists; the concrete witness Arb found -- `700520833333/1000000000000`, within
`3.33e-13` -- is recorded here only, never in the goal.

a negative-integer numerator parameter terminates the series: the value is the exact rational
269/384 (Arb ball of radius 0), the only composition here with an exact answer.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def regularized_pfq_terminating_3f2 : { x : Rat // abs ((Complex.regularizedHGFun {(-3 : ℂ), 1, 1} {2, 2} (1 / 2)).re - x) < 1 / 1000000 } := by lynth

-- Axiom footprint checks.
/-- info: 'IntervalArith.exp_sin_add_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_sin_add_cos
/-- info: 'IntervalArith.sin_exp_mul_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sin_exp_mul_cos
/-- info: 'IntervalArith.gamma_sin_add_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gamma_sin_add_two
/-- info: 'IntervalArith.log_gamma_add_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms log_gamma_add_sqrt
/-- info: 'IntervalArith.tan_sinh_mul_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tan_sinh_mul_cos
/-- info: 'IntervalArith.cosh_sin_add_arctan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cosh_sin_add_arctan
/-- info: 'IntervalArith.zeta_cos_add_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zeta_cos_add_three
/-- info: 'IntervalArith.arcsin_tanh_mul_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arcsin_tanh_mul_cos
/-- info: 'IntervalArith.arccos_sinh_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arccos_sinh_mul_exp
/-- info: 'IntervalArith.sinc_exp_mul_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sinc_exp_mul_sin
/-- info: 'IntervalArith.cot_sinh_add_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cot_sinh_add_two
/-- info: 'IntervalArith.arsinh_cos_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arsinh_cos_mul_exp
/-- info: 'IntervalArith.arcosh_exp_add_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arcosh_exp_add_sin
/-- info: 'IntervalArith.artanh_sin_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms artanh_sin_mul_exp
/-- info: 'IntervalArith.logb_exp_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logb_exp_sin
/-- info: 'IntervalArith.exp_chebyshev_t_add_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_chebyshev_t_add_sin
/-- info: 'IntervalArith.log_chebyshev_u_add_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms log_chebyshev_u_add_three
/-- info: 'IntervalArith.cos_euler_add_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cos_euler_add_sqrt
/-- info: 'IntervalArith.sinh_bell_over_hundred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sinh_bell_over_hundred
/-- info: 'IntervalArith.exp_bernoulli_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_bernoulli_poly
/-- info: 'IntervalArith.cos_bernoulli_four_add_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cos_bernoulli_four_add_sqrt
/-- info: 'IntervalArith.arctan_log_ten_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arctan_log_ten_mul_exp
/-- info: 'IntervalArith.log_two_gamma_div_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms log_two_gamma_div_exp
/-- info: 'IntervalArith.sqrt_pi_mul_tanh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqrt_pi_mul_tanh
/-- info: 'IntervalArith.choose_div_factorial_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choose_div_factorial_mul_sqrt
/-- info: 'IntervalArith.sqrt_agm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqrt_agm
/-- info: 'IntervalArith.sqrt_digamma_add_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqrt_digamma_add_exp
/-- info: 'IntervalArith.pochhammer_four_third_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pochhammer_four_third_mul_exp
/-- info: 'IntervalArith.rpow_sin_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rpow_sin_exponent
/-- info: 'IntervalArith.log_mul_hypergeometric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms log_mul_hypergeometric
/-- info: 'IntervalArith.regularized_gauss_hypergeometric_neg5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms regularized_gauss_hypergeometric_neg5
/-- info: 'IntervalArith.regularized_pfq_3f2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms regularized_pfq_3f2
/-- info: 'IntervalArith.regularized_pfq_2f3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms regularized_pfq_2f3
/-- info: 'IntervalArith.regularized_pfq_4f3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms regularized_pfq_4f3
/-- info: 'IntervalArith.regularized_pfq_terminating_3f2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms regularized_pfq_terminating_3f2

end IntervalArith

-- The repository convention (`Test/*.lean`, `Test/Grind/README.md`) pins the
-- axiom footprint of every declaration once the goals go through.  Uncomment
-- (and keep the `info` docstring in sync) when a goal starts closing:
--
-- /-- info: 'regularized_pfq_terminating_3f2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- #guard_msgs in
-- #print axioms regularized_pfq_terminating_3f2
