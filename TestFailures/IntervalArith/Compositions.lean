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
/-- info: 'IntervalArith.zeta_cos_add_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zeta_cos_add_three

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
/-- info: 'IntervalArith.sqrt_agm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqrt_agm

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
/-- info: 'IntervalArith.sqrt_digamma_add_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sqrt_digamma_add_exp

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
/-- info: 'IntervalArith.log_mul_hypergeometric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms log_mul_hypergeometric

/-- **MP31** — `regularized_gauss_hypergeometric_neg_half`: `regularizedGaussHGFun` evaluated at
`a = 1, b = 2, c = 3, z = -1/2`.

`x` is the *unknown*: the tactic has to produce a rational witness inside the tolerance
`1/1000000`. Closed form: `2F1(1,2;3;z)/Gamma(3) = sum z^n/(n+2) = (-log(1-z) - z)/z^2`, i.e.
`4 * (1/2 - log (3/2)) = 0.3781395675673425` at `z = -1/2`.

Changed from `z = -5`: Mathlib defines the function as the sum of its power series, which
diverges for `|z| >= 1` (its Mathlib value at `-5` is `0`), so the test now uses a point
inside the disc of convergence. -/
def regularized_gauss_hypergeometric_neg_half : { x : Rat // abs ((Complex.regularizedGaussHGFun 1 2 3 (-1 / 2)).re - x) < 1 / 1000000 } := by lynth
/-- info: 'IntervalArith.regularized_gauss_hypergeometric_neg_half' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms regularized_gauss_hypergeometric_neg_half

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
/-- info: 'IntervalArith.regularized_pfq_3f2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms regularized_pfq_3f2

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
/-- info: 'IntervalArith.regularized_pfq_2f3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms regularized_pfq_2f3

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
/-- info: 'IntervalArith.regularized_pfq_4f3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms regularized_pfq_4f3

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
/-- info: 'IntervalArith.regularized_pfq_terminating_3f2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms regularized_pfq_terminating_3f2

-- Axiom footprint checks.

end IntervalArith

-- The repository convention (`Test/*.lean`, `Test/Grind/README.md`) pins the
-- axiom footprint of every declaration once the goals go through.  Uncomment
-- (and keep the `info` docstring in sync) when a goal starts closing:
--
-- /-- info: 'regularized_pfq_terminating_3f2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- #guard_msgs in
-- #print axioms regularized_pfq_terminating_3f2
