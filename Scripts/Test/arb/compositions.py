#!/usr/bin/env python3
"""
compositions.py -- composition tests: one Arb evaluation per test, covering many
special functions at once by *nesting* them (`f (g x + h x)`), as requested.

Three shapes:

  point  :  def <name> : { x : Rat // abs (<composition>) < tol } := by lynth
  nat    :  def <name> : { n : Nat // n = ⌊<composition>⌋ } := by lynth
  range  :  def <name> : { p : Rat × Rat //
                abs (rangeSup (fun r => <composition in r>) a b - p.1) < tol ∧
                abs (rangeInf (fun r => <composition in r>) a b - p.2) < tol } := by lynth

Design rules (from the review of the first attempt):

  * **Composition, not conjunction.**  Each test is one expression tree, so a
    single goal exercises several functions: `exp (sin x + cos x)` touches
    `exp`, `sin` and `cos` at once.  The old "one theorem per function family
    with `∧`-joined statements" shape is gone.
  * **No inverse pairs.**  Nothing like `arcsin (sin x)`, `log (exp x)`,
    `sqrt (x ^ 2)` or `tan (arctan x)`: `simp`/`rw` could discharge those
    without doing any interval arithmetic, which is the opposite of the point.
    Inverse *functions* (arcsin, arcosh, …) do appear -- but always applied to
    something built out of *unrelated* functions, and never to their own inverse.
  * **Independent reference.**  Every entry carries both an Arb lambda and an
    mpmath lambda; the test passes only when Arb's rigorous enclosure contains
    the mpmath value (two implementations, written separately, must agree).

`Nat` tests are stronger than they look: `n = ⌊f x⌋` is proved by *certifying the
floor*, i.e. the Arb enclosure of `f x` must lie strictly inside `(n, n+1)`, and
the certificate records the distance to the two integers as the margin.
"""

from __future__ import annotations

from fractions import Fraction

import mpmath

from flint import ctx

import tools as T
from tools import A, I, F, lb, ub, Pi

mp = mpmath.mp
mp.dps = 40

M = lambda v: mpmath.mpf(v)          # reference value (mpmath, 40 digits)
P = lambda p, q=1: Fraction(p, q)    # exact rational reference
H = Fraction(1, 2)


def C(cid, kind, name, lean, py, ref, at, box=None, tol=None,
      note="", functions="", wrap=""):
    """`lean` is the *function expression*; for the discrete tests `wrap` holds
    the rounding operator the goal applies to it (`"⌊⌋"` / `"⌈⌉"`), which is how
    the Lean goal text is assembled (`lean_goal_text`)."""
    return dict(id=cid, kind=kind, name=name, lean=lean, py=py, ref=ref, at=at,
                box=box, tol=tol or Fraction(1, 10 ** 6),
                note=note, functions=functions, wrap=wrap)


def lean_goal_text(c):
    """The expression as it appears inside the Lean goal (with the rounding
    operator for the discrete tests).  The subscript in `⌊x⌋₊` is mathlib's
    `Nat.floor` (`ℝ → ℕ`); the plain `⌊x⌋` would be `Int.floor` and would make
    the `{ n : Nat // ... }` goal ill-typed."""
    return c["wrap"][0] + c["lean"] + c["wrap"][1:] if c["wrap"] else c["lean"]


# --------------------------------------------------------------------------
# MP1..MP29 -- point compositions (each one test, several functions)
# --------------------------------------------------------------------------
POINT = [
    C("MP01", "point", "exp_sin_add_cos",
      "Real.exp (Real.sin (1 / 2) + Real.cos (1 / 2))",
      lambda: (A(H).sin() + A(H).cos()).exp(),
      lambda: mpmath.exp(mpmath.sin(mpmath.mpf(1) / 2) + mpmath.cos(mpmath.mpf(1) / 2)),
      "x = 1/2", functions="exp, sin, cos",
      note="exp of a sum of two trigonometric values"),

    C("MP02", "point", "sin_exp_mul_cos",
      "Real.sin (Real.exp (1 / 2) * Real.cos (1 / 2))",
      lambda: (A(H).exp() * A(H).cos()).sin(),
      lambda: mpmath.sin(mpmath.exp(mpmath.mpf(1) / 2) * mpmath.cos(mpmath.mpf(1) / 2)),
      "x = 1/2", functions="sin, exp, cos",
      note="trigonometric function of a product of exp and cos"),

    C("MP03", "point", "gamma_sin_add_two",
      "Real.Gamma (Real.sin (1 / 2) + 2)",
      lambda: (A(H).sin() + 2).gamma(),
      lambda: mpmath.gamma(mpmath.sin(mpmath.mpf(1) / 2) + 2),
      "x = 1/2", functions="Gamma, sin",
      note="Gamma at an irrational argument built from sin"),

    C("MP04", "point", "log_gamma_add_sqrt",
      "Real.log (Real.Gamma (1 / 4) + Real.sqrt 2)",
      lambda: (A(Fraction(1, 4)).gamma() + A(2).sqrt()).log(),
      lambda: mpmath.log(mpmath.gamma(mpmath.mpf(1) / 4) + mpmath.sqrt(2)),
      "x = 1/4, 2", functions="log, Gamma, sqrt",
      note="log of a sum of two irrational special values"),

    C("MP05", "point", "tan_sinh_mul_cos",
      "Real.tan (Real.sinh (1 / 3) * Real.cos (1 / 3))",
      lambda: (A(Fraction(1, 3)).sinh() * A(Fraction(1, 3)).cos()).tan(),
      lambda: mpmath.tan(mpmath.sinh(mpmath.mpf(1) / 3) * mpmath.cos(mpmath.mpf(1) / 3)),
      "x = 1/3", functions="tan, sinh, cos"),

    C("MP06", "point", "cosh_sin_add_arctan",
      "Real.cosh (Real.sin 1 + Real.arctan 1)",
      lambda: (A(1).sin() + A(1).atan()).cosh(),
      lambda: mpmath.cosh(mpmath.sin(1) + mpmath.atan(1)),
      "x = 1", functions="cosh, sin, arctan"),

    C("MP07", "point", "zeta_cos_add_three",
      "(riemannZeta (Real.cos (1 / 3) + 3)).re",
      lambda: (A(Fraction(1, 3)).cos() + 3).zeta(),
      lambda: mpmath.zeta(mpmath.cos(mpmath.mpf(1) / 3) + 3),
      "s = cos(1/3) + 3", functions="riemannZeta, cos",
      note="zeta at an irrational argument off the real axis's critical strip"),

    C("MP08", "point", "arcsin_tanh_mul_cos",
      "Real.arcsin (Real.tanh (1 / 2) * Real.cos (1 / 3))",
      lambda: (A(H).tanh() * A(Fraction(1, 3)).cos()).asin(),
      lambda: mpmath.asin(mpmath.tanh(mpmath.mpf(1) / 2) * mpmath.cos(mpmath.mpf(1) / 3)),
      "x = 1/2, 1/3", functions="arcsin, tanh, cos",
      note="arcsin of a product of an unrelated hyperbolic and trig value "
           "(deliberately not arcsin (sin _))"),

    C("MP09", "point", "arccos_sinh_mul_exp",
      "Real.arccos (Real.sinh (1 / 2) * Real.exp (-(1 / 2)))",
      lambda: (A(H).sinh() * (-A(H)).exp()).acos(),
      lambda: mpmath.acos(mpmath.sinh(mpmath.mpf(1) / 2) * mpmath.exp(mpmath.mpf(-1) / 2)),
      "x = 1/2", functions="arccos, sinh, exp"),

    C("MP10", "point", "sinc_exp_mul_sin",
      "Real.sinc (Real.exp (-1) * Real.sin 1)",
      lambda: ((-A(1)).exp() * A(1).sin()).sinc(),
      lambda: mpmath.sin(mpmath.exp(-1) * mpmath.sin(1)) / (mpmath.exp(-1) * mpmath.sin(1)),
      "x = 1", functions="sinc, exp, sin"),

    C("MP11", "point", "cot_sinh_add_two",
      "Real.cot (Real.sinh (1 / 2) + 2)",
      lambda: (A(H).sinh() + 2).cot(),
      lambda: 1 / mpmath.tan(mpmath.sinh(mpmath.mpf(1) / 2) + 2),
      "x = 1/2", functions="cot, sinh"),

    C("MP12", "point", "arsinh_cos_mul_exp",
      "Real.arsinh (Real.cos (1 / 2) * Real.exp (1 / 2))",
      lambda: (A(H).cos() * A(H).exp()).asinh(),
      lambda: mpmath.asinh(mpmath.cos(mpmath.mpf(1) / 2) * mpmath.exp(mpmath.mpf(1) / 2)),
      "x = 1/2", functions="arsinh, cos, exp",
      note="arsinh fed by cos and exp -- no sinh anywhere, so no inverse pair"),

    C("MP13", "point", "arcosh_exp_add_sin",
      "Real.arcosh (Real.exp (1 / 2) + Real.sin (1 / 2))",
      lambda: (A(H).exp() + A(H).sin()).acosh(),
      lambda: mpmath.acosh(mpmath.exp(mpmath.mpf(1) / 2) + mpmath.sin(mpmath.mpf(1) / 2)),
      "x = 1/2", functions="arcosh, exp, sin"),

    C("MP14", "point", "artanh_sin_mul_exp",
      "Real.artanh (Real.sin (1 / 4) * Real.exp (-1))",
      lambda: (A(Fraction(1, 4)).sin() * (-A(1)).exp()).atanh(),
      lambda: mpmath.atanh(mpmath.sin(mpmath.mpf(1) / 4) * mpmath.exp(-1)),
      "x = 1/4", functions="artanh, sin, exp"),

    C("MP15", "point", "logb_exp_sin",
      "Real.logb 2 (Real.exp (Real.sin 1) + 1)",
      lambda: ((A(1).sin()).exp() + 1).log_base(2),
      lambda: mpmath.log(mpmath.exp(mpmath.sin(1)) + 1) / mpmath.log(2),
      "base 2, x = 1", functions="logb, exp, sin"),

    C("MP16", "point", "exp_chebyshev_t_add_sin",
      "Real.exp ((((Polynomial.Chebyshev.T ℚ 4).eval (1 / 3) : ℚ) : ℝ) + Real.sin (1 / 2))",
      lambda: (A(Fraction(1, 3)).chebyshev_t(4) + A(H).sin()).exp(),
      lambda: mpmath.exp(mpmath.chebyt(4, mpmath.mpf(1) / 3) + mpmath.sin(mpmath.mpf(1) / 2)),
      "n = 4, x = 1/3", functions="Chebyshev T, exp, sin",
      note="an exact rational polynomial value fed into exp together with sin"),

    C("MP17", "point", "log_chebyshev_u_add_three",
      "Real.log (3 + (((Polynomial.Chebyshev.U ℚ 4).eval (1 / 3) : ℚ) : ℝ))",
      lambda: (3 + A(Fraction(1, 3)).chebyshev_u(4)).log(),
      lambda: mpmath.log(3 + mpmath.chebyu(4, mpmath.mpf(1) / 3)),
      "n = 4, x = 1/3", functions="Chebyshev U, log"),

    C("MP18", "point", "cos_euler_add_sqrt",
      "Real.cos (Real.eulerMascheroniConstant + Real.sqrt 2)",
      lambda: (A(0).const_euler() + A(2).sqrt()).cos(),
      lambda: mpmath.cos(mpmath.euler + mpmath.sqrt(2)),
      "x = gamma + sqrt 2", functions="cos, eulerMascheroniConstant, sqrt"),

    C("MP19", "point", "sinh_bell_over_hundred",
      "Real.sinh (((Nat.bell 5 : ℕ) : ℝ) / 100)",
      lambda: (A(0).bell_number(5) / 100).sinh(),
      lambda: mpmath.sinh(mpmath.bell(5) / 100),
      "n = 5", functions="sinh, Nat.bell",
      note="integer-valued Bell number (52) inside a hyperbolic function"),

    C("MP20", "point", "exp_bernoulli_poly",
      "Real.exp ((((Polynomial.bernoulli 2).eval (1 / 3) : ℚ) : ℝ)) * 2",
      lambda: ((A(Fraction(1, 3)).bernoulli_poly(2)).exp()) * 2,
      lambda: 2 * mpmath.exp(mpmath.mpf(1) / 9 - mpmath.mpf(1) / 3 + mpmath.mpf(1) / 6),
      "n = 2, x = 1/3", functions="Polynomial.bernoulli, exp"),

    C("MP21", "point", "cos_bernoulli_four_add_sqrt",
      "Real.cos ((bernoulli 4 : ℝ) + Real.sqrt 2)",
      lambda: (A(0).bernoulli(4) + A(2).sqrt()).cos(),
      lambda: mpmath.cos(mpmath.mpf(-1) / 30 + mpmath.sqrt(2)),
      "n = 4", functions="cos, bernoulli, sqrt"),

    C("MP22", "point", "arctan_log_ten_mul_exp",
      "Real.arctan (Real.log 10 * Real.exp (-1))",
      lambda: (A(0).const_log10() * (-A(1)).exp()).atan(),
      lambda: mpmath.atan(mpmath.log(10) * mpmath.exp(-1)),
      "x = log 10 / e", functions="arctan, log 10, exp"),

    C("MP23", "point", "log_two_gamma_div_exp",
      "Real.log 2 * Real.Gamma (1 / 4) / Real.exp 1",
      lambda: A(2).log() * A(Fraction(1, 4)).gamma() / A(1).exp(),
      lambda: mpmath.log(2) * mpmath.gamma(mpmath.mpf(1) / 4) / mpmath.e,
      "x = 1/4", functions="log 2, Gamma, exp"),

    C("MP24", "point", "sqrt_pi_mul_tanh",
      "Real.sqrt Real.pi * Real.tanh (1 / 2)",
      lambda: Pi().sqrt() * A(H).tanh(),
      lambda: mpmath.sqrt(mpmath.pi) * mpmath.tanh(mpmath.mpf(1) / 2),
      "x = 1/2", functions="sqrt, pi, tanh"),

    C("MP25", "point", "choose_div_factorial_mul_sqrt",
      "((Nat.choose 7 3 : ℕ) : ℝ) / ((Nat.factorial 4 : ℕ) : ℝ) * Real.sqrt 2",
      lambda: A(35) / A(24) * A(2).sqrt(),
      lambda: mpmath.mpf(35) / 24 * mpmath.sqrt(2),
      "n = 7, k = 3", functions="Nat.choose, Nat.factorial, sqrt"),

    C("MP26", "point", "sqrt_agm",
      "Real.sqrt (((NNReal.agm 1 2 : ℝ≥0) : ℝ))",
      lambda: (A(1).agm(A(2))).sqrt(),
      lambda: mpmath.sqrt(mpmath.agm(1, 2)),
      "x = 1, y = 2", functions="sqrt, agm"),

    C("MP27", "point", "sqrt_digamma_add_exp",
      "Real.sqrt ((Complex.digamma 3).re + Real.exp (-1))",
      lambda: (A(3).digamma() + (-A(1)).exp()).sqrt(),
      lambda: mpmath.sqrt(mpmath.digamma(3) + mpmath.exp(-1)),
      "x = 3", functions="sqrt, digamma, exp"),

    C("MP28", "point", "pochhammer_four_third_mul_exp",
      "(((ascPochhammer ℚ 4).eval (1 / 3) : ℚ) : ℝ) * Real.exp (-1)",
      lambda: A(Fraction(1, 3)).rising(4) * (-A(1)).exp(),
      lambda: mpmath.rf(mpmath.mpf(1) / 3, 4) * mpmath.exp(-1),
      "n = 4, x = 1/3", functions="ascPochhammer, exp",
      note="(1/3)_4 = 280/81 fed into a product with exp (-1)"),

    C("MP29", "point", "rpow_sin_exponent",
      "(2 : ℝ) ^ (Real.sin (1 / 2) + 1 / 4)",
      lambda: A(2) ** (A(H).sin() + A(Fraction(1, 4))),
      lambda: mpmath.mpf(2) ** (mpmath.sin(mpmath.mpf(1) / 2) + mpmath.mpf(1) / 4),
      "base 2, exponent sin(1/2) + 1/4", functions="rpow, sin"),

    C("MP30", "point", "log_mul_hypergeometric",
      "Real.log 2 * ordinaryHypergeometric ℝ 1 1 2 (1 / 2)",
      lambda: A(2).log() * A(H).hypgeom_2f1(A(1), A(1), A(2)),
      lambda: mpmath.log(2) * mpmath.hyp2f1(1, 1, 2, mpmath.mpf(1) / 2),
      "a = b = 1, c = 2, x = 1/2", functions="log, ordinaryHypergeometric",
      note="the Gaussian 2F1 is now a mathlib declaration "
           "(`ordinaryHypergeometric`, notation `₂F₁`); "
           "2F1(1, 1; 2; 1/2) = 2 log 2, so the composition multiplies "
           "the series value by another log"),
]

# --------------------------------------------------------------------------
# MP31..MP35 -- the hypergeometric layer, mirrored 1:1 on mathlib
#
#   ordinaryHypergeometric ℝ a b c z          (mathlib, unregularized 2F1)
#   Complex.regularizedGaussHGFun a b c z     (mathlib, regularized 2F1)
#   Complex.regularizedHGFun {a...} {b...} z  (mathlib, general pFq)
#
# The Arb side uses the matching *specialized* kernel (hypgeom_2f1) for the
# Gaussian cases and the *general* hypgeom kernel for the pFq cases -- exactly
# the split D06/D14 of the zoo tests.  `regularized=True` is the normalization
# mathlib's definitions carry (divide by prod Gamma(b)).
# --------------------------------------------------------------------------
HYPERGEOMETRIC = [
    C("MP31", "point", "regularized_gauss_hypergeometric_neg5",
      "(Complex.regularizedGaussHGFun 1 2 3 (-5)).re",
      lambda: A(-5).hypgeom_2f1(A(1), A(2), A(3), regularized=True),
      lambda: mpmath.hyp2f1(1, 2, 3, -5) / mpmath.gamma(3),
      "a = 1, b = 2, c = 3, z = -5", functions="regularizedGaussHGFun",
      note="the regularized Gaussian hypergeometric function "
           "(`Complex.regularizedGaussHGFun`, i.e. 2F1/Gamma(c)) evaluated "
           "outside the unit disc: the same value as the Arb specialized "
           "kernel D06 check"),

    C("MP32", "point", "regularized_pfq_3f2",
      "(Complex.regularizedHGFun {1, 1, 1} {2, 2} (1 / 2)).re",
      lambda: A(H).hypgeom([A(1), A(1), A(1)], [A(2), A(2)], regularized=True),
      lambda: mpmath.hyper([1, 1, 1], [2, 2], mpmath.mpf(1) / 2)
              / (mpmath.gamma(2) * mpmath.gamma(2)),
      "3F2: a = (1, 1, 1), b = (2, 2), z = 1/2", functions="regularizedHGFun",
      note="3F2 -- five parameters, no specialized Arb kernel (the general "
           "hypgeom path is used), normalized by Gamma(2)Gamma(2) = 1"),

    C("MP33", "point", "regularized_pfq_2f3",
      "(Complex.regularizedHGFun {1, 2} {3, 4, 5} (1 / 4)).re",
      lambda: A(Fraction(1, 4)).hypgeom([A(1), A(2)], [A(3), A(4), A(5)],
                                        regularized=True),
      lambda: mpmath.hyper([1, 2], [3, 4, 5], mpmath.mpf(1) / 4)
              / (mpmath.gamma(3) * mpmath.gamma(4) * mpmath.gamma(5)),
      "2F3: a = (1, 2), b = (3, 4, 5), z = 1/4", functions="regularizedHGFun",
      note="2F3 -- the normalization divisor Gamma(3)Gamma(4)Gamma(5) = 288 is "
           "not 1, so this is the case that actually distinguishes the "
           "regularized definition"),

    C("MP34", "point", "regularized_pfq_4f3",
      "(Complex.regularizedHGFun {1, 1, 1, 1} {2, 2, 2} (1 / 4)).re",
      lambda: A(Fraction(1, 4)).hypgeom([A(1)] * 4, [A(2)] * 3, regularized=True),
      lambda: mpmath.hyper([1, 1, 1, 1], [2, 2, 2], mpmath.mpf(1) / 4),
      "4F3: a = (1, 1, 1, 1), b = (2, 2, 2), z = 1/4", functions="regularizedHGFun",
      note="4F3 -- seven parameters, three more than any specialized form"),

    C("MP35", "point", "regularized_pfq_terminating_3f2",
      "(Complex.regularizedHGFun {(-3 : ℂ), 1, 1} {2, 2} (1 / 2)).re",
      lambda: A(H).hypgeom([A(-3), A(1), A(1)], [A(2), A(2)], regularized=True),
      lambda: Fraction(269, 384),
      "3F2: a = (-3, 1, 1), b = (2, 2), z = 1/2", functions="regularizedHGFun",
      note="a negative-integer numerator parameter terminates the series: the "
           "value is the exact rational 269/384 (Arb ball of radius 0), the "
           "only composition here with an exact answer"),
]
POINT.extend(HYPERGEOMETRIC)

# --------------------------------------------------------------------------
# MD1..MD6 -- Nat / discrete compositions
# --------------------------------------------------------------------------
DISCRETE = [
    C("MD01", "nat", "floor_exp_two_add_sin_div_cos",
      "(Real.exp 2 + Real.sin 1) / Real.cos 1",
      lambda: (A(2).exp() + A(1).sin()) / A(1).cos(),
      lambda: (mpmath.exp(2) + mpmath.sin(1)) / mpmath.cos(1),
      "x = 2, 1", functions="exp, sin, cos, floor", wrap="⌊⌋₊",
      note="the shape from the review: a Nat witness equal to the floor of a "
           "composition of three functions divided by a fourth"),

    C("MD02", "nat", "floor_gamma_quarter_add_gamma_third",
      "Real.Gamma (1 / 4) + Real.Gamma (1 / 3)",
      lambda: A(Fraction(1, 4)).gamma() + A(Fraction(1, 3)).gamma(),
      lambda: mpmath.gamma(mpmath.mpf(1) / 4) + mpmath.gamma(mpmath.mpf(1) / 3),
      "x = 1/4, 1/3", functions="Gamma, floor", wrap="⌊⌋₊"),

    C("MD03", "nat", "floor_hundred_tanh_sqrt_two",
      "100 * Real.tanh (Real.sqrt 2)",
      lambda: 100 * (A(2).sqrt()).tanh(),
      lambda: 100 * mpmath.tanh(mpmath.sqrt(2)),
      "x = sqrt 2", functions="tanh, sqrt, floor", wrap="⌊⌋₊"),

    C("MD04", "nat", "floor_ten_sqrt_sum",
      "10 * (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5)",
      lambda: 10 * (A(2).sqrt() + A(3).sqrt() + A(5).sqrt()),
      lambda: 10 * (mpmath.sqrt(2) + mpmath.sqrt(3) + mpmath.sqrt(5)),
      "x = 2, 3, 5", functions="sqrt, floor", wrap="⌊⌋₊",
      note="sum of three radicals -- the classic test for a summation-based "
           "interval engine"),

    C("MD05", "nat", "gcd_of_fib",
      "Nat.gcd (Nat.fib 10) (Nat.fib 15)",
      lambda: A(0).fib(15) - 11 * A(0).fib(10),
      lambda: Fraction(5),
      "n = 10, 15", functions="Nat.gcd, Nat.fib",
      note="gcd(55, 610) = 5 -- the two Fibonacci numbers share the factor 5"),

    C("MD06", "sign", "sign_exp_sub_cos",
      "Real.sign (Real.exp (-1) - Real.cos (1 / 2))",
      lambda: ((-A(1)).exp() - A(H).cos()).sgn(),
      lambda: Fraction(-1),
      "x = 1, 1/2", functions="sign, exp, cos",
      note="a comparison between two transcendental values rather than a "
           "numerical value"),

    C("MD07", "ceil", "ceil_ten_exp_cos",
      "10 * Real.exp (Real.cos 1)",
      lambda: 10 * A(1).cos().exp(),
      lambda: 10 * mpmath.exp(mpmath.cos(1)),
      "x = 1", functions="ceil, exp, cos", wrap="⌈⌉₊",
      note="the ceiling counterpart of the floor tests: 10 * exp (cos 1) ~ "
           "17.165 sits between the consecutive integers 17 and 18"),
]

# --------------------------------------------------------------------------
# MR1..MR3 -- range compositions
# --------------------------------------------------------------------------
RANGE = [
    C("MR01", "range", "range_exp_sin_add_cos",
      "Real.exp (Real.sin r + Real.cos r)",
      lambda X: (X.sin() + X.cos()).exp(),
      lambda t: mpmath.exp(mpmath.sin(t) + mpmath.cos(t)),
      "r in [0, 1]", box=(0, 1), tol=Fraction(1, 10 ** 3),
      functions="exp, sin, cos",
      note="maximum at the interior point r = pi/4, minimum at the left endpoint"),

    C("MR02", "range", "range_arctan_sin_add_cos",
      "Real.arctan (Real.sin r + Real.cos r)",
      lambda X: (X.sin() + X.cos()).atan(),
      lambda t: mpmath.atan(mpmath.sin(t) + mpmath.cos(t)),
      "r in [0, 2]", box=(0, 2), tol=Fraction(1, 10 ** 3),
      functions="arctan, sin, cos",
      note="arctan is monotone, so the extrema come from sin + cos"),

    C("MR03", "range", "range_exp_cos_mul_sin",
      "Real.exp (Real.cos r) * Real.sin r",
      lambda X: X.cos().exp() * X.sin(),
      lambda t: mpmath.exp(mpmath.cos(t)) * mpmath.sin(t),
      "r in [0, 2]", box=(0, 2), tol=Fraction(1, 10 ** 3),
      functions="exp, cos, sin",
      note="interior maximum at r = pi/4, minimum 0 at the left endpoint"),
]

ALL_COMPS = POINT + DISCRETE + RANGE
BY_ID = {c["id"]: c for c in ALL_COMPS}

# Arb-side extras: compositions with functions mathlib has no declaration for.
# They are still one test each (never counted as Lean tests).
ARB_ONLY = [
    C("ME01", "point", "arb_erf_exp_add_sin",
      "arb.erf (ar.exp (-1) + ar.sin 1)  -- no mathlib counterpart",
      lambda: ((-A(1)).exp() + A(1).sin()).erf(),
      lambda: mpmath.erf(mpmath.exp(-1) + mpmath.sin(1)),
      "x = 1", functions="erf, exp, sin",
      note="Arb-only: mathlib has no erf"),

    C("ME02", "point", "arb_bessel_j_cosh_add_sqrt",
      "arb.bessel_j 1 (ar.cosh (1/2) + ar.sqrt 3)  -- no mathlib counterpart",
      lambda: (A(H).cosh() + A(3).sqrt()).bessel_j(1),
      lambda: mpmath.besselj(1, mpmath.cosh(mpmath.mpf(1) / 2) + mpmath.sqrt(3)),
      "x = 1/2, 3", functions="bessel_j, cosh, sqrt",
      note="Arb-only: mathlib has no Bessel functions"),

    C("ME03", "point", "arb_lambertw_exp_add_cos",
      "arb.lambertw (ar.exp 1 + ar.cos 1)  -- no mathlib counterpart",
      lambda: (A(1).exp() + A(1).cos()).lambertw(),
      lambda: mpmath.lambertw(mpmath.exp(1) + mpmath.cos(1)),
      "x = 1", functions="lambertw, exp, cos",
      note="Arb-only: mathlib has no Lambert W"),

    C("ME04", "point", "arb_polylog_cos_half",
      "arb.polylog 3 (ar.cos (1/2) / 2)  -- no mathlib counterpart",
      lambda: (A(H).cos() / 2).polylog(3),
      lambda: mpmath.polylog(3, mpmath.cos(mpmath.mpf(1) / 2) / 2),
      "x = 1/2", functions="polylog, cos",
      note="Arb-only: mathlib has polylog only as a Dirichlet series"),
]

# guard against the mistake that triggered this revision: an inverse composed with
# its own function (`arcsin (sin x)`, `log (exp x)`, ...) is dischargeable by
# rewriting alone and would not exercise interval arithmetic at all.
FORBIDDEN_PAIRS = [
    ("Real.arcsin", "Real.sin"), ("Real.arccos", "Real.cos"), ("Real.arctan", "Real.tan"),
    ("Real.arsinh", "Real.sinh"), ("Real.arcosh", "Real.cosh"), ("Real.artanh", "Real.tanh"),
    ("Real.log", "Real.exp"), ("Real.sqrt", "^ 2"), ("Real.logb", "Real.exp"),
    ("Real.cot", "Real.tan"), ("Real.tan", "Real.arctan"), ("Real.exp", "Real.log"),
]


def _arg_text(text, name):
    """Return the argument text of the *first* `name ( ... )` application, or None."""
    i = text.find(name + " (")
    if i < 0:
        i = text.find(name + "(")
    if i < 0:
        return None
    j = text.index("(", i)
    depth, k = 0, j
    while k < len(text):
        if text[k] == "(":
            depth += 1
        elif text[k] == ")":
            depth -= 1
            if depth == 0:
                return text[j + 1:k]
        k += 1
    return None


def audit_no_inverse_pairs():
    """Flag only *direct* nesting: `outer (inner ...)` where the argument of the
    inverse is exactly its own function applied to something (the case a rewriter
    can discharge without any interval arithmetic).  Sums, products and scalings of
    unrelated functions are fine, so `log 2 * Gamma (1/4) / exp 1` or
    `logb 2 (exp (sin 1) + 1)` do not count."""
    bad = []
    for c in ALL_COMPS:
        text = c["lean"]
        for outer, inner in FORBIDDEN_PAIRS:
            arg = _arg_text(text, outer)
            if arg is None:
                continue
            head = arg.strip().lstrip("(").strip()
            if inner == "^ 2":
                continue                      # square detection is structural; not used
            if head.startswith(inner + " ") or head.startswith(inner + "("):
                # the argument must be *exactly* inner (...) with nothing appended
                sub = _arg_text(head + ")", inner)
                if sub is not None and f"{inner} ({sub})".replace(" ", "") in head.replace(" ", ""):
                    bad.append(f"{c['id']}: {outer} applied directly to {inner}")
    return bad


# --------------------------------------------------------------------------
# evaluation helpers (shared by tests_arb.py, validate_lean_tests.py)
# --------------------------------------------------------------------------

def eval_point(c):
    """(ok, lo, hi, err, ref) for a point composition: Arb enclosure vs mpmath."""
    x = c["py"]()
    ref = Fraction(str(c["ref"]()))
    tol = Fraction(1, 10 ** 13) * max(Fraction(1), abs(ref))
    ok = lb(x) - tol <= ref <= ub(x) + tol
    err = max(abs(ref - lb(x)), abs(ref - ub(x)))
    return ok, lb(x), ub(x), err, ref


def eval_nat(c):
    """(ok, n, lo, hi, margin).  For floor goals the Arb enclosure of the inner
    composition must sit strictly inside (n, n+1): that is what proves
    `n = ⌊f x⌋`; for a ceiling the enclosure must sit inside `(n-1, n)`; and the
    margin is the certificate's slack.  `MD05`/`MD06` are exact/discrete
    instead (an integer identity with no interval search, and a sign
    decision)."""
    x = c["py"]()
    lo, hi = lb(x), ub(x)
    if c["id"] == "MD05":                    # Bezout expression, exact integer
        return (lo == hi == 5), 5, lo, hi, Fraction(10 ** 9)
    if c["id"] == "MD06":                    # sign: certify the sign, not a floor
        return (hi < 0), -1, lo, hi, -hi
    ref = mpmath.mpf(str(c["ref"]()))
    if c["kind"] == "ceil":
        n = int(mpmath.ceil(ref))
        return (lo > n - 1) and (hi < n), n, lo, hi, min(lo - (n - 1), n - hi)
    n = int(mpmath.floor(ref))
    return (lo > n) and (hi < n + 1), n, lo, hi, min(lo - n, (n + 1) - hi)


def mpmath_range(f, a, b, n=600):
    """Dense-scan + secant-refine reference for sup/inf of a composed real
    function on [a, b] (float-level; Arb is the rigorous side)."""
    xs = [mpmath.mpf(a) + (mpmath.mpf(b) - mpmath.mpf(a)) * i / n for i in range(n + 1)]
    cands = [(f(x), x) for x in xs]
    for i in range(n):
        d0 = mpmath.diff(f, xs[i])
        d1 = mpmath.diff(f, xs[i + 1])
        if d0 * d1 < 0:
            try:
                cr = mpmath.findroot(lambda t: mpmath.diff(f, t), (xs[i], xs[i + 1]))
                if a <= cr <= b:
                    cands.append((f(cr), cr))
            except Exception:
                pass
    vmax, xmax = max(cands)
    vmin, xmin = min(cands)
    return vmax, vmin


def summary(c):
    if c["kind"] == "point":
        ok, lo, hi, err, ref = eval_point(c)
        return (ok, f"{c['lean'].split('--')[0].strip()} = "
                    f"[{T.show(_lit(lo), 16)}, {T.show(_lit(hi), 16)}] "
                    f"(mpmath {mpmath.nstr(c['ref'](), 20)}; deviation {float(err):.2g})")
    if c["kind"] in ("nat", "sign", "ceil"):
        ok, n, lo, hi, margin = eval_nat(c)
        what = {"nat": "floor certified", "ceil": "ceiling certified",
                "sign": "sign certified"}[c["kind"]]
        return (ok, f"enclosure [{T.show(_lit(lo), 16)}, {T.show(_lit(hi), 16)}] "
                    f"=> {what}: {n}, margin {float(margin):.4f}")
    r = T.range_enclosure(c["py"], c["box"][0], c["box"][1], parts=128, refine=20)
    vmax, vmin = mpmath_range(c["ref"], c["box"][0], c["box"][1])
    ok = (r["sup_lo"] <= Fraction(str(vmax)) <= r["sup_hi"]
          and r["inf_lo"] <= Fraction(str(vmin)) <= r["inf_hi"])
    return (ok, f"sup in [{float(r['sup_lo']):.9g}, {float(r['sup_hi']):.9g}] "
                f"(ref {float(vmax):.9g}, at r ~ {float(r['argmax'][0]):.4f}); "
                f"inf in [{float(r['inf_lo']):.9g}, {float(r['inf_hi']):.9g}] "
                f"(ref {float(vmin):.9g}, at r ~ {float(r['argmin'][0]):.4f})")



# --------------------------------------------------------------------------
# Lean-side function inventory: every mathlib declaration the suite is meant to
# exercise must occur in at least one composition (this is what replaces the old
# "one theorem per function family" shape).
# --------------------------------------------------------------------------
MATHLIB_FUNCTIONS = [
    "Real.exp", "Real.log ", "Real.logb", "Real.log 10", "Real.log 2", "Real.sqrt", "Real.sinc",
    "Real.sin", "Real.cos", "Real.tan", "Real.cot", "Real.arcsin", "Real.arccos", "Real.arctan",
    "Real.sinh", "Real.cosh", "Real.tanh", "Real.arsinh", "Real.arcosh", "Real.artanh",
    "Real.Gamma", "riemannZeta", "Real.pi", "Real.eulerMascheroniConstant", "Complex.digamma",
    "NNReal.agm", "ascPochhammer", "Polynomial.Chebyshev.T", "Polynomial.Chebyshev.U",
    "Polynomial.bernoulli", "bernoulli", "Nat.bell", "Nat.choose", "Nat.factorial", "Nat.fib",
    "Nat.gcd", "Real.sign", "ordinaryHypergeometric",
    "regularizedGaussHGFun", "regularizedHGFun", "⌊", "⌈", "^",
]


def function_coverage():
    """{mathlib name -> [composition ids]} and the list of uncovered names."""
    cov = {}
    for name in MATHLIB_FUNCTIONS:
        ids = [c["id"] for c in ALL_COMPS if name in lean_goal_text(c)]
        if ids:
            cov[name] = ids
    missing = [n for n in MATHLIB_FUNCTIONS if n not in cov]
    return cov, missing


def _lit(fr):
    return A(fr)
