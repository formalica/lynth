#!/usr/bin/env python3
"""
function_zoo.py -- coverage tables for Arb's special-function surface.

One *family* = one composite test case (the request: "cover them with minimal
amount of tests, you can compose few functions in one testcase").  Every check
inside a family is one Arb function evaluated on a point input; the value is
compared against an independent reference (mpmath at 40 digits, an exact
rational, or a known closed form).

Two consumers share this table:

  * `tests_arb.py`  -> one row per family (group D) in `RESULTS.md`;
  * `validate_lean_tests.py` -> the `F*` composite certificates, i.e. the
    Lean mirror of the same numbers (only checks that carry a `lean`
    expression, i.e. functions that exist in mathlib at the pinned rev).

Conventions proven by probing python-flint 0.9.0 (they are *not* symmetric):

    x.hypgeom_0f1(a)          = 0F1(a; x)          (self = z)
    x.hypgeom_1f1(a, b)       = 1F1(a; b; x)
    x.hypgeom_2f1(a, b, c)    = 2F1(a, b; c; x)
    x.hypgeom_u(a, b)         = U(a, b, x)
    x.bessel_j(nu)            = J_nu(x)            (self = argument)
    x.gamma_lower(a)          = gamma(a, x)        (lower incomplete)
    x.gamma_upper(a)          = Gamma(a, x)        (upper incomplete)
    x.beta_lower(a, b)        = B_x(a, b)
    x.coulomb_f(l, eta), x.coulomb_g(l, eta)       (self = rho)
    x.expint(n)               = E_n(x)
    x.chebyshev_t(n) / chebyshev_u(n) / gegenbauer_c(n, a) / hermite_h(n) /
      jacobi_p(n, a, b) / laguerre_l(n, a) / legendre_p(n, m) / legendre_q(n, m)
    x.rising(n)               = (x)_n              (Pochhammer)
    arb(0).partitions_p(n), arb.fac_ui(n), arb.bin_uiui(n, k),
      arb(0).bernoulli(n), arb(0).bell_number(n), arb(0).airy_ai_zero(n),
      arb(0).legendre_p_root(n, k), arb.atan2(y, x)  -- static
"""

from __future__ import annotations

from fractions import Fraction

import mpmath

from flint import arb, acb, fmpq

import tools as T
from tools import A, I, F, lb, ub

mp = mpmath.mp
mp.dps = 40


def M(v):
    """Reference from mpmath (40 digits) -> Fraction."""
    return Fraction(str(v))


def P(p, q=1):
    """Exact rational reference."""
    return Fraction(p, q)


# --------------------------------------------------------------------------
# family definitions
# --------------------------------------------------------------------------

def fam(fid, lean, name, title, at, method, checks):
    return dict(id=fid, lean=lean, name=name, title=title, at=at,
                method=method, checks=checks)


def chk(fn, call, ref, lean=None, note="", mode="contains"):
    """mode: "contains" (ref lies in the enclosure), "ge" (the whole enclosure is
    >= ref, i.e. the function value is certified >= ref) or "le"."""
    return dict(fn=fn, call=call, ref=ref, lean=lean, note=note, mode=mode)



def two_prec(f):
    """Two-precision agreement (the FLINT test idiom): the difference of the
    enclosures computed at 256 and 384 bits must contain 0 -- used for the few
    functions that have no independent reference here."""
    def g():
        from flint import ctx
        old = ctx.prec
        ctx.prec = 384
        try:
            hi = f()
        finally:
            ctx.prec = old
        return hi - f()
    return g


FAMILIES = [
    # ------------------------------------------------------------------ D01
    fam("D01", "F01", "elementary_zoo",
        "elementary transcendental zoo: exp/expm1/log/log1p/log_base/sqrt/rsqrt/root/pow/sinc/sinc_pi",
        "x = 1/2, 2, 8 (points)",
        "11 Arb entry points, each checked against an mpmath reference",
        [
            chk("exp(1/2)", lambda: A(Fraction(1, 2)).exp(), M(mpmath.exp(0.5)),
                lean="Real.exp (1 / 2)"),
            chk("expm1(1/2)", lambda: A(Fraction(1, 2)).expm1(), M(mpmath.expm1(0.5))),
            chk("log(2)", lambda: A(2).log(), M(mpmath.log(2)), lean="Real.log 2"),
            chk("log1p(1/2)", lambda: A(Fraction(1, 2)).log1p(), M(mpmath.log1p(0.5))),
            chk("log_base 8 (base 2)", lambda: A(8).log_base(2), P(3),
                lean="Real.logb 2 8"),
            chk("sqrt(3)", lambda: A(3).sqrt(), M(mpmath.sqrt(3)), lean="Real.sqrt 3"),
            chk("rsqrt(2)", lambda: A(2).rsqrt(), M(1 / mpmath.sqrt(2))),
            chk("2^(1/3) via root", lambda: A(2).root(3), M(mpmath.mpf(2) ** (mpmath.mpf(1) / 3)),
                lean="(2 : ℝ) ^ ((1 : ℝ) / 3)"),
            chk("2^(1/3) via exp(log/3)", lambda: (A(2).log() / 3).exp(),
                M(mpmath.mpf(2) ** (mpmath.mpf(1) / 3))),
            chk("sinc(1/2) = sin x / x", lambda: A(Fraction(1, 2)).sinc(),
                M(mpmath.sin(0.5) / 0.5), lean="Real.sinc (1 / 2)"),
            chk("sinc_pi(1/2) = sin(pi x)/(pi x)", lambda: A(Fraction(1, 2)).sinc_pi(),
                M(2 / mpmath.pi)),
        ]),

    # ------------------------------------------------------------------ D02
    fam("D02", "F02", "trig_zoo",
        "trigonometric zoo: sin/cos/tan/cot/sec/csc/asin/acos/atan/atan2, "
        "sin_cos, sin_pi/cos_pi/tan_pi/cot_pi, exact pi-fractions",
        "x = 1/2, 1, 1/6, 1/3, 1/4 (points and exact rational multiples of pi)",
        "20 Arb entry points; the pi-rational ones use algebraic pi reduction",
        [
            chk("sin(1/2)", lambda: A(Fraction(1, 2)).sin(), M(mpmath.sin(0.5)),
                lean="Real.sin (1 / 2)"),
            chk("cos(1/2)", lambda: A(Fraction(1, 2)).cos(), M(mpmath.cos(0.5)),
                lean="Real.cos (1 / 2)"),
            chk("tan(1/2)", lambda: A(Fraction(1, 2)).tan(), M(mpmath.tan(0.5)),
                lean="Real.tan (1 / 2)"),
            chk("cot(1/2)", lambda: A(Fraction(1, 2)).cot(), M(mpmath.cot(0.5)),
                lean="Real.cot (1 / 2)"),
            chk("sec(1/2)", lambda: A(Fraction(1, 2)).sec(), M(1 / mpmath.cos(0.5))),
            chk("csc(1/2)", lambda: A(Fraction(1, 2)).csc(), M(1 / mpmath.sin(0.5))),
            chk("asin(1/2)", lambda: A(Fraction(1, 2)).asin(), M(mpmath.asin(0.5)),
                lean="Real.arcsin (1 / 2)"),
            chk("acos(1/2)", lambda: A(Fraction(1, 2)).acos(), M(mpmath.acos(0.5)),
                lean="Real.arccos (1 / 2)"),
            chk("atan(1)", lambda: A(1).atan(), M(mpmath.atan(1)),
                lean="Real.arctan 1"),
            chk("atan2(1, 2)", lambda: arb.atan2(A(1), A(2)), M(mpmath.atan2(1, 2))),
            chk("sin_cos(1/2).sin", lambda: A(Fraction(1, 2)).sin_cos()[0], M(mpmath.sin(0.5))),
            chk("sin_cos(1/2).cos", lambda: A(Fraction(1, 2)).sin_cos()[1], M(mpmath.cos(0.5))),
            chk("sin_pi(1/6)", lambda: A(Fraction(1, 6)).sin_pi(), M(mpmath.sin(mpmath.pi / 6)),
                lean="Real.sin (Real.pi / 6)"),
            chk("cos_pi(1/3)", lambda: A(Fraction(1, 3)).cos_pi(), M(mpmath.cos(mpmath.pi / 3)),
                lean="Real.cos (Real.pi / 3)"),
            chk("sin_cos_pi(1/6).sin", lambda: A(Fraction(1, 6)).sin_cos_pi()[0],
                M(mpmath.sin(mpmath.pi / 6))),
            chk("sin_cos_pi(1/6).cos", lambda: A(Fraction(1, 6)).sin_cos_pi()[1],
                M(mpmath.cos(mpmath.pi / 6))),
            chk("tan_pi(1/4)", lambda: A(Fraction(1, 4)).tan_pi(), P(1),
                lean="Real.tan (Real.pi / 4)"),
            chk("cot_pi(1/6)", lambda: A(Fraction(1, 6)).cot_pi(), M(1 / mpmath.tan(mpmath.pi / 6))),
            chk("sin_pi_fmpq(1/6)", lambda: A(0).sin_pi_fmpq(fmpq(1, 6)), P(1, 2)),
            chk("cos_pi_fmpq(1/3)", lambda: A(0).cos_pi_fmpq(fmpq(1, 3)), P(1, 2)),
            chk("sin_cos_pi_fmpq(1/6).sin", lambda: A(0).sin_cos_pi_fmpq(fmpq(1, 6))[0], P(1, 2)),
            chk("sin_cos_pi_fmpq(1/6).cos", lambda: A(0).sin_cos_pi_fmpq(fmpq(1, 6))[1],
                M(mpmath.sqrt(3) / 2)),
        ]),

    # ------------------------------------------------------------------ D03
    fam("D03", "F03", "hyperbolic_zoo",
        "hyperbolic zoo: sinh/cosh/tanh/coth/sech/csch and inverses asinh/acosh/atanh",
        "x = 1/2, 2 (points)",
        "10 Arb entry points against mpmath",
        [
            chk("sinh(1/2)", lambda: A(Fraction(1, 2)).sinh(), M(mpmath.sinh(0.5)),
                lean="Real.sinh (1 / 2)"),
            chk("cosh(1/2)", lambda: A(Fraction(1, 2)).cosh(), M(mpmath.cosh(0.5)),
                lean="Real.cosh (1 / 2)"),
            chk("tanh(1/2)", lambda: A(Fraction(1, 2)).tanh(), M(mpmath.tanh(0.5)),
                lean="Real.tanh (1 / 2)"),
            chk("coth(1/2)", lambda: A(Fraction(1, 2)).coth(), M(1 / mpmath.tanh(0.5))),
            chk("sech(1/2)", lambda: A(Fraction(1, 2)).sech(), M(1 / mpmath.cosh(0.5))),
            chk("csch(1/2)", lambda: A(Fraction(1, 2)).csch(), M(1 / mpmath.sinh(0.5))),
            chk("asinh(1/2)", lambda: A(Fraction(1, 2)).asinh(), M(mpmath.asinh(0.5)),
                lean="Real.arsinh (1 / 2)"),
            chk("acosh(2)", lambda: A(2).acosh(), M(mpmath.acosh(2)),
                lean="Real.arcosh 2"),
            chk("atanh(1/2)", lambda: A(Fraction(1, 2)).atanh(), M(mpmath.atanh(0.5)),
                lean="Real.artanh (1 / 2)"),
            chk("sinh_cosh(1/2).sinh", lambda: A(Fraction(1, 2)).sinh_cosh()[0], M(mpmath.sinh(0.5))),
            chk("sinh_cosh(1/2).cosh", lambda: A(Fraction(1, 2)).sinh_cosh()[1], M(mpmath.cosh(0.5))),
        ]),

    # ------------------------------------------------------------------ D04
    fam("D04", "F04a", "gamma_zoo",
        "gamma family: gamma, rgamma, lgamma, digamma, incomplete gamma/beta, "
        "gamma_fmpq, fac, rising",
        "x = 1/4, 7/2, 3, 2; z = 1/2 (points)",
        "12 Arb entry points; incomplete gamma/beta use the self=z convention",
        [
            chk("gamma(1/4)", lambda: A(Fraction(1, 4)).gamma(), M(mpmath.gamma(0.25)),
                lean="Real.Gamma (1 / 4)"),
            chk("gamma(7/2)", lambda: A(Fraction(7, 2)).gamma(), M(mpmath.gamma(3.5))),
            chk("rgamma(3) = 1/Gamma(3)", lambda: A(3).rgamma(), P(1, 2)),
            chk("lgamma(3) = log Gamma(3)", lambda: A(3).lgamma(), M(mpmath.log(2))),
            chk("digamma(3)", lambda: A(3).digamma(), M(mpmath.digamma(3)),
                ),
            chk("gamma_lower: gamma(1, z=2)", lambda: A(2).gamma_lower(A(1)),
                M(mpmath.gammainc(1, 0, 2))),
            chk("gamma_upper: Gamma(1, z=2)", lambda: A(2).gamma_upper(A(1)),
                M(mpmath.gammainc(1, 2, mpmath.inf))),
            chk("beta_lower: B_{1/2}(2,3)", lambda: A(Fraction(1, 2)).beta_lower(A(2), A(3)),
                M(mpmath.betainc(2, 3, 0, 0.5))),
            chk("gamma_fmpq(1/4)", lambda: A(0).gamma_fmpq(fmpq(1, 4)), M(mpmath.gamma(0.25))),
            chk("fac(10) = 10!", lambda: A(10).fac(), P(3628800),
                lean="(Nat.factorial 10 : ℝ)"),
            chk("fac_ui(12)", lambda: A(0).fac_ui(12), P(479001600)),
            chk("rising(1/2, 3) = (1/2)(3/2)(5/2)", lambda: A(Fraction(1, 2)).rising(3), P(15, 8),
                lean="(((ascPochhammer ℚ 3).eval (1 / 2) : ℚ) : ℝ)"),
            chk("rising2(1/2, 3) = (15/8, 5/2*3/2)", lambda: A(Fraction(1, 2)).rising2(3)[0], P(15, 8),
                note="rising2 returns (x)_n and (x+1)_{n-1}"),
            chk("rising_fmpq_ui(1/2, 3)", lambda: arb.rising_fmpq_ui(fmpq(1, 2), 3), P(15, 8)),
        ]),

    # ------------------------------------------------------------------ D05
    fam("D05", "F04b", "zeta_zoo",
        "zeta family: zeta at 2, 3, -1, 1/2; polylog; Backlund S; Gram points; zero counting",
        "s = 2, 3, -1, 1/2; t = 14, 15, 22, 50 (points)",
        "11 Arb entry points (mpmath + exact rationals -1/12, -3/4*zeta(3))",
        [
            chk("zeta(2)", lambda: A(2).zeta(), M(mpmath.pi ** 2 / 6)),
            chk("zeta(3)", lambda: A(3).zeta(), M(mpmath.zeta(3)), lean="(riemannZeta 3).re"),
            chk("zeta(-1) = -1/12", lambda: A(-1).zeta(), P(-1, 12)),
            chk("zeta(1/2)", lambda: A(Fraction(1, 2)).zeta(), M(mpmath.zeta(0.5))),
            chk("polylog(2, 1/2)", lambda: A(Fraction(1, 2)).polylog(2), M(mpmath.polylog(2, 0.5))),
            chk("polylog(3, -1) = -(3/4) zeta(3)", lambda: A(-1).polylog(3),
                M(-mpmath.mpf(3) / 4 * mpmath.zeta(3))),
            chk("backlund_s(14)", lambda: A(14).backlund_s(), M(mpmath.backlunds(14))),
            chk("gram_point(1)", lambda: A(0).gram_point(1), M(mpmath.grampoint(1))),
            chk("zeta_nzeros(14)", lambda: A(14).zeta_nzeros(), P(0)),
            chk("zeta_nzeros(15)", lambda: A(15).zeta_nzeros(), P(1)),
            chk("zeta_nzeros(22)", lambda: A(22).zeta_nzeros(), P(2)),
            chk("zeta_nzeros(50)", lambda: A(50).zeta_nzeros(), P(10)),
        ]),

    # ------------------------------------------------------------------ D06
    fam("D06", "F04c", "hypergeometric_specialized_zoo",
        "specialized hypergeometric implementations: hypgeom_0f1, hypgeom_1f1, "
        "hypgeom_2f1 (incl. the Gauss transformation flags), hypgeom_u",
        "z = 1, 1/2, -5, 9/10 (points); parameters 1, 2, 3, sqrt(2)",
        "12 checks: one per specialized entry point, plus the regularized and "
        "flag-selected evaluation paths and the general entry point cross-checks",
        [
            # ---- hypgeom_0f1 -------------------------------------------------
            chk("0F1(2; 1) = I_1(2)", lambda: A(1).hypgeom_0f1(A(2)),
                M(mpmath.hyp0f1(2, 1)),
                note="hypgeom_0f1: 0F1(a; z), self is z; = Gamma(a) z^((1-a)/2) I_{a-1}(2 sqrt z)"),
            chk("0F1(2; 1) regularized (= /Gamma(2))",
                lambda: A(1).hypgeom_0f1(A(2), regularized=True),
                M(mpmath.hyp0f1(2, 1) / mpmath.gamma(2)),
                note="regularized=True divides by Gamma(a)"),
            # ---- hypgeom_1f1 -------------------------------------------------
            chk("1F1(2; 1; 1) = 2e", lambda: A(1).hypgeom_1f1(A(2), A(1)),
                M(mpmath.hyp1f1(2, 1, 1)),
                note="hypgeom_1f1: confluent 1F1(a; b; z), self is z"),
            chk("1F1(3; 2; 1/2)", lambda: A(Fraction(1, 2)).hypgeom_1f1(A(3), A(2)),
                M(mpmath.hyp1f1(3, 2, 0.5))),
            # ---- hypgeom_2f1 -------------------------------------------------
            chk("2F1(1, 2; 3; -5)", lambda: A(-5).hypgeom_2f1(A(1), A(2), A(3)),
                M(mpmath.hyp2f1(1, 2, 3, -5)),
                lean="ordinaryHypergeometric ℝ (1 : ℚ) (2 : ℚ) (3 : ℚ) ((-5 : ℚ) : ℝ)",
                note="z < 0 outside the unit disc: the analytic continuation is used "
                     "(FLINT docstring value 0.2566592424617555999350018)"),
            chk("2F1(1, 2; 3; -5) regularized (= /Gamma(3))",
                lambda: A(-5).hypgeom_2f1(A(1), A(2), A(3), regularized=True),
                M(mpmath.hyp2f1(1, 2, 3, -5) / mpmath.gamma(3)),
                lean="Complex.regularizedGaussHGFun 1 2 3 (-5)",
                note="the regularized 2F1 is mathlib's `Complex.regularizedGaussHGFun` "
                     "(FLINT docstring value 0.1283296212308777999675009)"),
            chk("2F1(sqrt2, 1/2; sqrt2 + 3/2; 9/10, abc=True)",
                lambda: A("9/10").hypgeom_2f1(A(2).sqrt(), A(Fraction(1, 2)),
                                              A(2).sqrt() + A(Fraction(3, 2)), abc=True),
                M(mpmath.hyp2f1(mpmath.sqrt(2), mpmath.mpf(1) / 2,
                                mpmath.sqrt(2) + mpmath.mpf(3) / 2, mpmath.mpf(9) / 10)),
                note="a + b - c = 1 is an exact integer although the parameters are "
                     "inexact: abc=True selects the Gauss transformation path "
                     "(without the flag Arb reports 'no convergence')"),
            # ---- hypgeom_u ---------------------------------------------------
            chk("U(1, 1, 1) = e E_1(1)", lambda: A(1).hypgeom_u(A(1), A(1)),
                M(mpmath.hyperu(1, 1, 1)),
                note="hypgeom_u: Tricomi's confluent function U(a, b, z)"),
            chk("U(2, 3, 1/2) = 4 exactly", lambda: A(Fraction(1, 2)).hypgeom_u(A(2), A(3)),
                P(4), note="closed form U(2, 3, z) = z^-2 by Kummer's transformation"),
            # ---- the general entry point on the specialized domain -----------
            chk("hypgeom 0F1([], [2]; 1)", lambda: A(1).hypgeom([], [A(2)]),
                M(mpmath.hyp0f1(2, 1)), note="general form: lists of upper/lower parameters"),
            chk("hypgeom 1F1([2], [1]; 1)", lambda: A(1).hypgeom([A(2)], [A(1)]),
                M(mpmath.hyp1f1(2, 1, 1))),
            chk("hypgeom 2F1([1, 1], [2]; 1/2)",
                lambda: A(Fraction(1, 2)).hypgeom([A(1), A(1)], [A(2)]),
                M(mpmath.hyp2f1(1, 1, 2, 0.5)),
                lean="ordinaryHypergeometric ℝ (1 : ℚ) (1 : ℚ) (2 : ℚ) (1 / 2 : ℝ)"),
        ]),

    # ------------------------------------------------------------------ D07
    fam("D07", "—", "bessel_airy_coulomb_zoo",
        "Bessel (J/Y/I/K), Airy (Ai/Bi + zeros) and Coulomb wave functions",
        "x = 1, 2; order 1, 2; l = 0, eta = 1",
        "12 Arb entry points against mpmath (no mathlib counterpart: Arb-only coverage)",
        [
            chk("bessel_j: J_1(2)", lambda: A(2).bessel_j(1), M(mpmath.besselj(1, 2))),
            chk("bessel_y: Y_1(2)", lambda: A(2).bessel_y(1), M(mpmath.bessely(1, 2))),
            chk("bessel_i: I_1(2)", lambda: A(2).bessel_i(1), M(mpmath.besseli(1, 2))),
            chk("bessel_k: K_1(2)", lambda: A(2).bessel_k(1), M(mpmath.besselk(1, 2))),
            chk("airy_ai(1)", lambda: A(1).airy_ai(), M(mpmath.airyai(1))),
            chk("airy_bi(1)", lambda: A(1).airy_bi(), M(mpmath.airybi(1))),
            chk("airy(1).Ai'", lambda: A(1).airy()[1], M(mpmath.airyai(1, 1))),
            chk("airy(1).Bi'", lambda: A(1).airy()[3], M(mpmath.airybi(1, 1))),
            chk("airy_ai_zero(1)", lambda: A(0).airy_ai_zero(1), M(mpmath.airyaizero(1))),
            chk("airy_bi_zero(1)", lambda: A(0).airy_bi_zero(1),
                M(mpmath.airybizero(1))),
            chk("coulomb_f: F_0(eta=1, x=1)", lambda: A(1).coulomb_f(0, 1),
                M(mpmath.coulombf(0, 1, 1))),
            chk("coulomb_g: G_0(eta=1, x=1)", lambda: A(1).coulomb_g(0, 1),
                M(mpmath.coulombg(0, 1, 1))),
            chk("coulomb(1, 0, eta=1) = (F, G)", lambda: A(1).coulomb(0, 1)[1],
                M(mpmath.coulombg(0, 1, 1)), note="the tuple entry point returns both F and G"),
        ]),

    # ------------------------------------------------------------------ D08
    fam("D08", "—", "exponential_integral_zoo",
        "exponential/trigonometric integrals: Ei, li, Si, Ci, Shi, Chi, E_n",
        "x = 1, 2; n = 1, 2",
        "8 Arb entry points against mpmath (no mathlib counterpart)",
        [
            chk("ei(1)", lambda: A(1).ei(), M(mpmath.ei(1))),
            chk("li(2)", lambda: A(2).li(), M(mpmath.li(2))),
            chk("si(1)", lambda: A(1).si(), M(mpmath.si(1))),
            chk("ci(1)", lambda: A(1).ci(), M(mpmath.ci(1))),
            chk("shi(1)", lambda: A(1).shi(), M(mpmath.shi(1))),
            chk("chi(1)", lambda: A(1).chi(), M(mpmath.chi(1))),
            chk("expint: E_1(2)", lambda: A(2).expint(1), M(mpmath.e1(2))),
            chk("expint: E_2(2)", lambda: A(2).expint(2), M(mpmath.expint(2, 2))),
        ]),

    # ------------------------------------------------------------------ D09
    fam("D09", "—", "error_function_zoo",
        "error functions and Fresnel integrals: erf, erfc, erfi, erfinv, erfcinv, S, C",
        "x = 1, 1/2",
        "7 Arb entry points against mpmath (no mathlib counterpart)",
        [
            chk("erf(1)", lambda: A(1).erf(), M(mpmath.erf(1))),
            chk("erfc(1)", lambda: A(1).erfc(), M(mpmath.erfc(1))),
            chk("erfi(1)", lambda: A(1).erfi(), M(mpmath.erfi(1))),
            chk("erfinv(1/2)", lambda: A(Fraction(1, 2)).erfinv(), M(mpmath.erfinv(0.5))),
            chk("erfcinv(1/2)", lambda: A(Fraction(1, 2)).erfcinv(), M(mpmath.erfinv(0.5))),
            chk("fresnel_s(1)", lambda: A(1).fresnel_s(), M(mpmath.fresnels(1))),
            chk("fresnel_c(1)", lambda: A(1).fresnel_c(), M(mpmath.fresnelc(1))),
        ]),

    # ------------------------------------------------------------------ D10
    fam("D10", "F04d+F05", "agm_lambertw_orthogonal_zoo",
        "AGM, Lambert W and the orthogonal-polynomial family "
        "(Chebyshev T/U, Gegenbauer, Hermite, Jacobi, Laguerre, Legendre P/Q)",
        "x = 1/2, 0; degrees 2, 3",
        "13 Arb entry points (mpmath / closed forms); Chebyshev and AGM exist in mathlib",
        [
            chk("agm(1, 2)", lambda: A(1).agm(A(2)), M(mpmath.agm(1, 2)),
                ),
            chk("lambertw(1)", lambda: A(1).lambertw(), M(mpmath.lambertw(1))),
            chk("chebyshev_t(3)(1/2)", lambda: A(Fraction(1, 2)).chebyshev_t(3), P(-1),
                lean="(((Polynomial.Chebyshev.T ℚ 3).eval (1 / 2) : ℚ) : ℝ)"),
            chk("chebyshev_u(2)(0)", lambda: A(0).chebyshev_u(2), P(-1),
                lean="(((Polynomial.Chebyshev.U ℚ 2).eval (0 : ℚ) : ℚ) : ℝ)"),
            chk("gegenbauer_c(3,1)(1/2)", lambda: A(Fraction(1, 2)).gegenbauer_c(3, 1), P(-1)),
            chk("hermite_h(3)(1/2)", lambda: A(Fraction(1, 2)).hermite_h(3), P(-5)),
            chk("jacobi_p(2,1,1)(1/2)", lambda: A(Fraction(1, 2)).jacobi_p(2, 1, 1), P(3, 16)),
            chk("laguerre_l(3,0)(1/2)", lambda: A(Fraction(1, 2)).laguerre_l(3, 0), P(-7, 48)),
            chk("legendre_p(2,0)(1/2)", lambda: A(Fraction(1, 2)).legendre_p(2, 0), P(-1, 8)),
            chk("legendre_q(2,0)(1/2)", lambda: A(Fraction(1, 2)).legendre_q(2, 0),
                M(mpmath.legenq(2, 0, mpmath.mpf("0.5")))),
            chk("legendre_p_root(2, 1)", lambda: A(0).legendre_p_root(2, 1),
                M(-1 / mpmath.sqrt(3)), note="roots come out in descending order, k is 0-based"),
            chk("legendre_p_root(3, 2)", lambda: A(0).legendre_p_root(3, 2),
                M(-mpmath.sqrt(mpmath.mpf(3) / 5))),
            chk("legendre_p(1,1)(1/2) = -sqrt(1-x^2)", lambda: A(Fraction(1, 2)).legendre_p(1, 1),
                M(-mpmath.sqrt(3) / 2)),
        ]),

    # ------------------------------------------------------------------ D11
    fam("D11", "F06", "combinatorial_zoo",
        "combinatorial layer: bin, bin_uiui, fac, fac_ui, fib, Bernoulli numbers and "
        "polynomials, Bell numbers, partitions, rising factorial",
        "n = 0..100, k = 2 (exact integer values)",
        "14 Arb entry points against exact rational values (no floating reference needed)",
        [
            chk("bin(5, 2)", lambda: A(5).bin(2), P(10), lean="(Nat.choose 5 2 : ℝ)"),
            chk("bin_uiui(10, 3)", lambda: A(0).bin_uiui(10, 3), P(120)),
            chk("fac(10)", lambda: A(10).fac(), P(3628800),
                lean="(Nat.factorial 10 : ℝ)"),
            chk("fac_ui(20)", lambda: A(0).fac_ui(20), P(2432902008176640000)),
            chk("fib(20)", lambda: A(0).fib(20), P(6765), lean="(Nat.fib 20 : ℝ)"),
            chk("fib(0)", lambda: A(0).fib(0), P(0)),
            chk("bernoulli(1)", lambda: A(0).bernoulli(1), P(-1, 2), lean="(bernoulli 1 : ℝ)"),
            chk("bernoulli(6)", lambda: A(0).bernoulli(6), P(1, 42), lean="(bernoulli 6 : ℝ)"),
            chk("bernoulli_poly(3)(1/2)", lambda: A(Fraction(1, 2)).bernoulli_poly(3), P(0),
                lean="(((Polynomial.bernoulli 3).eval (1 / 2) : ℚ) : ℝ)"),
            chk("bell_number(10)", lambda: A(0).bell_number(10), P(115975),
                lean="(Nat.bell 10 : ℝ)"),
            chk("partitions_p(10)", lambda: A(0).partitions_p(10), P(42)),
            chk("partitions_p(100)", lambda: A(0).partitions_p(100), P(190569292)),
            chk("rising(2, 3) = 2*3*4", lambda: A(2).rising(3), P(24)),
            chk("gamma_fmpq(1/2) = sqrt(pi)", lambda: A(0).gamma_fmpq(fmpq(1, 2)),
                M(mpmath.sqrt(mpmath.pi))),
        ]),

    # ------------------------------------------------------------------ D12
    fam("D12", "F07+F08", "constants_rounding_zoo",
        "constants (pi, e, gamma, log 2, log 10, sqrt pi, Catalan, Glaisher, Khinchin) and "
        "the rounding/integer layer (floor, ceil, sgn, abs bounds, integer predicates)",
        "points and intervals",
        "18 Arb entry points; mpmath constants + exact integer claims",
        [
            chk("const_pi", lambda: A(0).pi(), M(mpmath.pi), lean="Real.pi"),
            chk("const_e", lambda: A(0).const_e(), M(mpmath.e), lean="Real.exp 1"),
            chk("const_euler", lambda: A(0).const_euler(), M(mpmath.euler),
                lean="Real.eulerMascheroniConstant"),
            chk("const_log2", lambda: A(0).const_log2(), M(mpmath.log(2)), lean="Real.log 2"),
            chk("const_log10", lambda: A(0).const_log10(), M(mpmath.log(10)), lean="Real.log 10"),
            chk("const_sqrt_pi", lambda: A(0).const_sqrt_pi(), M(mpmath.sqrt(mpmath.pi)),
                lean="Real.sqrt Real.pi"),
            chk("const_catalan", lambda: A(0).const_catalan(), M(mpmath.catalan)),
            chk("const_glaisher", lambda: A(0).const_glaisher(), M(mpmath.glaisher)),
            chk("const_khinchin", lambda: A(0).const_khinchin(), M(mpmath.khinchin)),
            chk("sgn(1/2)", lambda: A(Fraction(1, 2)).sgn(), P(1), lean="Real.sign (1 / 2)"),
            chk("floor([1/4, 7/4]) = [0, 1]", lambda: I(Fraction(1, 4), Fraction(7, 4)).floor(),
                P(1), note="point floor([1/4,7/4]) = 1; as an interval operation it yields [0, 1]"),
            chk("ceil([1/4, 7/4]) = [1, 2]", lambda: I(Fraction(1, 4), Fraction(7, 4)).ceil(),
                P(2), note="point ceil([1/4,7/4]) = 2"),
            chk("floor(17/5) = 3", lambda: A(Fraction(17, 5)).floor(), P(3),
                lean="((⌊(17 / 5 : ℝ)⌋ : ℤ) : ℝ)"),
            chk("ceil(17/5) = 4", lambda: A(Fraction(17, 5)).ceil(), P(4),
                lean="((⌈(17 / 5 : ℝ)⌉ : ℤ) : ℝ)"),
            chk("abs_lower([-5, 5]) = 0", lambda: I(-5, 5).abs_lower(), P(0)),
            chk("abs_upper([-5, 5]) >= 5", lambda: I(-5, 5).abs_upper(), P(5), mode="ge"),
            chk("contains_integer(7)", lambda: A(1) if A(7).contains_integer() else A(0), P(1),
                note="returns a Bool, compared as 1/0"),
            chk("unique_fmpz(7) = 7", lambda: A(int(A(7).unique_fmpz())), P(7)),
        ]),

    # ------------------------------------------------------------------ D13
    fam("D13", "—", "complex_ball_extras",
        "complex-ball extras (elliptic, modular and zeta-zero machinery): polygamma, "
        "Jacobi theta, Riemann zeros, Weierstrass zeta/sigma",
        "z = 2, 1/2, tau = i (points)",
        "10 checks: mpmath references for polygamma/theta/zeros, and rigorous identities "
        "(quasi-periodicity) + two-precision agreement for the Weierstrass functions",
        [
            chk("polygamma(1, 2)", lambda: acb(2).polygamma(1).real, M(mpmath.polygamma(1, 2))),
            chk("polygamma(2, 2)", lambda: acb(2).polygamma(2).real, M(mpmath.polygamma(2, 2))),
            chk("theta3(1/2, i)", lambda: acb(fmpq(1, 2)).modular_theta(acb(0, 1))[2].real,
                M(mpmath.jtheta(3, mpmath.pi / 2, mpmath.exp(-mpmath.pi))),
                note="Arb's theta convention includes the factor pi for z"),
            chk("theta4(1/2, i)", lambda: acb(fmpq(1, 2)).modular_theta(acb(0, 1))[3].real,
                M(mpmath.jtheta(4, mpmath.pi / 2, mpmath.exp(-mpmath.pi)))),
            chk("theta2(1/2, i) = 0", lambda: acb(fmpq(1, 2)).modular_theta(acb(0, 1))[1].real,
                P(0), note="theta2 vanishes at u = pi/2"),
            chk("zeta_zero(1).im", lambda: acb(0).zeta_zero(1).imag,
                M(mpmath.zetazero(1).imag), note="first nontrivial zero of zeta on 1/2 + i t"),
            chk("zeta_zero(3).im", lambda: acb(0).zeta_zero(3).imag, M(mpmath.zetazero(3).imag)),
            chk("elliptic_zeta quasi-periodicity zeta(3/2) - 3 zeta(1/2)",
                lambda: acb(fmpq(3, 2)).elliptic_zeta(acb(0, 1)).real
                - 3 * acb(fmpq(1, 2)).elliptic_zeta(acb(0, 1)).real, P(0),
                note="zeta(z + 1) = zeta(z) + 2 eta1 with eta1 = zeta(1/2)"),
            chk("elliptic_zeta two-precision agreement",
                two_prec(lambda: acb(fmpq(2, 3)).elliptic_zeta(acb(0, 1)).real), P(0)),
            chk("elliptic_sigma quasi-periodicity sigma(3/2) + exp(2 eta1) sigma(1/2)",
                lambda: acb(fmpq(3, 2)).elliptic_sigma(acb(0, 1)).real
                + (2 * acb(fmpq(1, 2)).elliptic_zeta(acb(0, 1)).real).exp()
                * acb(fmpq(1, 2)).elliptic_sigma(acb(0, 1)).real, P(0),
                note="sigma(z + 1) = -exp(2 eta1 (z + 1/2)) sigma(z) at z = 1/2"),
        ]),
    # ------------------------------------------------------------------ D14
    fam("D14", "F04d", "hypergeometric_general_zoo",
        "the generalized hypergeometric entry point hypgeom(a, b; z): exactly the "
        "parameter vectors Arb has *no* specialized implementation for",
        "z = 1/2, 1/4 (points); 3F2, 2F3 and 4F3 parameter vectors (5-7 parameters)",
        "5 checks; each has strictly more parameters than any specialized form "
        "(0F1/1F1/2F1/U take at most 3); mpmath references + one exact rational",
        [
            chk("3F2([1,1,1], [2,2]; 1/2)",
                lambda: A(Fraction(1, 2)).hypgeom([A(1), A(1), A(1)], [A(2), A(2)]),
                M(mpmath.hyper([1, 1, 1], [2, 2], mpmath.mpf(1) / 2)),
                lean="Complex.regularizedHGFun {1, 1, 1} {2, 2} (1 / 2)",
                note="5 parameters; p = 3 > q = 2 -- no specialized Arb kernel"),
            chk("2F3([1,2], [3,4,5]; 1/4)",
                lambda: A(Fraction(1, 4)).hypgeom([A(1), A(2)], [A(3), A(4), A(5)]),
                M(mpmath.hyper([1, 2], [3, 4, 5], mpmath.mpf(1) / 4)),
                lean="Complex.regularizedHGFun {1, 2} {3, 4, 5} (1 / 4)",
                note="5 parameters; p + 1 < q (entire, minimal type)"),
            chk("2F3([1,2], [3,4,5]; 1/4) regularized (= /288)",
                lambda: A(Fraction(1, 4)).hypgeom([A(1), A(2)], [A(3), A(4), A(5)],
                                                  regularized=True),
                M(mpmath.hyper([1, 2], [3, 4, 5], mpmath.mpf(1) / 4)
                  / (mpmath.gamma(3) * mpmath.gamma(4) * mpmath.gamma(5))),
                note="regularized=True divides by Gamma(3)Gamma(4)Gamma(5) = 288 "
                     "(mathlib's `Complex.regularizedHGFun` is this normalized version)"),
            chk("4F3([1,1,1,1], [2,2,2]; 1/4)",
                lambda: A(Fraction(1, 4)).hypgeom([A(1)] * 4, [A(2)] * 3),
                M(mpmath.hyper([1, 1, 1, 1], [2, 2, 2], mpmath.mpf(1) / 4)),
                lean="Complex.regularizedHGFun {1, 1, 1, 1} {2, 2, 2} (1 / 4)",
                note="7 parameters -- three more than any specialized form"),
            chk("3F2([-3,1,1], [2,2]; 1/2) terminating = 269/384 exactly",
                lambda: A(Fraction(1, 2)).hypgeom([A(-3), A(1), A(1)], [A(2), A(2)]),
                P(269, 384),
                lean="Complex.regularizedHGFun {(-3 : ℂ), 1, 1} {2, 2} (1 / 2)",
                note="a negative integer numerator parameter terminates the series "
                     "after three terms: the exact rational 269/384"),
        ]),

]


FAMILIES_BY_ID = {f["id"]: f for f in FAMILIES}

# functions with a mathlib counterpart at the pinned rev -> Lean goals
LEAN_FAMS = [f for f in FAMILIES if f["lean"] != "—"]


# --------------------------------------------------------------------------
# evaluation
# --------------------------------------------------------------------------

def eval_check(c, rel_tol=Fraction(1, 10 ** 13)):
    """Return (ok, lo, hi, err, ref) for one check (None-valued = special case)."""
    if c["call"] is None:
        return None
    x = c["call"]()
    ref = c["ref"]
    tol = rel_tol * max(Fraction(1), abs(ref))
    mode = c.get("mode", "contains")
    if mode == "contains":
        ok = lb(x) - tol <= ref <= ub(x) + tol
        err = max(abs(ref - lb(x)), abs(ref - ub(x)))
    elif mode == "ge":                       # certified: value >= ref
        ok = lb(x) >= ref - tol
        err = ref - lb(x)
    else:                                    # certified: value <= ref
        ok = ub(x) <= ref + tol
        err = ub(x) - ref
    return ok, lb(x), ub(x), err, ref


def run_family(f, rel_tol=Fraction(1, 10 ** 13)):
    """Evaluate a family: returns (n_ok, n_total, summary_text, details)."""
    ok_n, n, details, fails = 0, 0, [], []
    for c in f["checks"]:
        r = eval_check(c, rel_tol)
        if r is None:                        # interval-valued / custom check
            continue
        ok, lo, hi, err, ref = r
        n += 1
        ok_n += bool(ok)
        details.append((c["fn"], lo, hi, err))
        if not ok:
            fails.append(f"{c['fn']}: enclosure [{T.show(_lit(lo), 18)}, {T.show(_lit(hi), 18)}] "
                         f"misses {float(ref):.20g}")
    return ok_n, n, details, fails


def _lit(fr):
    """Fraction -> arb (for display only)."""
    return A(fr)


def summary(f, details, limit=6):
    """Compact one-line summary of a family for RESULTS.md."""
    parts = [f"{fn} = {T.show(_lit(lo), 18).split(' +/-')[0].strip('[]')}"
             for fn, lo, hi, err in details[:limit]]
    more = "" if len(details) <= limit else f", + {len(details) - limit} more"
    return "; ".join(parts) + more


def widths(f, details):
    w = [float(hi - lo) for _, lo, hi, _ in details]
    return (max(w) if w else 0.0)
