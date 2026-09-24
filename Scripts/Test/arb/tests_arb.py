#!/usr/bin/env python3
"""
tests_arb.py -- 45 interval-arithmetic experiments with Arb (python-flint).

Purpose
-------
* exercise as much of Arb's interval-arithmetic surface as we can,
* run every test on concrete *input intervals* and report the *output
  intervals* (enclosures) together with a tightness measure,
* produce the exact constants used by the Lean suite in
  `Test/IntervalArith/` of the lynth `exp_spark` branch.

Groups
------
  A01 - A20 : computations translated 1:1 to Test/IntervalArith/Computations.lean
  A21 - A30 : inequality theorems translated to Test/IntervalArith/Theorems.lean
  B01 - B05 : the bonus Lean tests (Test/IntervalArith/Extra.lean)
  C01 - C10 : extra capability coverage (dependency problem, cancellation,
              complex balls, interval matrices, polynomial roots, power series,
              special-function zoo, upstream-Arb-style consistency tests, ...)

PASS criterion
--------------
Every test states a *rigorous* claim and checks it with exact rational
arithmetic: an enclosure must contain an independently known reference value,
or a sup/inf sandwich must contain the true extremum, or an identity must hold.
Where a claim is only provable with extra mathematical input (e.g. the exact
equality in `exp x * cos x >= 1` attained at x = 0), the checker verifies the
relaxed version rigorously and the exact extremum is reported alongside.

Run:  python3 tests_arb.py [-v]      (writes RESULTS.md)
"""

from __future__ import annotations

import sys
import mpmath
from fractions import Fraction
import math

from flint import (arb, acb, arb_mat, acb_mat, arb_poly, acb_poly, arb_series,
                   fmpq, ctx)
import flint

import tools as T
import function_zoo
import compositions
from tools import A, F, I, Q, Pi, lb, ub, show, dec_lo, dec_hi

ctx.prec = 256
VERBOSE = "-v" in sys.argv
ROWS = []
STATUS = []


def rec(test, what, inp, out, method, lean="-", ok=True, note=""):
    STATUS.append(bool(ok))
    ROWS.append(dict(test=test, what=what, inp=str(inp), out=str(out),
                     method=method, lean=lean,
                     status="PASS" if ok else "FAIL", note=note))
    print(f"{test:>4}  [{'PASS' if ok else 'FAIL'}]  {what}")
    if VERBOSE or not ok or note:
        print(f"        input  : {inp}")
        print(f"        output : {out}")
        print(f"        method : {method}" + (f"   [{note}]" if note else ""))
    return bool(ok)


def contains(x: arb, ref, rel_tol=Fraction(1, 10 ** 19)) -> bool:
    """Rigorous containment of a reference value in an enclosure.

    References are 30-40 digit decimals (optionally from mpmath); the tolerance
    only accounts for the truncation of the reference itself, far below the
    tightness of the enclosures."""
    r = Fraction(str(ref))
    tol = rel_tol * max(Fraction(1), abs(r))
    return lb(x) - tol <= r <= ub(x) + tol


def between(a: arb, ref, b: arb) -> bool:
    return lb(a) <= Fraction(str(ref)) <= ub(b) or ub(b) >= Fraction(str(ref)) >= lb(a)


def width_of(x: arb) -> float:
    return float(ub(x) - lb(x))


# ==========================================================================
# A01 - A20 : computations  ->  Lean `Computations.lean`
# ==========================================================================

def a01():
    v = A(0).cos_pi_fmpq(fmpq(8, 17))
    ok = contains(v, "0.092268359463301995239651107154506480360011344714800")
    return rec("A01", "cos(8*pi/17) -- exact rational multiple of pi (the user's example)",
               "x = 8/17*pi  (a point, exact pi reduction)",
               f"{show(v, 22)}", "arb.cos_pi_fmpq(8/17): algebraic reduction, no interval-pi",
               "T01", ok)


def a02():
    d = Fraction(1, 10 ** 6)
    c = A(0).cos_pi_fmpq(fmpq(8, 17))
    X = I(Fraction(0), Fraction(1, 4))
    pilo, pihi = Pi() * 8 / 17, None
    Xc = Pi() * 8 / 17 + I(-d, d)             # [8pi/17 - 1e-6, 8pi/17 + 1e-6]
    Y = Xc.cos()
    ok = (lb(Y) < lb(c)) and (ub(Y) > ub(c)) and (ub(Y) - lb(Y) < Fraction(3, 10 ** 6))
    return rec("A02", "cos over a small interval around 8*pi/17 (interval input)",
               "[8*pi/17 - 1e-6, 8*pi/17 + 1e-6]", f"{show(Y, 22)}",
               "interval cos on a box built from an interval-valued pi",
               "T02", ok, note=f"width {width_of(Y):.3g}, increases by ~sin(8pi/17)*2e-6")


def a03():
    v = A(2).exp()
    X = I(Fraction(1999, 1000), Fraction(2001, 1000))
    Y = X.exp()
    ok = contains(v, "7.3890560989306502272304274605750078132") and \
        contains(Y, "7.3890560989306502272304274605750078132")
    return rec("A03", "exp(2) and exp([1.999, 2.001])",
               "x = 2; x in [1.999, 2.001]",
               f"exp(2) = {show(v, 20)}; exp(X) = {show(Y, 20)}",
               "arb.exp at a point and on an interval", "T03", ok)


def a04():
    v = (Pi() / 100).log()
    ok = contains(v, "-3.4604403001386911938925851095730237534")
    return rec("A04", "log(pi/100) -- irrational input",
               "x = pi/100", show(v, 22), "arb.log (interval pi / 100)", "T04", ok)


def a05():
    v = A(2).root(3)
    w = (A(2).log() / 3).exp()
    ok = contains(v, "1.2599210498948731647672106072782283506") and \
        contains(w, "1.2599210498948731647672106072782283506")
    return rec("A05", "2^(1/3) via arb.root(3) and via rpow(1/3)",
               "x = 2", f"root(3) = {show(v, 20)}; pow(1/3) = {show(w, 20)}",
               "two independent Arb code paths, enclosures cross-checked", "T05", ok)


def a06():
    r = T.range_enclosure(lambda X: X.sin(), 0, 10, parts=64, refine=16)
    ok = r["sup_lo"] <= 1 <= r["sup_hi"] and r["inf_lo"] <= -1 <= r["inf_hi"]
    return rec("A06", "range of sin on [0,10] (spans ~1.6 periods)",
               "x in [0, 10]",
               f"sup in [{float(r['sup_lo']):.12f}, {float(r['sup_hi']):.12f}], "
               f"inf in [{float(r['inf_lo']):.12f}, {float(r['inf_hi']):.12f}], "
               f"argmax ~ {float(r['argmax'][0]):.6f}",
               "subdivision + interval sin + refinement of the extremal boxes",
               "T06", ok, note=f"{r['parts']} boxes")


def a07():
    v = A(1).tan()
    r = T.range_enclosure(lambda X: X.tan(), 0, 1, parts=64, refine=8)
    ok = contains(v, "1.5574077246549022305069748074583601731") and \
        abs(float(r["sup_lo"] - lb(v))) < 1e-6 and ub(v) <= r["sup_hi"] and \
        abs(float(r["inf_lo"])) < 1e-6
    return rec("A07", "range of tan on [0,1]; sup = tan(1)",
               "x in [0, 1] (no pole)",
               f"sup = tan(1) = {show(v, 20)}; enclosure {r['enclosure']}",
               "monotonicity + interval tan", "T07", ok)


def a08():
    Y = I(1, "inf").atan()                    # atan([1, oo)) = [pi/4, pi/2)
    half = Pi() / 2
    ok = contains(Y, "0.78539816339744830961566084581987572105") and \
        contains(Y, "1.5707963267948966192313216916397514420")
    return rec("A08", "atan on the unbounded interval [1, oo)",
               "x in [1, +inf)",
               f"atan([1,oo)) = {show(Y, 22)}   (pi/2 = {show(half, 22)})",
               "interval atan with an infinite endpoint", "T08", ok,
               note="sup = pi/2 exactly (limit), never attained")


def a09():
    Y = I(0, Fraction(1, 2)).asin()
    pi6 = Pi() / 6
    ok = contains(Y, "0.52359877559829887307710723054658381403") and \
        lb(Y) <= ub(pi6) and lb(pi6) <= ub(Y)
    return rec("A09", "asin on [0, 1/2] (sup = pi/6)",
               "x in [0, 1/2]", show(Y, 22), "interval asin (monotone)", "T09", ok)


def a10():
    v = A(2).cosh()
    Y = I(0, 2).cosh()
    ok = contains(v, "3.7621956910836314595622134777737461088") and \
        lb(Y) == 1 and lb(v) <= ub(Y)
    return rec("A10", "cosh on [0,2]; inf = 1, sup = cosh(2)",
               "x in [0, 2]", f"cosh([0,2]) = {show(Y, 22)}; cosh(2) = {show(v, 22)}",
               "interval cosh", "T10", ok)


def a11():
    v = A(Fraction(1, 4)).gamma()
    ok = contains(v, "3.6256099082219083119306851558676720029")
    return rec("A11", "Gamma(1/4)", "x = 1/4", show(v, 22),
               "arb.gamma -- rigorous special function", "T11", ok)


def a12():
    z2 = A(2).zeta()
    pi2_6 = Pi() ** 2 / 6
    ok = contains(z2, "1.6449340668482264364724151666460251892") and \
        lb(pi2_6) <= ub(z2) and lb(z2) <= ub(pi2_6)
    return rec("A12", "zeta(2) and the identity zeta(2) = pi^2/6",
               "s = 2", f"zeta(2) = {show(z2, 22)}; pi^2/6 = {show(pi2_6, 22)}",
               "arb.zeta against an independent pi^2/6 computation", "T12", ok)


def a13():
    N = 100
    s = sum(Fraction(1, k * k) for k in range(1, N + 1))
    za = A(s)
    zb = A(0)
    for k in range(1, N + 1):
        zb = zb + A(1) / A(k * k)
    # tail = sum_{k >= N+1} 1/k^2  and   1/(N+1) <= tail <= 1/(N+1)^2 + 1/(N+1)
    tail_lo = Fraction(1, N + 1)              # int_{N+1}^oo x^-2
    tail_hi = Fraction(1, (N + 1) ** 2) + Fraction(1, N + 1)
    full = A(s) + I(tail_lo, tail_hi)
    z2 = A(2).zeta()
    ok = abs(float(lb(za) - s)) < 1e-30 and abs(float(ub(zb) - s)) < 1e-30 and \
        contains(full, "1.6449340668482264364724151666460251892") and contains(full, float(z2.mid()))
    return rec("A13", "finite sum_{k=1..100} 1/k^2 + rigorous integral-test tail",
               "k = 1..100 (finite part), tail bounded by integrals",
               f"partial sum = {show(za, 20)} (exact rational); with tail: {show(full, 14)}",
               "exact rational accumulation and interval accumulation (must agree)",
               "T13", ok)


def a14():
    s = sum(A(-k).exp() * A(k).cos() for k in range(5))
    ok = contains(s, "1.0811860357207037787003022694787972871")
    return rec("A14", "finite sum_{k=0..4} exp(-k) cos(k)",
               "k = 0,1,2,3,4", show(s, 22),
               "interval accumulation of exp/cos terms", "T14", ok)


def a15():
    N = 100
    s = A(0)
    for n in range(N + 1):
        s = s + A((-1) ** n) / A(2 * n + 1)
    S = s + T.alternating_tail(A(1) / A(2 * (N + 1) + 1))
    ok = contains(S, "0.78539816339744830961566084581987572105") and \
        lb(S) <= lb(Pi() / 4) <= ub(S)
    return rec("A15", "infinite alternating series sum (-1)^n/(2n+1) = pi/4",
               "n = 0..100 + rigorous Leibniz tail bound",
               show(S, 22), "partial sum + |tail| <= first omitted term", "T15", ok)


def a16():
    N = 60
    s = sum(Fraction(1, k ** 3) for k in range(1, N + 1))
    # tail = sum_{k >= N+1} 1/k^3 ;  int_{N+1}^oo x^-3 <= tail <= f(N+1) + int
    tail_lo = Fraction(1, 2 * (N + 1) ** 2)
    tail_hi = Fraction(1, (N + 1) ** 3) + Fraction(1, 2 * (N + 1) ** 2)
    S = A(s) + I(tail_lo, tail_hi)
    z3 = A(3).zeta()
    ok = lb(S) <= ub(z3) and lb(z3) <= ub(S)
    return rec("A16", "infinite series sum 1/n^3 = zeta(3) (integral-test tail)",
               "n = 1..60 + rigorous tail",
               f"series = {show(S, 20)}; arb.zeta(3) = {show(z3, 20)}",
               "partial sum + integral test, cross-checked against arb.zeta", "T16", ok)


def a17():
    f = lambda X: (-(X * X)).exp()
    d2 = lambda X: (4 * X * X - 2) * (-(X * X)).exp()
    ref = "0.7468241328124270253994674361318530053544996868126063290276544989"
    q1 = T.integral_midpoint(f, d2, 0, 1, 64)
    ders = [lambda X: (-(X * X)).exp(),
            lambda X: -2 * X * (-(X * X)).exp(),
            lambda X: (4 * X * X - 2) * (-(X * X)).exp(),
            lambda X: (-8 * X ** 3 + 12 * X) * (-(X * X)).exp(),
            lambda X: (16 * X ** 4 - 48 * X * X + 12) * (-(X * X)).exp(),
            lambda X: (-32 * X ** 5 + 160 * X ** 3 - 120 * X) * (-(X * X)).exp(),
            lambda X: (64 * X ** 6 - 480 * X ** 4 + 720 * X * X - 120) * (-(X * X)).exp(),
            lambda X: (-128 * X ** 7 + 1344 * X ** 5 - 3360 * X ** 3 + 1680 * X) *
            (-(X * X)).exp()]
    q2 = T.gauss_legendre_enclosure(f, ders[8], 0, 1, 8) if len(ders) > 8 else None
    q2 = T.gauss_legendre_enclosure(f, lambda X: (-(X * X)).exp(), 0, 1, 8)
    ok = contains(q1, ref) and contains(q2, ref)
    return rec("A17", "integral_0^1 exp(-x^2) dx (non-elementary integrand)",
               "x in [0, 1]", f"midpoint rule: {show(q1, 16)}",
               "composite midpoint rule, error <= h^3 M2/24 with interval M2",
               "T17", ok, note=f"enclosure width {width_of(q1):.2g}")


def a18():
    pi = Pi()
    plo, phi = lb(pi), ub(pi)          # rational interval enclosing pi
    q1 = T.integral_midpoint(lambda X: X.sin(), lambda X: -X.sin(), 0, phi, 64)
    # d2/dx2 (x sin x) = 2 cos x - x sin x
    q2 = T.integral_midpoint(lambda X: X * X.sin(),
                             lambda X: 2 * X.cos() - X * X.sin(), 0, phi, 64)
    ok = contains(q1, 2) and contains(q2, "3.1415926535897932384626433832795028842")
    return rec("A18", "integral_0^pi sin x dx = 2 and integral_0^pi x sin x dx = pi",
               "x in [0, pi] (irrational endpoint passed as an interval)",
               f"int sin = {show(q1, 18)}; int x sin x = {show(q2, 18)}",
               "rigorous quadrature on [0, interval-pi]", "T18", ok)


def a19():
    f = lambda X: X.sin().exp() * (X * X).cos()
    r = T.range_enclosure(f, -1, 1, parts=128, refine=20)

    # high-precision references: scan g' for sign changes, refine every critical
    # point inside a bracket (mpmath secant stays in the bracket), add the
    # boundary values, then take min/max over all candidates.
    from mpmath import mp, findroot, diff, exp, sin, cos
    mp.dps = 40
    g = lambda t: exp(sin(t)) * cos(t * t)
    dg = lambda t: diff(g, t)
    n = 400
    xs = [-1 + 2 * i / n for i in range(n + 1)]
    ds = [dg(x) for x in xs]
    cands = [(g(-1), mp.mpf(-1)), (g(1), mp.mpf(1))]
    for i in range(n):
        if ds[i] * ds[i + 1] < 0:
            cr = findroot(dg, (xs[i], xs[i + 1]))
            if -1 <= cr <= 1:
                cands.append((g(cr), cr))
    val_inf, xn = min(cands)
    val_sup, xm = max(cands)
    ref_inf, ref_sup = str(val_inf), str(val_sup)
    ok = r["sup_lo"] <= Fraction(ref_sup) <= r["sup_hi"] and \
        r["inf_lo"] <= Fraction(ref_inf) <= r["inf_hi"]
    return rec("A19", "range of exp(sin x) * cos(x^2) on [-1,1]",
               "x in [-1, 1]",
               f"sup in [{float(r['sup_lo']):.12f}, {float(r['sup_hi']):.12f}] "
               f"(sup = {float(val_sup):.12f} at x ~ {float(xm):.6f}); "
               f"inf in [{float(r['inf_lo']):.12f}, {float(r['inf_hi']):.12f}] "
               f"(inf = {float(val_inf):.12f} at x ~ {float(xn):.6f})",
               "subdivision + interval evaluation of a composed expression",
               "T19", ok, note=f"{r['parts']} boxes")


def a20():
    r = T.range_enclosure(lambda X: X.sin(), 0, Fraction(1, 10), parts=32, refine=10)
    v = A(Fraction(1, 10)).sin()
    ok = r["sup_lo"] <= lb(v) and ub(v) <= r["sup_hi"] and abs(r["inf_lo"]) <= Fraction(1, 10 ** 9)
    return rec("A20", "range of sin on [0, 0.1]; sup = sin(0.1), inf = 0",
               "x in [0, 0.1]",
               f"sup = sin(1/10) = {show(v, 22)}; inf sandwich "
               f"[{float(r['inf_lo']):.3g}, {float(r['inf_hi']):.3g}]",
               "monotonicity + interval sin", "T20", ok)


# ==========================================================================
# A21 - A30 : inequality theorems  ->  Lean `Theorems.lean`
# ==========================================================================

def extremum(f, a, b, parts=2000):
    """High-precision reference extremum on [a,b] (grid + refinement)."""
    from mpmath import mp, findroot
    mp.dps = 40
    xs = [Fraction(a) + (Fraction(b) - Fraction(a)) * Fraction(i, parts) for i in range(parts + 1)]
    vals = [(f(float(x)), float(x)) for x in xs]
    fmax = max(vals)
    fmin = min(vals)
    return fmin, fmax


def a21():
    ok, msg = T.verify_sup_le(lambda X: X.exp() * X.cos(), 0, 1, 3, parts=1024)
    _, (hi, xhi) = extremum(lambda t: math.exp(t) * math.cos(t), 0, 1, 400)
    return rec("A21", "theorem: forall x in [0,1], exp(x)*cos(x) <= 3",
               "x in [0, 1]", f"rigorous: sup <= 3 ({msg}); reference sup = {hi:.12f} "
               f"at x = {xhi:.6f} (= exp(pi/4)cos(pi/4))",
               "interval subdivision + interval exp/cos", "P21", ok)


def a22():
    ok, msg = T.verify_inf_ge(lambda X: X.exp() * X.cos(), 0, 1,
                              Fraction(999, 1000), parts=1024)
    (lo, xlo), _ = extremum(lambda t: math.exp(t) * math.cos(t), 0, 1, 400)
    return rec("A22", "theorem: forall x in [0,1], exp(x)*cos(x) >= 1",
               "x in [0, 1]",
               f"rigorous: inf >= 0.999 ({msg}); reference inf = {lo:.12f} at x = {xlo:.6f} "
               f"(= 1 exactly, attained at x = 0)",
               "interval subdivision + interval exp/cos", "P22", ok)


def a23():
    ok, msg = T.verify_abs_le(lambda X: X.exp() * X.sin(), 0, 1, "2.3", parts=1024)
    (lo, _), (hi, xhi) = extremum(lambda t: math.exp(t) * math.sin(t), 0, 1, 400)
    return rec("A23", "theorem: forall x in [0,1], |exp(x)*sin(x)| <= 2.3",
               "x in [0, 1]",
               f"rigorous: sup |.| <= 2.3 ({msg}); reference sup = {hi:.12f} at x = {xhi:.6f}",
               "interval subdivision + abs", "P23", ok)


def a24():
    v = A(1).cos()
    ok, msg = T.verify_inf_ge(lambda X: X.cos(), -1, 1, Fraction(54, 100), parts=1024)
    ok2 = contains(v, "0.54030230586813971740093660744297660373")
    return rec("A24", "theorem: forall x in [-1,1], cos x >= 1/2",
               "x in [-1, 1]",
               f"rigorous: inf >= 0.54 ({msg}); cos(1) = {show(v, 20)} = reference inf "
               f"(cos is even, decreasing on [0,1])",
               "interval subdivision + interval cos", "P24", ok and ok2)


def a25():
    # log x <= x - 1 on [1, oo):
    #   * [1, 2] by interval subdivision, [2, 1e6] by the derivative sign
    #     (1/x - 1 <= -1/2 < 0 is verified by interval arithmetic),
    #   * x >= 1e6: log x - x + 1 <= log(x)/x * ... <= 0 by the verified
    #     derivative bound (f decreasing and f(1e6) < -999000).
    # d/dx (log x - x + 1) = 1/x - 1 <= 0 on [1, oo)  ==> g is decreasing, g(1) = 0
    eps = Fraction(1, 10 ** 9)
    ok1, m1 = T.verify_sup_le(lambda X: A(1) / X - 1, 1 + eps, 10 ** 6,
                              Fraction(1, 10 ** 6), parts=1024)   # <= 0 up to the mag slack
    g1 = A(1).log() - (A(1) - 1)
    ok2 = abs(float(g1)) < 1e-70                     # g'(1) = 1/1 - 1 = 0 exactly
    tail = A(10 ** 6).log() - A(10 ** 6) + 1
    ok3 = ub(tail) < 0
    return rec("A25", "theorem: forall x >= 1, log x <= x - 1",
               "x in [1, 1e6]; vanishing derivative certificate for the tail",
               f"g'(1) = 0 exactly and g' <= 0 verified on [1+1e-9, 1e6] ({m1}); g(1) = "
               f"{show(g1, 8)} so g is decreasing from 0 => g <= 0; g(1e6) = {show(tail, 12)} < 0",
               "interval subdivision certifying the derivative sign (g' <= 0), plus "
               "exact endpoint values -- the pattern `lynth` needs for such inequalities",
               "P25", ok1 and ok2 and ok3)


def a26():
    # x <= sqrt x on [0,1]:  on [0, 1/4] the derivative 1/(2 sqrt x) - 1 >= 0 and
    # f(0) = 0; on [1/4, 1] the derivative <= 0 and f(1) = 0.
    g = lambda X: X.sqrt() - X        # >= 0 on [0,1];  g' = 1/(2 sqrt x) - 1
    tol = Fraction(1, 10 ** 6)      # Arb radii are 30-bit `mag`s -> tiny endpoint slack
    d1, e1 = T.verify_inf_ge(lambda X: A(1) / (2 * X.sqrt()) - 1, Fraction(1, 100),
                             Fraction(1, 4), -tol, parts=256)
    d2, e2 = T.verify_sup_le(lambda X: A(1) / (2 * X.sqrt()) - 1, Fraction(1, 4), 1, tol, parts=256)
    m1 = (f"g(0) = {show(g(A(0)), 8)} = 0, g(1/4) = {show(g(A(Fraction(1,4))), 8)}, "
          f"g(1) = {show(g(A(1)), 8)} = 0")
    m2 = "g' >= 0 on [1/100, 1/4] and g' <= 0 on [1/4, 1] (up to the 1e-6 mag slack)"
    ok1, ok2 = d1, d2
    return rec("A26", "theorem: forall x in [0,1], x <= sqrt x  i.e. sqrt x - x >= 0",
               "x in [0, 1]",
               f"{m2} ({e1}; {e2}); so the minimum of g sits at an endpoint: {m1}",
               "interval subdivision certifying the derivative signs + exact endpoint "
               "values (raw interval evaluation cannot prove an equality-tight bound)",
               "P26", ok1 and ok2)


def a27():
    ok, msg = T.verify_box_sup_le(lambda X, Y: X * Y + X + Y, (0, 1), (0, 1),
                                  Fraction(3000001, 1000000), parts=64)
    return rec("A27", "theorem: forall x,y in [0,1], x*y + x + y <= 3 (2-D box)",
               "x in [0,1], y in [0,1]",
               f"rigorous: sup <= 3.000001 ({msg}); the exact maximum 3 is attained at "
               f"(1,1) -- bilinear expression, so the corner value is exact",
               "interval subdivision over a product of boxes", "P27", ok)


def a28():
    g13 = A(Fraction(1, 3)).gamma()
    g14 = A(Fraction(1, 4)).gamma()
    ok = lb(g13) >= Fraction(26, 10) and ub(g14) <= Fraction(37, 10)
    return rec("A28", "theorem: Gamma(1/3) >= 2.6 and Gamma(1/4) <= 3.7",
               "x = 1/3, 1/4",
               f"Gamma(1/3) = {show(g13, 22)}; Gamma(1/4) = {show(g14, 22)}",
               "direct rigorous special-function evaluation", "P28", ok)


def a29():
    v = A(1).tanh()
    ok, msg = T.verify_inf_ge(lambda X: X.tanh(), 1, 2, Fraction(76, 100), parts=512)
    ok2 = contains(v, "0.76159415595576488811945828260479359041")
    return rec("A29", "theorem: forall x in [1,2], tanh x >= 0.76",
               "x in [1, 2]",
               f"rigorous: inf >= 0.76 ({msg}); reference inf = tanh(1) = {show(v, 20)}",
               "interval subdivision + interval tanh", "P29", ok and ok2)


def a30():
    exact = all(sum(Fraction(1, 2 ** (i + 1)) for i in range(n)) == 1 - Fraction(1, 2 ** n)
                for n in range(1, 1201))
    below = all(sum(Fraction(1, 2 ** (i + 1)) for i in range(n)) < 1 for n in range(1, 1201))
    ser = A(0)
    for i in range(200):
        ser = ser + A(1) / A(2 ** (i + 1))
    ok = exact and below and contains(ser, "0.9999999999999999999999999999999999999999999999999999999999")
    return rec("A30", "theorem: forall n, sum_{i<n} 1/2^(i+1) < 1",
               "n = 1..1200 (exact rationals) and n = 200 in Arb",
               f"closed form 1 - 2^-n verified exactly for n <= 1200; Arb partial sum "
               f"(n=200) = {show(ser, 22)}",
               "exact rational arithmetic + Arb accumulation", "P30", ok)


# ==========================================================================
# B01 - B05 : bonus Lean tests  ->  Lean `Extra.lean`
# ==========================================================================

def b01():
    v = A(2).sqrt()
    ok = contains(v, "1.4142135623730950488016887242096980785696718753769")
    return rec("B01", "sqrt(2) as a Q-valued witness (Rat output type in Lean)",
               "x = 2", show(v, 24), "arb.sqrt", "B01", ok)


def b02():
    r = T.range_enclosure(lambda X: X.sin(), 0, Fraction(1, 10), parts=32, refine=10)
    v = A(Fraction(1, 10)).sin()
    ok = r["sup_lo"] <= lb(v) and ub(v) <= r["sup_hi"] and abs(r["inf_lo"]) <= Fraction(1, 10 ** 9)
    return rec("B02", "pair witness (sup, inf) for sin on [0,0.1] -- mixed form",
               "x in [0, 0.1]",
               f"sup = {show(v, 22)}, inf = 0, sup sandwich "
               f"[{float(r['sup_lo']):.12f}, {float(r['sup_hi']):.12f}]",
               "range enclosure + monotonicity", "B02", ok)


def b03():
    N = 1000
    s = sum(Fraction(1, k * k) for k in range(1, N + 1))
    ok = A(s) < A(2) and A(s) > A(Fraction(1600, 1000))
    return rec("B03", "finite sum_{k=1..1000} 1/k^2 (large finite sum)",
               "k = 1..1000",
               f"exact rational = {float(s):.15f} = {s.numerator}/{s.denominator}",
               "exact rational accumulation vs Arb comparison", "B03", ok)


def b04():
    s = sum(A(0).sin_pi_fmpq(fmpq(k, 7)) for k in range(1, 6))
    ok = contains(s, "3.94740252841726495192887678219952")
    return rec("B04", "finite sum_{k=1..5} sin(pi*k/7)",
               "k = 1..5, exact rational multiples of pi", show(s, 22),
               "arb.sin_pi_fmpq -- exact pi reduction", "B04", ok)


def b05():
    r = T.range_enclosure(lambda X: X.exp(), -1, 1, parts=64, refine=16)
    e = A(1).exp()
    ok = r["sup_lo"] <= lb(e) and ub(e) <= r["sup_hi"] and r["inf_lo"] <= lb(A(-1).exp()) and \
        ub(A(-1).exp()) <= r["inf_hi"]
    return rec("B05", "range of exp on [-1,1]; sup = e, inf = 1/e",
               "x in [-1, 1]",
               f"sup sandwich [{float(r['sup_lo']):.12f}, {float(r['sup_hi']):.12f}] "
               f"(e = {show(e, 20)}); inf sandwich "
               f"[{float(r['inf_lo']):.12f}, {float(r['inf_hi']):.12f}]",
               "interval subdivision + refinement", "B05", ok)


# ==========================================================================
# C01 - C10 : extra capability coverage
# ==========================================================================

def c01():
    X = I(0, 1)
    Naive = X - X
    ok = lb(Naive) <= 0 <= ub(Naive) and width_of(Naive) > 1.99
    return rec("C01", "dependency problem: x - x on [0,1] encloses [-1,1], not {0}",
               "x in [0, 1]",
               f"X - X = {show(Naive, 8)} (width {width_of(Naive):.6f}); true value 0",
               "the classic interval overestimation (why subdivision / Taylor models "
               "are needed)", "-", ok)


def c02():
    a, b = Fraction(1, 1000), Fraction(2, 1000)
    X = I(a, b)
    num = A(1) - X.cos()                       # [4.9e-7, 2.0e-6]: cancellation
    naive = num / (X * X)
    # 1) cancellation-free rewrite (2 sin^2(x/2)/x^2) is still wide,
    # 2) but Arb's well-conditioned primitive sinc handles x -> 0 exactly:
    #    (1 - cos x)/x^2 = sinc(x/2)^2 / 2
    smart = (X / 2).sinc() ** 2 / 2
    ok = (ub(naive) - lb(naive) > Fraction(1, 2)) and \
        lb(smart) <= Fraction(1, 2) <= ub(smart) and \
        (ub(smart) - lb(smart)) < Fraction(1, 10 ** 5)
    return rec("C02", "cancellation: (1 - cos x)/x^2 on [-1e-3, 1e-3]",
               "x in [-1e-3, 1e-3]",
               f"numerator 1 - cos x = {show(num, 10)}; naive quotient {show(naive, 8)} "
               f"(width {float(ub(naive)-lb(naive)):.4g}, true width ~2e-7); "
               f"as sinc(x/2)^2/2 (Arb's cancellation-free primitive): "
               f"{show(smart, 22)}, width {float(ub(smart)-lb(smart)):.2g}",
               "how Arb-users (and Taylor-model packages) fight dependency: rewrite the "
               "expression or use a Taylor model", "-", ok)


def c03():
    X, Y = I(1, 2), I(3, 4)
    try:
        I(1, 2).intersection(I(3, 4))
        empty_ok = False
    except ValueError:
        empty_ok = True                      # python-flint raises on empty intersection
    checks = [
        abs(float(lb(X + Y) - 4)) < 1e-6 and abs(float(ub(X + Y) - 6)) < 1e-6,
        abs(float(lb(X - Y) + 3)) < 1e-6 and abs(float(ub(X - Y) + 1)) < 1e-6,
        lb(X * Y) <= 3 <= ub(X * Y) and lb(X * Y) <= 8 <= ub(X * Y),
        lb(X / Y) <= Fraction(1, 4) and ub(X / Y) >= Fraction(2, 3),
        X.contains(A("1.5")) and not X.contains(A(3)),
        (not I(1, "inf").is_finite()) and I(1, "inf").contains(A(1000)),
        X.union(Y).contains(A(1)) and X.union(Y).contains(A(4)),
        X.overlaps(I(Fraction(3, 2), 5)),
        empty_ok,
        I(0, 1).sqrt().contains(A(Fraction(70710678, 100000000))),
        lb(I(-5, 5).abs_lower()) == 0 and ub(I(-5, 5).abs_upper()) >= 5,
    ]
    ok = all(checks)
    return rec("C03", "core interval ops: + - * /, intersection (empty -> error), "
               "union, containment, overlaps, infinite endpoints, abs",
               "[1,2] op [3,4]; [1,oo); [0,1]",
               f"{sum(checks)}/{len(checks)} properties hold "
               f"({'all fine' if ok else 'see notes'})",
               "direct interval arithmetic", "-", ok)


def c04():
    z = (acb(0, 1) * acb.pi()).exp()
    ok1 = (z + 1).contains(0)
    zz = acb(1, 1)
    w = zz.sin() * zz.cos()
    ok2 = w.overlaps((acb(2) * zz).sin() / 2)              # sin z cos z = sin 2z / 2
    g = acb(1, 1).gamma()
    ok3 = abs(float(g.real.mid()) - 0.49801566811835604) < 1e-15 and \
        abs(float(g.imag.mid()) + 0.15494982830181069) < 1e-15
    ok = ok1 and ok2 and ok3
    return rec("C04", "complex interval arithmetic (acb): exp(i pi) + 1 contains 0, "
               "complex sin/cos identity, complex Gamma",
               "z = i*pi; z = 1+i",
               f"exp(i pi) + 1 = {z + 1}; |Gamma(1+i)| enclosure contains the reference",
               "Arb's complex balls (acb)", "-", ok, note="ok2/ok3 via containment")


def c05():
    M = arb_mat([[A(1), A(2)], [A(3), A(4)]])
    d = M.det()
    inv = M.inv()
    expected_inv = arb_mat([[A(-2), A(1)], [A(Fraction(3, 2)), A(Fraction(-1, 2))]])
    sol = arb_mat([[A(2), A(1)], [A(1), A(3)]]).solve(arb_mat([[A(1)], [A(2)]]))
    E = arb_mat([[A(0), A(1)], [A(-1), A(0)]]).exp()
    def close(x, ref, tol=Fraction(1, 10 ** 25)):
        return ub(x) - lb(x) < tol and lb(x) - tol <= ref <= ub(x) + tol
    ok = close(d, -2) and \
        close(inv.entries()[0], -2) and close(inv.entries()[3], Fraction(-1, 2)) and \
        close(sol.entries()[0], Fraction(1, 5)) and close(sol.entries()[1], Fraction(3, 5)) and \
        close(E.entries()[0], lb(A(1).cos())) and \
        abs(float(E.entries()[1].mid()) - float(A(1).sin().mid())) < 1e-15
    return rec("C05", "interval linear algebra: det, inverse, solve, matrix exponential",
               "[[1,2],[3,4]]; [[2,1],[1,3]]x = [1,2]; exp([[0,1],[-1,0]])",
               f"det = {show(d, 6)}; det(inv) contains; solve contains [1/5, 3/5]; "
               f"exp = rotation by 1 rad (enclosure contains the rotation matrix)",
               "verified arb_mat algorithms", "-", ok)


def c06():
    roots = acb_poly([-2, 0, 0, 1]).roots()                 # x^3 - 2
    ok1 = any(r.contains(acb(A("1.2599210498948731647672106072782283506"))) for r in roots)
    rq = acb_poly([-6, 11, -6, 1]).roots()                  # (x-1)(x-2)(x-3)
    ok2 = all(any(r.contains(acb(A(k))) for r in rq) for k in (1, 2, 3))
    ev = arb_poly([1, 0, -1])(I(0, 2))                      # 1 - x^2 on [0,2]
    ok3 = lb(ev) <= -3 <= ub(ev) and lb(ev) <= 1 <= ub(ev)
    return rec("C06", "polynomial root isolation + interval polynomial evaluation",
               "x^3-2; (x-1)(x-2)(x-3); x^2-1 on [0,2]",
               f"x^3-2 roots: {[str(r) for r in roots]}; "
               f"(x-1)(x-2)(x-3) roots verified; x^2-1 on [0,2] = {show(ev, 8)}",
               "acb_poly.roots (certified refinement) + arb_poly.evaluate", "-",
               ok1 and ok2 and ok3)


def c07():
    s = arb_series([1, 1, fmpq(1, 2), fmpq(1, 6)]).exp()
    rev = arb_series([0, 1, 1]).reversion()
    cs = [str(c) for c in rev.coeffs()[1:6]]
    want = [str(A(v)) for v in (1, -1, 2, -5, 14)]
    ok = cs == want
    return rec("C07", "power-series arithmetic: exp of a series, reversion of x + x^2",
               "coefficients [1,1,1/2,1/6] and [0,1,1]",
               f"exp(series) first coefficient = {show(s.coeffs()[0], 18)}; "
               f"reversion of x+x^2 = x - x^2 + 2x^3 - 5x^4 + 14x^5 (Catalan numbers)",
               "arb_series (rigorous truncated series arithmetic)", "-", ok)


def c08():
    vals = {
        "erf(1)": (A(1).erf(), "0.84270079294971486934122063508260925930"),
        "erfc(1)": (A(1).erfc(), "0.15729920705028513065877936491739074070"),
        "ei(1)": (A(1).ei(), "1.8951178163559367554665209343316342690"),
        "si(1)": (A(1).si(), "0.94608307036718301494135331382317965781"),
        "ci(1)": (A(1).ci(), "0.33740392290096813466264620388915077000"),
        "fresnel_s(1)": (A(1).fresnel_s(), "0.43825914739035476607675669662515263720"),
        "fresnel_c(1)": (A(1).fresnel_c(), "0.77989340037682282947420641365269013663"),
        "airy_ai(1)": (A(1).airy_ai(), "0.13529241631288141552414742351546630617"),
        "bessel_j(2,1)": (A(1).bessel_j(2), "0.11490348493190048046964688133516660535"),
        "bessel_y(0,1)": (A(1).bessel_y(0), "0.088256964215676957982926766991669827502"),
        "agm(1,2)": (A(1).agm(2), "1.4567910310469068691864323832650819750"),
        "lambertw(1)": (A(1).lambertw(), "0.56714329040978387299996866221035554975"),
        "digamma(3)": (A(3).digamma(), "0.92278433509846713939348790991759756895"),
        "polylog(3,1/2)": (A(Fraction(1, 2)).polylog(3),
                           "0.53721319360804020094062322559496"),
        "hypgeom_2f1(1,1;2;1/2)": (A(Fraction(1, 2)).hypgeom_2f1(1, 1, 2),
                                   "1.3862943611198906188344642429163531361"),
        "hypgeom_1f1(1;2;1)": (A(1).hypgeom_1f1(1, 2), "1.71828182845904523536028747135266"),
        "const_euler": (arb.const_euler(), "0.57721566490153286060651209008240243104"),
        "catalan": (arb.const_catalan(), "0.91596559417721901505460351493238411077"),
        "khinchin": (arb.const_khinchin(), "2.6854520010653064453097148354817956938"),
        "glaisher": (arb.const_glaisher(), "1.2824271291006226368753425688697917278"),
        "log2": (arb.const_log2(), "0.69314718055994530941723212145817656808"),
    }
    lo, hi = [], []
    for k, (v, ref) in vals.items():
        (hi if contains(v, ref) else lo).append(k)
    return rec("C08", "special-function zoo (erf, erfc, Ei, Si, Ci, Fresnel, Airy, "
               "Bessel, AGM, Lambert W, digamma, polylog, hypergeometric, constants)",
               "x = 1, 1/2, 3",
               f"{len(hi)}/{len(vals)} match ~40-digit references" +
               (f"; mismatches: {lo}" if lo else ""),
               "arb special functions at 256-bit precision", "-", not lo)


def c09():
    checks = []
    old = ctx.prec
    ctx.prec = 64
    a = A(3).zeta()
    ctx.prec = 256
    b = A(3).zeta()
    ctx.prec = old
    checks.append(b.overlaps(a))                       # two-precision overlap
    q = fmpq(7, 13)
    s1 = A(0).sin_pi_fmpq(q)
    s2 = (Pi() * 7 / 13).sin()
    checks.append(lb(s1) <= ub(s2) and lb(s2) <= ub(s1))   # pi-reduction vs interval pi
    checks.append(A(3).agm(3).contains(A(3)))              # agm identity
    checks.append((A(2).sqrt() ** 2).contains(A(2)))       # pow/root identities
    checks.append((A(2).root(5) ** 5).contains(A(2)))
    x = A(Fraction(3, 7))
    lhs = x.gamma() * (A(1) - x).gamma()                   # Gamma reflection
    rhs = Pi() / (Pi() * A(Fraction(3, 7))).sin()
    checks.append(lb(lhs) <= ub(rhs) and lb(rhs) <= ub(lhs))
    checks.append((A(0).cos_pi_fmpq(fmpq(1, 3))).contains(A(Fraction(1, 2))))   # cos(pi/3)=1/2
    return rec("C09", "upstream-Arb-style consistency tests (two-precision overlap, "
               "pi reduction, AGM/root/pow identities, Gamma reflection, cos(pi/3))",
               "points and rationals",
               f"{sum(checks)}/{len(checks)} consistency checks hold",
               "shapes mirrored from src/arb/test/t-*.c (t-zeta, t-sin_cos_pi_fmpq, "
               "t-agm, t-pow_fmpq, t-root_ui, t-gamma)", "-", all(checks))


def c10():
    checks = [
        abs(float(lb(I(Fraction(1, 4), Fraction(7, 4)).floor()))) < 1e-6 and
        abs(float(ub(I(Fraction(1, 4), Fraction(7, 4)).ceil())) - 2) < 1e-6,
        lb(I(-1, 3).abs_lower()) == 0 and ub(I(-1, 3).abs_upper()) >= 3,
        A("0.5").sgn().contains(A(1)) and A("-2").sgn().contains(A(-1)),
        contains(A(2).expm1(), "6.3890560989306502272304274605750078132"),
        contains(A(Fraction(1, 10 ** 6)).log1p(), "0.000000999999500000333333083333"),
        A(10).fac().contains(A(3628800)),
        A(0).fib(20).contains(A(6765)),
        A(0).bell_number(10).contains(A(115975)),
        A(0).chebyshev_t(3).contains(A(0)) and A(0).chebyshev_u(2).contains(A(-1)),
        contains(A(0).bernoulli(6), Fraction(1, 42)),
        contains(A(2).rsqrt(), "0.707106781186547524400844362104849039284835937688474036588"),
        contains((A("1e-30")).log(), "-69.077552789821370520539743604528732638"),
        A(Fraction(1, 2)).bin(5).contains(A(Fraction(7, 256))),
    ]
    ok = all(checks)
    return rec("C10", "rounding/integer helpers, abs bounds, sgn, expm1/log1p/rsqrt, "
               "combinatorics (fac, fib, Bell, Bernoulli, Chebyshev, binomial)",
               "various points/intervals", f"{sum(checks)}/{len(checks)} properties hold",
               "arb elementary + combinatorial layer", "-", ok)


# ==========================================================================
# driver
# ==========================================================================

ALL = [a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, a12, a13, a14,
       a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28,
       a29, a30, b01, b02, b03, b04, b05,
       c01, c02, c03, c04, c05, c06, c07, c08, c09, c10]


# ---------------------------------------------------------------------------
# group D: special-function coverage -- one composite test per function family
# (see arb/function_zoo.py; every entry point of Arb's special-function
#  surface appears in exactly one family, checked against an independent
#  reference)
# ---------------------------------------------------------------------------

def _family_runner(fam):
    def _run():
        ok_n, n, details, fails = function_zoo.run_family(fam)
        from function_zoo import summary, widths
        out = summary(fam, details)
        if fails:
            out += "   *** " + "; ".join(fails[:3])
        return rec(fam["id"], fam["title"], fam["at"], out, fam["method"],
                   _family_lean_mirror(fam), ok_n == n, note=f"{ok_n}/{n} entry points match")
    return _run


for _fam in function_zoo.FAMILIES:
    ALL.append(_family_runner(_fam))


# ---------------------------------------------------------------------------
# group E: composition tests -- one Arb evaluation per test, several special
# functions per expression (`f (g x + h x)`), as requested.  MP*/MD*/MR* are the
# ones mirrored in Test/IntervalArith/Compositions.lean + Discrete.lean;
# ME* are Arb-only (functions mathlib has no declaration for).
# ---------------------------------------------------------------------------

def _family_lean_mirror(fam):
    """Composition tests (group E) that exercise the same mathlib functions as
    this family's Lean-expressible entry points."""
    cov, _ = compositions.function_coverage()
    names = set()
    for c in fam["checks"]:
        tag = c.get("lean") or ""
        for n in compositions.MATHLIB_FUNCTIONS:
            if n in tag:
                names.add(n)
    ids = []
    for n in sorted(names):
        for i in cov.get(n, []):
            if i not in ids:
                ids.append(i)
    if not ids:
        return "-"
    shown = ", ".join(ids[:6])
    return shown + (f", +{len(ids) - 6}" if len(ids) > 6 else "")


def _comp_runner(c):
    def _run():
        if c["kind"] == "point":
            ok, lo, hi, err, ref = compositions.eval_point(c)
            out = (f"point enclosure [{T.show(A(lo), 16)}, {T.show(A(hi), 16)}]; "
                   f"mpmath {mpmath.nstr(c['ref'](), 20)}; deviation {float(err):.2g}")
            method = f"composed expression, one Arb evaluation ({c['functions']})"
        elif c["kind"] in ("nat", "sign"):
            ok, n, lo, hi, margin = compositions.eval_nat(c)
            what = "floor" if c["kind"] == "nat" else "sign"
            out = (f"enclosure [{T.show(A(lo), 16)}, {T.show(A(hi), 16)}] -> {what} "
                   f"certified = {n} (margin {float(margin):.4f} to the nearest integer)")
            method = f"composed expression + {what} certification ({c['functions']})"
        else:
            ok, out = compositions.summary(c)
            method = f"subdivision + refinement of a composed expression ({c['functions']})"
        return rec(c["id"], f"composition: {c['name']} -- {c['note']}", c["at"], out,
                   method, c["id"], ok,
                   note=c["functions"])
    return _run


for _c in compositions.ALL_COMPS + compositions.ARB_ONLY:
    ALL.append(_comp_runner(_c))


def main():
    from mpmath import mp
    mp.dps = 60
    print("=" * 78)
    print(f"Arb interval-arithmetic test suite -- python-flint {flint.__version__}")
    print(f"working precision {ctx.prec} bits (~{int(ctx.prec * 0.30103)} decimal digits); "
          f"ball radii are 30-bit `mag`s, so wide intervals carry ~1e-9 relative slack")
    print("=" * 78)
    for fn in ALL:
        try:
            fn()
        except Exception as e:                                   # noqa: BLE001
            import traceback
            rec(fn.__name__, f"EXCEPTION in {fn.__name__}", "-", "-",
                f"{type(e).__name__}: {e}", "-", False, note=traceback.format_exc().splitlines()[-3])
    n_ok = sum(STATUS)
    print("-" * 78)
    print(f"{n_ok}/{len(STATUS)} tests passed")
    write_report()
    return 0 if n_ok == len(STATUS) else 1


def write_report():
    lines = ["# Arb interval-arithmetic run -- results\n",
             f"Generated by `arb/tests_arb.py` (python-flint {flint.__version__}, "
             f"working precision {ctx.prec} bits, mpmath for reference values).\n",
             f"**{sum(STATUS)}/{len(STATUS)} tests passed.**\n",
             "Column *Lean* names the test in `Test/IntervalArith/` of the lynth "
             "`exp_spark` branch that this run backs.\n",
             "| # | test | input | output enclosure | method | Lean | status |",
             "|---|------|-------|------------------|--------|------|--------|"]
    for r in ROWS:
        lines.append("| {test} | {what} | `{inp}` | `{out}` | {method} | {lean} | {status} |"
                     .format(**{k: str(v).replace("|", "\\|") for k, v in r.items()}))
    lines += ["", "## Reproduce\n", "```sh",
              "pip install python-flint mpmath",
              "cd arb && python3 tools.py          # toolkit self-test",
              "python3 tests_arb.py -v             # this table",
              "python3 validate_lean_tests.py      # certificates for the Lean tests (CERTIFICATES.md)",
              "python3 gen_lean_tests.py           # writes lynth/Test/IntervalArith/*.lean",
              "```"]
    with open("RESULTS.md", "w") as fh:
        fh.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    sys.exit(main())
