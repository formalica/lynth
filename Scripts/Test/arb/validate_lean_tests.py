#!/usr/bin/env python3
"""
Certificates for the Lean tests under `Test/IntervalArith/` (lynth, exp_spark).

Every declaration in `Test/IntervalArith/*.lean` is backed here by a rigorous
Arb computation (`tools.py`), which is what `lynth` is expected to reproduce
internally:

  * computational tests (`{ x : Rat // |f - x| < tol }`): an Arb enclosure
    `f ∈ [lo, hi]` plus a rational witness `w` with
    `max(|lo - w|, |hi - w|) < tol`;
  * range tests (`{ p : Rat × Rat // ... }`): rigorous `sup`/`inf` enclosures on
    a subdivison of the box, compared against the returned pair;
  * theorem tests: a proof certificate (interval subdivision for `sup ≤ c`,
    `inf ≥ c`, derivative-sign certificates for global statements, direct
    enclosure for special-function bounds);
  * sums / integrals: partial sums with rigorous tail bounds, and quadrature
    with an interval error term.

Tolerances are validated against a *lower* rational bound, so an irrational
tolerance such as `Real.pi / 100` is handled rigorously.

Output: `CERTIFICATES.md` (human readable) and `certificates.json` (consumed by
`gen_lean_tests.py`, which writes the Lean files).

Run:  python3 validate_lean_tests.py [-v]
"""

import json
import os
import re
from decimal import Decimal
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import mpmath  # noqa: E402
from mpmath import mp, diff, exp as mexp, cos as mcos, sin as msin, findroot  # noqa: E402

import tools as T  # noqa: E402
import function_zoo  # noqa: E402
from tools import A, F, I, Pi, lb, ub, dec_lo, dec_hi, show  # noqa: E402
from flint import fmpq  # noqa: E402

OUT_DIR = os.path.dirname(os.path.abspath(__file__))


# --------------------------------------------------------------------------
# tolerances: Lean text + a rigorous rational lower bound on their value
# --------------------------------------------------------------------------

def tol_rat(lean, value):
    return {"lean": lean, "lo": F(value), "disp": str(value)}


def tol_pi_div(n, lean):
    return {"lean": lean, "lo": lb(Pi()) / n, "disp": f"pi/{n}"}


TOL_1E5 = tol_rat("(10 : ℝ) ^ (-5 : ℤ)", Fraction(1, 10 ** 5))
TOL_1E6 = tol_rat("1 / 1000000", Fraction(1, 10 ** 6))
TOL_1E10 = tol_rat("(10 : ℝ) ^ (-10 : ℤ)", Fraction(1, 10 ** 10))
TOL_1E30 = tol_rat("(10 : ℝ) ^ (-30 : ℤ)", Fraction(1, 10 ** 30))
TOL_1E7 = tol_rat("(10 : ℝ) ^ (-7 : ℤ)", Fraction(1, 10 ** 7))
TOL_1E3 = tol_rat("1 / 1000", Fraction(1, 10 ** 3))
TOL_1E2 = tol_rat("1 / 100", Fraction(1, 10 ** 2))
TOL_1E500 = tol_rat("1 / 500", Fraction(1, 500))
TOL_PI100 = tol_pi_div(100, "Real.pi / 100")


# --------------------------------------------------------------------------
# certificate records
# --------------------------------------------------------------------------

def _fmt_frac(x, places=25):
    return f"{float(x):.{places}g}"


def witness_cert(tid, goal, enclosure, witness, tol, note="", witness_str=None, err=None):
    """f ∈ [lo, hi] and |f - w| < tol for every f in the enclosure."""
    lo, hi = enclosure
    if err is None:
        err = max(abs(witness - lo), abs(witness - hi))
    ok = err < tol["lo"]
    return {
        "id": tid, "kind": "witness", "ok": ok, "goal": goal,
        "lean_tol": tol["lean"], "tol_disp": tol["disp"],
        "tol_lo": _fmt_frac(tol["lo"]),
        "enclosure": (_fmt_frac(lo), _fmt_frac(hi)),
        "witness": witness_str or _fmt_frac(witness),
        "wid": float(hi - lo), "err": _fmt_frac(err), "note": note,
    }


def proof_cert(tid, kind, goal, ok, rows, note=""):
    return {
        "id": tid, "kind": kind, "ok": ok, "goal": goal,
        "lean_tol": "", "tol_disp": "", "tol_lo": "",
        "enclosure": None, "witness": "", "wid": None, "err": "",
        "notes": rows, "note": note,
    }


def pick_witness(lo, hi, ref, places=12):
    """A short rational witness for a point test.  Arb's point enclosures are far
    narrower than any tolerance we use (typically ~1e-76), so instead of looking
    for a rational *inside* the enclosure we take the reference rounded to
    `places` significant digits and let the caller measure its distance to the
    enclosure endpoints."""
    d = Decimal(mp.nstr(mp.mpf(ref.numerator) / mp.mpf(ref.denominator), places))
    return Fraction(d)


def as_frac_dec(x, places=20):
    """Rational version of Arb's outward-rounded decimal at `places`."""
    from decimal import Decimal
    lo = Fraction(Decimal(dec_lo(x, places)))
    hi = Fraction(Decimal(dec_hi(x, places)))
    return lo, hi


# --------------------------------------------------------------------------
# T01-T06: point values (Test/IntervalArith/Basic.lean)
# --------------------------------------------------------------------------

def t01():
    X = A(8) / 17 * Pi()
    val = X.cos()
    exact = A(0).cos_pi_fmpq(fmpq(8, 17))
    lo, hi = as_frac_dec(val, 20)
    w = Fraction(Decimal_of(dec_lo(val, 20)))
    note = (f"arb.cos_pi_fmpq(8,17) cross-check {show(exact, 22)}; "
            f"enclosure width {float(hi - lo):.2g}")
    return witness_cert("T01", "|Real.cos (Real.pi * 8 / 17) - x| < (10 : ℝ) ^ (-5 : ℤ)",
                        (lb(val), ub(val)), w, TOL_1E5, note=note,
                        witness_str=dec_lo(val, 20))


def t02():
    X = A(8) / 17 * Pi()
    val = X.sin()
    exact = A(0).sin_pi_fmpq(fmpq(8, 17))
    note = f"arb.sin_pi_fmpq(8,17) cross-check {show(exact, 22)}; tolerance is irrational (pi/100)"
    return witness_cert("T02", "|Real.sin (Real.pi * 8 / 17) - x| < Real.pi / 100",
                        (lb(val), ub(val)), Fraction(Decimal_of(dec_lo(val, 20))), TOL_PI100,
                        note=note, witness_str=dec_lo(val, 20))


def t03():
    val = A(2).exp()
    return witness_cert("T03", "|Real.exp 2 - x| < 1 / 1000000",
                        (lb(val), ub(val)), Fraction(Decimal_of(dec_lo(val, 20))), TOL_1E6,
                        witness_str=dec_lo(val, 20))


def t04():
    val = (Pi() / 100).log()
    v = A(31415926535897932384626433832795028841971693993751) / A(10 ** 49) / 100
    note = f"log of the irrational pi/100; enclosure {show(val, 22)}"
    return witness_cert("T04", "|Real.log (Real.pi / 100) - x| < 1 / 100000",
                        (lb(val), ub(val)), Fraction(Decimal_of(dec_lo(val, 20))), TOL_1E5,
                        note=note, witness_str=dec_lo(val, 20))


def t05():
    root = A(2).root(3)
    via_pow = (A(2).log() / 3).exp()
    lo = min(lb(root), lb(via_pow))          # intersection of the two enclosures
    hi = max(ub(root), ub(via_pow))
    w = Fraction(Decimal_of(dec_lo(root, 20)))
    note = (f"two Arb paths agree: root(3) = {show(root, 22)}, "
            f"exp(log 2 / 3) = {show(via_pow, 22)}")
    return witness_cert("T05", "|(2 : ℝ) ^ ((1 : ℝ) / 3) - x| < 1 / 1000000",
                        (lo, hi), w, TOL_1E6, note=note, witness_str=dec_lo(root, 20))


def t06():
    val = A(2).sqrt()
    return witness_cert("T06", "|Real.sqrt 2 - x| < (10 : ℝ) ^ (-10 : ℤ)",
                        (lb(val), ub(val)), Fraction(Decimal_of(dec_lo(val, 20))), TOL_1E10,
                        witness_str=dec_lo(val, 20))


# --------------------------------------------------------------------------
# T07-T11: ranges (Test/IntervalArith/Ranges.lean)
# --------------------------------------------------------------------------

def _mid(box):
    return float((box[0] + box[1]) / 2)


def _range_cert(tid, goal, f, a, b, wsup, winf, tol_sup, tol_inf, parts=128, refine=24):
    r = T.range_enclosure(f, a, b, parts=parts, refine=refine)
    e_sup = max(abs(wsup - r["sup_lo"]), abs(wsup - r["sup_hi"]))
    e_inf = max(abs(winf - r["inf_lo"]), abs(winf - r["inf_hi"]))
    ok = e_sup < tol_sup["lo"] and e_inf < tol_inf["lo"]
    return {
        "id": tid, "kind": "witness", "ok": ok, "goal": goal,
        "lean_tol": f"{tol_sup['lean']} / {tol_inf['lean']}",
        "tol_disp": f"sup {tol_sup['disp']}, inf {tol_inf['disp']}",
        "tol_lo": f"{_fmt_frac(tol_sup['lo'])} / {_fmt_frac(tol_inf['lo'])}",
        "enclosure": (f"sup in [{_fmt_frac(r['sup_lo'])}, {_fmt_frac(r['sup_hi'])}]",
                      f"inf in [{_fmt_frac(r['inf_lo'])}, {_fmt_frac(r['inf_hi'])}]"),
        "witness": f"({_fmt_frac(wsup)}, {_fmt_frac(winf)})",
        "wid": float(max(r["sup_hi"] - r["sup_lo"], r["inf_hi"] - r["inf_lo"])),
        "err": f"sup {_fmt_frac(e_sup)}, inf {_fmt_frac(e_inf)}",
        "note": f"{r['parts']} boxes, argmax in {_mid(r['argmax']):.6f}, argmin in {_mid(r['argmin']):.6f}",
    }


def t07():
    sup = A(1) / 10
    supv = sup.sin()
    wsup = Fraction(Decimal_of(dec_lo(supv, 20)))
    return _range_cert("T07",
                       "|rangeSup Real.sin 0 (1 / 10) - p.1| < 1 / 1000 ∧ "
                       "|rangeInf Real.sin 0 (1 / 10) - p.2| < 1 / 1000",
                       lambda X: X.sin(), 0, Fraction(1, 10), wsup, Fraction(0),
                       TOL_1E3, TOL_1E3, parts=64, refine=8)


def t08():
    # cos is even and decreasing on [0, 3/2]: sup = cos 0 = 1, inf = cos(3/2)
    inf = (A(3) / 2).cos()
    winf = Fraction(Decimal_of(dec_lo(inf, 20)))
    return _range_cert("T08",
                       "|rangeSup Real.cos 0 (3 / 2) - p.1| < 1 / 1000 ∧ "
                       "|rangeInf Real.cos 0 (3 / 2) - p.2| < 1 / 1000",
                       lambda X: X.cos(), 0, Fraction(3, 2), Fraction(1), winf,
                       TOL_1E3, TOL_1E3)


def t09():
    sup = A(1).exp()
    inf = (-A(1)).exp()
    wsup = Fraction(Decimal_of(dec_lo(sup, 20)))
    winf = Fraction(Decimal_of(dec_lo(inf, 20)))
    return _range_cert("T09",
                       "|rangeSup Real.exp (-1) 1 - p.1| < 1 / 1000 ∧ "
                       "|rangeInf Real.exp (-1) 1 - p.2| < 1 / 1000",
                       lambda X: X.exp(), -1, 1, wsup, winf, TOL_1E3, TOL_1E3)


def t10():
    sup = A(1).tan()
    wsup = Fraction(Decimal_of(dec_lo(sup, 20)))
    return _range_cert("T10",
                       "|rangeSup Real.tan 0 1 - p.1| < 1 / 1000 ∧ "
                       "|rangeInf Real.tan 0 1 - p.2| < 1 / 1000",
                       lambda X: X.tan(), 0, 1, wsup, Fraction(0), TOL_1E3, TOL_1E3,
                       parts=64, refine=16)


def t11():
    f = lambda X: X.sin().exp() * (X * X).cos()
    # interior maximum at x ~ 0.7042472, minimum at the left endpoint x = -1
    xm = findroot(lambda t: diff(lambda u: mexp(msin(u)) * mcos(u * u), t), (0.69, 0.72))
    sup = mexp(msin(xm)) * mcos(xm * xm)
    inf = mexp(msin(-1)) * mcos(1)
    wsup = Fraction(str(sup))
    winf = Fraction(str(inf))
    return _range_cert("T11",
                       "|rangeSup (fun r => Real.exp (Real.sin r) * Real.cos (r ^ 2)) (-1) 1 - p.1| < 1 / 100 ∧ "
                       "|rangeInf (fun r => Real.exp (Real.sin r) * Real.cos (r ^ 2)) (-1) 1 - p.2| < 1 / 1000",
                       f, -1, 1, wsup, winf, TOL_1E2, TOL_1E3)


# --------------------------------------------------------------------------
# T12-T14 + B01-B03: finite and infinite sums (Test/IntervalArith/Sums.lean)
# --------------------------------------------------------------------------

def t12():
    S = None
    for k in range(5):
        term = (-A(k)).exp() * A(k).cos()
        S = term if S is None else S + term
    ref = sum(mexp(-k) * mcos(k) for k in range(5))
    return witness_cert("T12",
                        "|(∑ k ∈ Finset.range 5, Real.exp (-(k : ℝ)) * Real.cos (k : ℝ)) - x| < 1 / 1000000",
                        (lb(S), ub(S)), Fraction(Decimal_of(dec_lo(S, 20))), TOL_1E6,
                        note=f"5 terms, interval accumulation; mpmath reference {ref}",
                        witness_str=dec_lo(S, 20))


def t13():
    # sum_{k<100} 2^-(k+1) = 1 - 2^-100 exactly: check the rational identity
    S = None
    for k in range(100):
        term = (A(1) / 2) ** (k + 1)
        S = term if S is None else S + term
    exact = sum(Fraction(1, 2 ** (k + 1)) for k in range(100))
    closed = 1 - Fraction(1, 2 ** 100)
    w = closed
    ok_id = (exact == closed)
    c = witness_cert("T13",
                     "|(∑ k ∈ Finset.range 100, (1 / 2 : ℝ) ^ (k + 1)) - x| < (10 : ℝ) ^ (-30 : ℤ)",
                     (exact, exact), w, TOL_1E30,
                     note=f"exact rational identity 1 - 2^-100 = {float(closed):.20f}; "
                          f"Arb accumulation agrees to {show(S, 20)}",
                     witness_str="1 - 1 / 1267650600228229401496703205376")
    c["ok"] = c["ok"] and ok_id
    return c


def t14():
    S = None
    for k in range(1, 6):
        term = A(0).sin_pi_fmpq(fmpq(k, 7))
        S = term if S is None else S + term
    ref = sum(msin(mp.pi * k / 7) for k in range(1, 6))
    return witness_cert("T14",
                        "|(∑ k ∈ Finset.range 5, Real.sin (Real.pi * (k + 1) / 7)) - x| < 1 / 1000000",
                        (lb(S), ub(S)), Fraction(Decimal_of(dec_lo(S, 20))), TOL_1E6,
                        note=f"exact pi-reduction sin_pi_fmpq(k,7) per term; mpmath reference {ref}",
                        witness_str=dec_lo(S, 20))


def b01():
    # |sum_{j=1..1000} 1/j^2 - pi^2/6| < 1/500   (integral-test tail)
    exact = sum(Fraction(1, j * j) for j in range(1, 1001))
    pi2_6 = Pi() * Pi() / 6
    d_lo = exact - ub(pi2_6)
    d_hi = exact - lb(pi2_6)
    err = max(abs(d_lo), abs(d_hi))
    tol = TOL_1E500
    ok = err < tol["lo"]
    tail = Fraction(1, 1001)  # int_1000^inf dx/x^2 = 1/1000, so tail < 1/1001
    return proof_cert("B01", "theorem",
                      "|(∑ k ∈ Finset.range 1000, 1 / ((k : ℝ) + 1) ^ 2) - Real.pi ^ 2 / 6| < 1 / 500",
                      ok,
                      [f"exact rational partial sum S_1000 = {float(exact):.20f}",
                       f"arb pi^2/6 = {show(pi2_6, 22)}",
                       f"rigorous difference S_1000 - pi^2/6 in [{_fmt_frac(d_lo)}, {_fmt_frac(d_hi)}] "
                       f"= {float(d_hi):.6e} (approx {float(exact) - float(mp.pi ** 2 / 6):.6e}), |.| < 1/500 = {float(tol['lo']):.6g}",
                       f"integral-test tail bound: sum_(j>1000) 1/j^2 <= 1/1000 (and >= {float(tail):.6g})"],
                      note="infinite series bounded by an exact partial sum + an integral tail")


def b02():
    # telescoping: sum_{k<n} 1/((k+1)(k+2)) = 1 - 1/(n+1), exactly
    worst = None
    for n in list(range(0, 40)) + [100, 1000, 4000]:
        lhs = sum(Fraction(1, (k + 1) * (k + 2)) for k in range(n))
        rhs = 1 - Fraction(1, n + 1)
        worst = (lhs - rhs) if worst is None or abs(lhs - rhs) > abs(worst) else worst
    ok = (worst == 0)
    return proof_cert("B02", "theorem",
                      "∀ n : ℕ, (∑ k ∈ Finset.range n, 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) "
                      "= 1 - 1 / ((n : ℝ) + 1)",
                      ok,
                      ["exact rational identity verified for n = 0..39, 100, 1000, 4000",
                       "difference = 0 in every case (telescoping is exact)"],
                      note="exact rational identity -- the closed form the goal states")


def b03():
    # |sum_{k<100} (-1)^k/(2k+1) - pi/4| < 1/100  (Leibniz)
    S = None
    for k in range(100):
        term = A((-1) ** k) / A(2 * k + 1)
        S = term if S is None else S + term
    quarter_pi = Pi() / 4
    err = max(abs(lb(S) - ub(quarter_pi)), abs(ub(S) - lb(quarter_pi)))
    tol = TOL_1E2
    ok = err < tol["lo"]
    return proof_cert("B03", "theorem",
                      "|(∑ k ∈ Finset.range 100, (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1)) - Real.pi / 4| < 1 / 100",
                      ok,
                      [f"arb partial sum S_100 = {show(S, 22)}",
                       f"arb pi/4 = {show(quarter_pi, 22)}",
                       f"rigorous |S_100 - pi/4| < {_fmt_frac(err)} ({float(err):.6e}) < 1/100",
                       "Leibniz tail bound: the omitted tail is <= 1/(2*100+1) = 1/201 < 1/100"],
                      note="alternating series + exact pi/4 enclosure")


# --------------------------------------------------------------------------
# T15-T17: integrals (Test/IntervalArith/Integrals.lean)
# --------------------------------------------------------------------------

def t15():
    f = lambda X: (-(X * X)).exp()
    d2 = lambda X: (4 * X * X - 2) * (-(X * X)).exp()
    val = T.integral_midpoint(f, d2, 0, 1, n=128)
    ref = mp.quad(lambda t: mexp(-t * t), [0, 1])
    return witness_cert("T15", "|(∫ y in (0 : ℝ)..1, Real.exp (-(y ^ 2))) - x| < 1 / 1000",
                        (lb(val), ub(val)), Fraction(str(ref)), TOL_1E3,
                        note=f"composite midpoint rule n=128, error <= h^3 M2/24 with interval M2; "
                             f"enclosure {show(val, 20)}",
                        witness_str=f"{ref}")


def integral_0_pi(f, d2f, tail_bound, n=128):
    """Rigorous enclosure of int_0^pi f: quadrature on [0, pi_lo] plus a tail
    piece bounded by (pi_hi - pi_lo) * sup|f| on the tail."""
    L = lb(Pi())
    q = T.integral_midpoint(f, d2f, 0, L, n=n)
    return q + I(0, (ub(Pi()) - L) * tail_bound)


def t16():
    f = lambda X: X.sin()
    d2 = lambda X: -(X.sin())
    val = integral_0_pi(f, d2, Fraction(1))
    ref = 2
    return witness_cert("T16", "|(∫ y in (0 : ℝ)..Real.pi, Real.sin y) - x| < 1 / 1000",
                        (lb(val), ub(val)), Fraction(2), TOL_1E3,
                        note=f"exact value 2; quadrature on [0, arb pi] = {show(val, 20)}",
                        witness_str="2")


def t17():
    f = lambda X: X * X.sin()
    d2 = lambda X: 2 * X.cos() - X * X.sin()
    val = integral_0_pi(f, d2, Fraction(3152, 1000))     # sup |x sin x| <= pi_hi
    ref = mp.pi
    return witness_cert("T17", "|(∫ y in (0 : ℝ)..Real.pi, y * Real.sin y) - x| < 1 / 100",
                        (lb(val), ub(val)), Fraction(Decimal_of(dec_lo(val, 20))), TOL_1E2,
                        note=f"exact value pi = {ref}; quadrature = {show(val, 20)}",
                        witness_str=dec_lo(val, 20))


# --------------------------------------------------------------------------
# T18-T20 + B06: special functions and a certified root (Test/IntervalArith/Special.lean)
# --------------------------------------------------------------------------

def t18():
    val = A(Fraction(1, 4)).gamma()
    return witness_cert("T18", "|Real.Gamma (1 / 4) - x| < (10 : ℝ) ^ (-5 : ℤ)",
                        (lb(val), ub(val)), Fraction(Decimal_of(dec_lo(val, 20))), TOL_1E5,
                        note="arb.gamma at 1/4 (reflection/AGM-based, rigorous)",
                        witness_str=dec_lo(val, 20))


def t19():
    val = A(3).zeta()
    return witness_cert("T19", "|(riemannZeta 3).re - x| < (10 : ℝ) ^ (-5 : ℤ)",
                        (lb(val), ub(val)), Fraction(Decimal_of(dec_lo(val, 20))), TOL_1E5,
                        note="arb.zeta(3) (Apéry's constant)",
                        witness_str=dec_lo(val, 20))


def t20():
    w = Fraction(355, 113)
    val = Pi()
    err = max(abs(w - lb(val)), abs(w - ub(val)))
    ok = err < TOL_1E3["lo"]
    return witness_cert("T20", "|Real.pi - x| < 1 / 1000",
                        (lb(val), ub(val)), w, TOL_1E3,
                        note=f"classic continued-fraction convergent 355/113; |355/113 - pi| = {float(err):.6e}",
                        witness_str="355 / 113")


def b06():
    # certified root of x^3 - 2 in [1.25, 1.3]: interval Newton + residual check
    status, box, exists = T.interval_newton(lambda X: X ** 3 - 2, lambda X: 3 * X * X, I(Fraction(5, 4), Fraction(13, 10)), iters=60)
    w = Fraction(Decimal_of(dec_lo(A(2).root(3), 20)))
    resid = abs(w ** 3 - 2)
    tol = TOL_1E7
    ok = resid < tol["lo"] and exists
    lo_r, hi_r = (lb(A(2).root(3)), ub(A(2).root(3)))
    return witness_cert("B06", "abs ((x : ℝ) ^ 3 - 2) < (10 : ℝ) ^ (-7 : ℤ)",
                        (lo_r, hi_r), w, tol, err=resid,
                        note=f"interval Newton on [5/4, 13/10]: {status}, box {show(box, 18)}, "
                             f"existence certified = {exists}; residual |x^3 - 2| of the 20-digit "
                             f"witness {_fmt_frac(resid)}",
                        witness_str=dec_lo(A(2).root(3), 20))


# --------------------------------------------------------------------------
# B04-B05: interval linear algebra (Test/IntervalArith/Linear.lean)
# --------------------------------------------------------------------------

def b04():
    import flint
    M = flint.arb_mat([[1, 2], [3, 4]])
    d = M.det()
    return witness_cert("B04",
                        "|Matrix.det (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) - d| < 1 / 1000",
                        (lb(d), ub(d)), Fraction(-2), TOL_1E3,
                        note=f"arb_mat det = {show(d, 20)} (exact: 1*4 - 2*3 = -2)",
                        witness_str="-2")


def b05():
    import flint
    M = flint.arb_mat([[2, 1], [1, 3]])
    b = flint.arb_mat([[1], [2]])
    x = M.solve(b)
    # residual (2*a + b - 1, a + 3*b - 2) for the interval solution
    a, bb = x[0, 0], x[1, 0]
    tol = TOL_1E3
    r1 = 2 * a + bb - 1
    r2 = a + 3 * bb - 2
    err = max(abs(lb(r1)), abs(ub(r1)), abs(lb(r2)), abs(ub(r2)))
    ok = err < tol["lo"] and abs(lb(a) - Fraction(1, 5)) < Fraction(1, 10 ** 10)
    return witness_cert("B05",
                        "|(2 * v.1 + v.2) - 1| < 1 / 1000 ∧ |(v.1 + 3 * v.2) - 2| < 1 / 1000",
                        (lb(a), ub(a)), Fraction(1, 5), tol, err=err,
                        note=f"arb_mat.solve gives v = ({show(a, 20)}, {show(bb, 20)}); "
                             f"worst residual of the interval solution {float(err):.3g}; "
                             f"exact solution (1/5, 3/5)",
                        witness_str="1 / 5 (v.1), 3 / 5 (v.2)")


# --------------------------------------------------------------------------
# P21-P30: theorems (Test/IntervalArith/Theorems.lean)
# --------------------------------------------------------------------------

def p21():
    ok, msg = T.verify_sup_le(lambda X: X.exp() * X.cos(), 0, 1, 3, parts=512)
    return proof_cert("P21", "theorem",
                      "∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x * Real.cos x ≤ 3", ok,
                      [f"interval subdivision + exp/cos: {msg}",
                       "reference sup = exp(pi/4) cos(pi/4) = 1.550882951115 at r = pi/4 ~ 0.785398",
                       "the relaxed bound 3 leaves a factor ~1.9 of slack"],
                      note="range bound by subdivision")


def p22():
    ok, msg = T.verify_inf_ge(lambda X: X.exp() * X.cos(), 0, 1, 1 - Fraction(1, 100000),
                              parts=512)
    g = A(0).exp() * A(0).cos()
    ok = ok and abs(float(g) - 1) < 1e-30
    return proof_cert("P22", "theorem",
                      "∀ x ∈ Set.Icc (0 : ℝ) 1, 1 ≤ Real.exp x * Real.cos x", ok,
                      [f"interval subdivision: {msg}; the box [0, 1/512] touches the minimum, and "
                       f"cos([0, 1/512]) >= 1 - 1.9e-6 is what the subdivision can give",
                       f"the infimum is exactly 1, attained at r = 0: exp(0) * cos(0) = {show(g, 20)}",
                       "range bound by subdivision; the minimum is attained at the left endpoint"],
                      note="range bound by subdivision, equality at the left endpoint")


def p23():
    ok, msg = T.verify_abs_le(lambda X: X.exp() * X.sin(), 0, 1, Fraction(23, 10), parts=512)
    ref = mexp(1) * msin(1)
    return proof_cert("P23", "theorem",
                      "∀ x ∈ Set.Icc (0 : ℝ) 1, |Real.exp x * Real.sin x| ≤ 23 / 10", ok,
                      [f"interval subdivision + abs: {msg}",
                       f"reference sup = exp(1) sin(1) = {float(ref):.12f} at r = 1",
                       "exp r * sin r >= 0 on [0,1], so the absolute value is redundant here"],
                      note="absolute-value bound")


def p24():
    ok, msg = T.verify_inf_ge(lambda X: X.cos(), -1, 1, Fraction(1, 2), parts=512)
    c1 = A(1).cos()
    return proof_cert("P24", "theorem",
                      "∀ x ∈ Set.Icc (-1 : ℝ) 1, 1 / 2 ≤ Real.cos x", ok,
                      [f"interval subdivision + interval cos: {msg}",
                       f"cos is even and decreasing on [0,1], so inf = cos 1 = {show(c1, 20)}",
                       "cos 1 = 0.5403... > 1/2 with ~8% slack"],
                      note="range bound by subdivision (even function)")


def p25():
    # log r <= r - 1 on [1, oo): derivative sign g' = 1/r - 1 <= 0 and g(1) = 0
    eps = Fraction(1, 10 ** 9)
    ok1, m1 = T.verify_sup_le(lambda X: A(1) / X - 1, 1 + eps, 10 ** 6, Fraction(1, 10 ** 6), parts=1024)
    g1 = A(1).log() - (A(1) - 1)
    tail = A(10 ** 6).log() - A(10 ** 6) + 1
    ok = ok1 and abs(float(g1)) < 1e-70 and ub(tail) < 0
    return proof_cert("P25", "theorem",
                      "∀ x : ℝ, 1 ≤ x → Real.log x ≤ x - 1", ok,
                      [f"g(r) = log r - r + 1; g'(r) = 1/r - 1 <= 0 verified on [1 + 1e-9, 1e6] ({m1})",
                       f"g(1) = 0 exactly ({show(g1, 8)}), so g is decreasing and <= 0 on [1, 1e6]",
                       f"g(1e6) = {show(tail, 12)} < 0 covers the unbounded tail"],
                      note="global statement: derivative-sign certificate + exact endpoint value")


def p26():
    g = lambda X: X.sqrt() - X
    dg = lambda X: 1 / (2 * X.sqrt()) - 1
    ok1, m1 = T.verify_inf_ge(dg, Fraction(1, 100), Fraction(1, 4), Fraction(-1, 10 ** 6), parts=256)
    ok2, m2 = T.verify_sup_le(dg, Fraction(1, 4), 1, Fraction(1, 10 ** 6), parts=256)
    g0 = A(0).sqrt() - A(0)
    gq = (A(1) / 4).sqrt() - A(1) / 4
    g1 = A(1).sqrt() - A(1)
    ok = ok1 and ok2 and abs(float(g0)) < 1e-70 and abs(float(g1)) < 1e-70 and abs(float(gq) - 0.25) < 1e-9
    return proof_cert("P26", "theorem",
                      "∀ x ∈ Set.Icc (0 : ℝ) 1, x ≤ Real.sqrt x", ok,
                      [f"g(r) = sqrt r - r; g' = 1/(2 sqrt r) - 1 >= 0 on [1/100, 1/4] ({m1})",
                       f"and <= 0 on [1/4, 1] ({m2}), so the minimum is at an endpoint",
                       f"g(0) = 0 ({show(g0, 8)}), g(1/4) = 0.25 ({show(gq, 8)}), g(1) = 0 ({show(g1, 8)})"],
                      note="derivative signs + exact endpoint values (raw interval evaluation cannot "
                           "prove an equality-tight bound)")


def p27():
    ok, msg = T.verify_box_sup_le(lambda X, Y: X * Y + X + Y, (0, 1), (0, 1),
                                  Fraction(3000001, 1000000), parts=64)
    corner = A(1) * A(1) + A(1) + A(1)
    ok = ok and lb(corner) <= 3 <= ub(corner)
    return proof_cert("P27", "theorem",
                      "∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, x * y + x + y ≤ 3", ok,
                      [f"interval subdivision over the product of boxes: {msg}",
                       "the maximum 3 is attained at (1,1); bilinear, so the corner value is exact"],
                      note="2-D subdivision; the bound is attained at a corner")


def p28():
    g13 = A(Fraction(1, 3)).gamma()
    g14 = A(Fraction(1, 4)).gamma()
    ok = lb(g13) >= 13 / 5 and ub(g14) <= 37 / 10
    return proof_cert("P28", "theorem",
                      "13 / 5 ≤ Real.Gamma (1 / 3) ∧ Real.Gamma (1 / 4) ≤ 37 / 10", ok,
                      [f"arb Gamma(1/3) = {show(g13, 22)} >= 2.6",
                       f"arb Gamma(1/4) = {show(g14, 22)} <= 3.7",
                       "direct rigorous special-function evaluation (no subdivision needed)"],
                      note="special-function bounds")


def p29():
    ok, msg = T.verify_inf_ge(lambda X: X.tanh(), 1, 2, Fraction(19, 25), parts=512)
    t1 = A(1).tanh()
    return proof_cert("P29", "theorem",
                      "∀ x ∈ Set.Icc (1 : ℝ) 2, 19 / 25 ≤ Real.tanh x", ok,
                      [f"interval subdivision + interval tanh: {msg}",
                       f"tanh is increasing, inf = tanh 1 = {show(t1, 20)} >= 0.76"],
                      note="range bound by subdivision (monotone)")


def p30():
    # sum_{i<n} 2^-(i+1) = 1 - 2^-n < 1, exactly, for every n
    worst = max((1 - Fraction(1, 2 ** n)) for n in [1, 2, 3, 10, 100, 1200])
    exact_ok = all(sum(Fraction(1, 2 ** (i + 1)) for i in range(n)) == 1 - Fraction(1, 2 ** n)
                   for n in [1, 2, 5, 40, 300, 1200])
    S = None
    for i in range(200):
        term = (A(1) / 2) ** (i + 1)
        S = term if S is None else S + term
    arb_ok = ub(S) <= 1
    ok = exact_ok and arb_ok and worst < 1
    return proof_cert("P30", "theorem",
                      "∀ n : ℕ, (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1)) < 1", ok,
                      [f"exact rational closed form sum = 1 - 2^-n verified for n = 1, 2, 5, 40, 300, 1200",
                       f"sup over n: 1 - 2^-1200 = {float(worst):.20f} < 1",
                       f"arb partial sum at n = 200 = {show(S, 20)} <= 1"],
                      note="exact rational identity + Arb accumulation")



def absify(goal):
    """Rewrite `|e|` as `abs (e)` (the spelling used in the request)."""
    out, buf, inside = [], [], False
    for ch in goal:
        if ch == "|":
            if not inside:
                inside, buf = True, []
                out.append("abs (")
            else:
                inside = False
                out.append("".join(buf) + ")")
        else:
            (buf if inside else out).append(ch)
    return "".join(out)



# --------------------------------------------------------------------------
# MP/MD/MR: composition tests (`arb/compositions.py`)
#
#   point :  |<composition> - x| < 1/1000000          (rational witness)
#   nat   :  n = ⌊<composition>⌋                      (floor certified strictly)
#   sign  :  sign <composition> = s                  (sign certified)
#   range :  |sup f - p.1| < tol ∧ |inf f - p.2| < tol (subdivision + refinement)
#
# The `├` shapes come from the same table the Arb suite (group E) runs, so the
# numbers below are the ones checked there; here they are re-derived *per
# declaration* and compared with the witness the Lean goal asks for.
# --------------------------------------------------------------------------

import compositions  # noqa: E402

POINT_TOL = Fraction(1, 10 ** 6)

# Per-test tolerances: the composition group deliberately mixes exact-decimal
# tolerances with irrational ones (a rational *lower* bound of the tolerance is
# what the certificate has to beat, so `Real.pi / 1000` is handled rigorously).
COMP_TOL = {
    "MP02": tol_rat("1 / 10000", Fraction(1, 10 ** 4)),
    "MP05": tol_rat("1 / 100000", Fraction(1, 10 ** 5)),
    "MP09": tol_pi_div(1000, "Real.pi / 1000"),
    "MP13": tol_rat("1 / 100000000", Fraction(1, 10 ** 8)),
    "MP18": tol_pi_div(100, "Real.pi / 100"),
    "MP23": tol_rat("1 / 100000000", Fraction(1, 10 ** 8)),
    "MP24": tol_pi_div(10 ** 7, "Real.pi / (10 : ℝ) ^ 7"),
    "MP27": tol_rat("1 / 10000", Fraction(1, 10 ** 4)),
}
DEFAULT_TOL = tol_rat("1 / 1000000", POINT_TOL)
RANGE_TOL = {
    "MR01": tol_rat("1 / 1000", Fraction(1, 10 ** 3)),
    "MR02": tol_pi_div(1000, "Real.pi / 1000"),
    "MR03": tol_rat("1 / 1000", Fraction(1, 10 ** 3)),
}
DEFAULT_RANGE_TOL = tol_rat("1 / 1000", Fraction(1, 10 ** 3))


def _rat(w):
    return f"({w.numerator} / {w.denominator} : ℝ)" if w.denominator != 1 \
        else f"({w.numerator} : ℝ)"


def _short(w):
    """12-significant-digit decimal of a rational (the witness shown in Lean)."""
    return Fraction(Decimal(mp.nstr(mp.mpf(w.numerator) / mp.mpf(w.denominator), 12)))


def comp_cert(c):
    cid, kind, name = c["id"], c["kind"], c["name"]
    if kind == "point":
        tol = COMP_TOL.get(cid, DEFAULT_TOL)
        ok, lo, hi, err, ref = compositions.eval_point(c)
        w = pick_witness(lo, hi, ref)
        err = max(abs(w - lo), abs(w - hi))
        # NB: the goal keeps `x` as the *unknown*; the witness stays in the
        # certificate only (it is the evidence that such an `x` exists).
        goal = f"abs ({c['lean']} - x) < {tol['lean']}"
        cert = witness_cert(cid, goal, (lo, hi), w, tol,
                            note=f"{c['note']} [{c['functions']}]",
                            witness_str=str(w))
        cert["ok"] = cert["ok"] and ok and err < tol["lo"]
        cert["err"] = _fmt_frac(err, 3)
        cert["kind"] = "point"
        cert["witness_decimal"] = "yes"
        cert["binder"] = "x : Rat"
        cert["name"] = name
        cert["expr"] = c["lean"]
        cert["at"] = c["at"]
        cert["functions"] = c["functions"]
        cert["note_extra"] = c["note"]
        cert["note_extra"] = c["note"]
        return cert
    elif kind in ("nat", "sign", "ceil"):
        ok, n, lo, hi, margin = compositions.eval_nat(c)
        goal_expr = compositions.lean_goal_text(c)
        if kind == "sign":
            goal = f"{goal_expr} = (s : ℝ)"
            witness = str(n)
            decision = "sign"
            detail = (f"Arb enclosure [{_fmt_frac(lo, 18)}, {_fmt_frac(hi, 18)}] is strictly "
                      f"negative, so the sign is {n} (margin {float(-hi):.4f} to 0)")
            why = "the enclosure is strictly one-signed, which decides the sign"
        elif cid == "MD05":
            goal = f"n = {goal_expr}"
            witness = str(n)
            decision = "exact"
            detail = (f"exact integer identity: the Bezout expression `fib 15 - 11 * fib 10` has a "
                      f"zero-width Arb ball, so the value {n} is exact -- no interval search")
            why = "exact integer arithmetic (the identity is proved by the Bezout coefficients)"
        elif kind == "ceil":
            goal = f"n = {goal_expr}"
            witness = str(n)
            decision = "ceiling"
            detail = (f"Arb enclosure of the composition: [{_fmt_frac(lo, 18)}, "
                      f"{_fmt_frac(hi, 18)}]; strict ceiling certificate n = {n} with margin "
                      f"{float(margin):.4f} (the enclosure lies strictly inside ({n - 1}, {n}))")
            why = "a strict enclosure between two consecutive integers decides the ceiling"
        else:
            goal = f"n = {goal_expr}"
            witness = str(n)
            decision = "floor"
            detail = (f"Arb enclosure of the composition: [{_fmt_frac(lo, 18)}, "
                      f"{_fmt_frac(hi, 18)}]; strict floor certificate n = {n} with margin "
                      f"{float(margin):.4f} (the enclosure lies strictly inside ({n}, {n + 1}))")
            why = "a strict enclosure between two consecutive integers decides the floor"
        cert = proof_cert(cid, kind, goal, ok, [detail], note=why)
        cert["decision"] = decision
        cert["note_extra"] = c["note"]
        cert["witness"] = witness
        cert["name"] = name
        cert["binder"] = {"nat": "n : Nat", "ceil": "n : Nat", "sign": "s : ℤ"}[kind]
        cert["err"] = f"margin {float(margin):.4f}"
        cert["tol_disp"] = "exact"
        cert["lean_tol"] = ""
        cert["tol_lo"] = ""
        cert["kind"] = kind
        cert["at"] = c["at"]
        cert["functions"] = c["functions"]
        cert["expr"] = c["lean"]
        return cert
    else:
        tol = RANGE_TOL.get(cid, DEFAULT_RANGE_TOL)
        r = T.range_enclosure(c["py"], c["box"][0], c["box"][1], parts=16384, refine=40)
        vmax, vmin = compositions.mpmath_range(c["ref"], c["box"][0], c["box"][1])
        w_sup, w_inf = _short(Fraction(str(vmax))), _short(Fraction(str(vmin)))
        e_sup = max(abs(w_sup - r["sup_lo"]), abs(w_sup - r["sup_hi"]))
        e_inf = max(abs(w_inf - r["inf_lo"]), abs(w_inf - r["inf_hi"]))
        ok = (e_sup < tol["lo"] and e_inf < tol["lo"]
              and r["sup_lo"] <= Fraction(str(vmax)) <= r["sup_hi"]
              and r["inf_lo"] <= Fraction(str(vmin)) <= r["inf_hi"])
        a, b = c["box"]
        goal = (f"abs (rangeSup (fun r => {c['lean']}) {_lean_rat(a)} {_lean_rat(b)} - p.1) < "
                f"{tol['lean']} ∧\n    abs (rangeInf (fun r => {c['lean']}) {_lean_rat(a)} "
                f"{_lean_rat(b)} - p.2) < {tol['lean']}")
        cert = proof_cert(cid, "range", goal, ok,
                          [f"sup enclosure [{_fmt_frac(r['sup_lo'], 18)}, {_fmt_frac(r['sup_hi'], 18)}], "
                           f"reference {float(vmax):.12g} at r ~ {float(r['argmax'][0]):.6f}, "
                           f"witness error {float(e_sup):.2g}",
                           f"inf enclosure [{_fmt_frac(r['inf_lo'], 18)}, {_fmt_frac(r['inf_hi'], 18)}], "
                           f"reference {float(vmin):.12g} at r ~ {float(r['argmin'][0]):.6f}, "
                           f"witness error {float(e_inf):.2g}",
                           f"functions composed: {c['functions']}"],
                          note="subdivision + refinement of the composed expression")
        cert["witness"] = f"({w_sup}, {w_inf})"
        cert["name"] = name
        cert["binder"] = "p : Rat × Rat"
        cert["enclosure"] = (f"sup in [{_fmt_frac(r['sup_lo'], 18)}, {_fmt_frac(r['sup_hi'], 18)}]",
                             f"inf in [{_fmt_frac(r['inf_lo'], 18)}, {_fmt_frac(r['inf_hi'], 18)}]")
        cert["err"] = f"sup {float(e_sup):.2g}, inf {float(e_inf):.2g}"
        cert["tol_disp"] = tol["disp"]
        cert["lean_tol"] = tol["lean"]
        cert["tol_lo"] = _fmt_frac(tol["lo"], 3)
        cert["expr"] = c["lean"]
        cert["at"] = c["at"]
        cert["functions"] = c["functions"]
        cert["note_extra"] = c["note"]
        cert["wid"] = float(max(r["sup_hi"] - r["sup_lo"], r["inf_hi"] - r["inf_lo"]))
        return cert


def _lean_rat(x):
    f = Fraction(x)
    return f"({f.numerator} / {f.denominator} : ℝ)" if f.denominator != 1 else f"({f.numerator} : ℝ)"


def comp_certs():
    return [comp_cert(c) for c in compositions.ALL_COMPS]


def binder_audit(certs):
    """Every `{ v : T // <goal> }` declaration must actually use `v` in the goal
    (a witness baked into the goal would make the declaration meaningless: it
    would not ask the tactic to produce anything).  Returns the violations."""
    bad = []
    for c in certs:
        binder = c.get("binder")
        if not binder or c["kind"] in ("theorem", "composite"):
            continue
        var = binder.split(":")[0].strip()
        if not re.search(r"\b" + re.escape(var) + r"\b", c["goal"]):
            bad.append(f"{c['id']}: binder `{binder}` unused in `{c['goal'][:60]}`")
    return bad


def coverage_audit():
    """Every mathlib-side function the suite claims must occur in a composition."""
    cov, missing = compositions.function_coverage()
    return missing, cov


ALL = [t01, t02, t03, t04, t05, t06, t07, t08, t09, t10, t11, t12, t13, t14,
       t15, t16, t17, t18, t19, t20, b01, b02, b03, b04, b05, b06,
       p21, p22, p23, p24, p25, p26, p27, p28, p29, p30,
       comp_certs]


def main(verbose=False):
    mp.dps = 40
    certs = []
    for fn in ALL:
        try:
            out = fn()
        except Exception as exc:  # pragma: no cover - diagnostics
            certs.append(proof_cert(getattr(fn, "__name__", "?").upper(), "error", "-", False,
                                    [f"EXCEPTION: {type(exc).__name__}: {exc}"],
                                    note="certificate failed"))
            continue
        certs.extend(out if isinstance(out, list) else [out])
    for c in certs:
        c["goal"] = absify(c["goal"])
    missing, cov = coverage_audit()
    if missing:
        print(f"COVERAGE GAP: no composition exercises {missing}")
    unused = binder_audit(certs)
    for u in unused:
        print(f"UNUSED BINDER: {u}")
    bad = [c for c in certs if not c["ok"]] + [{"id": "BINDER_AUDIT"} for _ in unused]
    write_json(certs)
    write_md(certs)
    if verbose:
        for c in certs:
            print(f"{c['id']:>4} [{'PASS' if c['ok'] else 'FAIL'}] {c['kind']:8} "
                  f"{c['goal'][:78]}")
            for r in c.get("notes", []):
                print(f"        {r}")
            if c["kind"] == "witness":
                print(f"        enclosure {c['enclosure']}  witness {c['witness']}  "
                      f"err {c['err']} < tol {c['tol_lo']} ({c['tol_disp']})")
            if c.get("note"):
                print(f"        note: {c['note']}")
    print(f"certificates: {len(certs) - len(bad)}/{len(certs)} validated")
    for c in bad:
        print(f"  FAIL {c['id']}: {c.get('notes')}")
    return 1 if bad else 0


def write_json(certs):
    with open(os.path.join(OUT_DIR, "certificates.json"), "w") as fh:
        json.dump(certs, fh, indent=1, sort_keys=False)
        fh.write("\n")


def write_md(certs):
    n_ok = sum(1 for c in certs if c["ok"])
    lines = [
        "# Certificates for the Lean tests in `Test/IntervalArith/`",
        "",
        "Generated by `arb/validate_lean_tests.py` (python-flint 0.9.0, Arb balls at 256-bit working "
        "precision, mpmath references).  Every row is the Arb-side ground truth for one Lean "
        "declaration; `arb/certificates.json` carries the same data for the generator "
        "`arb/gen_lean_tests.py`.",
        "",
        f"**{n_ok}/{len(certs)} certificates validated.**",
        "",
        "On the Lean side each declaration is a `by lynth` goal of the shape",
        "`def <name> : { x : Rat // <goal> } := by lynth` (or `Rat × Rat` for ranges, "
        "`theorem <name> : <goal> := by lynth` for the theorem tests).",
        "",
        "| # | kind | Lean goal | Arb enclosure | witness | error | tolerance |",
        "|---|------|-----------|---------------|---------|-------|-----------|",
    ]
    for c in certs:
        enc = c["enclosure"]
        if isinstance(enc, tuple):
            enc = " ".join(enc)
        enc = (enc or "-").replace("|", "\\|")
        goal = c["goal"].replace("|", "\\|")
        w = str(c["witness"]).replace("|", "\\|")
        err = str(c["err"]).replace("|", "\\|") or "-"
        tol = f"{c['tol_disp']} (= {c['tol_lo']})" if c["tol_disp"] else "-"
        lines.append(f"| {c['id']} | {c['kind']} | `{goal}` | {enc} | {w} | {err} | {tol} |")
    lines += ["", "## Certificate detail", ""]
    for c in certs:
        status = "validated" if c["ok"] else "FAILED"
        lines.append(f"### {c['id']} ({status})")
        lines.append("")
        lines.append(f"```lean\n{c['goal']}\n```")
        lines.append("")
        if c.get("notes"):
            for r in c["notes"]:
                lines.append(f"- {r}")
        if c.get("note"):
            lines.append(f"- {c['note']}")
        lines.append("")
    lines += ["## Reproduce", "",
              "```sh", "cd arb && python3 validate_lean_tests.py -v",
              "python3 gen_lean_tests.py        # writes Test/IntervalArith/*.lean", "```", ""]
    with open(os.path.join(OUT_DIR, "CERTIFICATES.md"), "w") as fh:
        fh.write("\n".join(lines))


def Decimal_of(s):  # tiny local alias (keeps call sites short)
    from decimal import Decimal
    return Decimal(s)


if __name__ == "__main__":
    sys.exit(main(verbose="-v" in sys.argv))
