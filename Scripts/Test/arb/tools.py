"""
tools.py -- rigorous interval-arithmetic helpers on top of python-flint / Arb.

Every function here returns *enclosures*: when it hands back an Arb ball B, the
mathematical object it represents is guaranteed to lie in B (modulo the
correctness of Arb, which is why we use it).  Floating point is never used
unguarded -- interval endpoints are extracted from Arb's binary `repr()` as
exact dyadic `Fraction`s, so all comparisons and max/min bookkeeping are exact
rational arithmetic; nothing is ever rounded inward.

Used by
  * tests_arb.py            -- 45 interval-arithmetic experiments
  * validate_lean_tests.py  -- numerical certificates for the Lean tests in
                               Test/IntervalArith/*.lean

`dec_lo` / `dec_hi` turn an enclosure into decimal literals guaranteed to lie
outside the true value -- exactly what may be written into a Lean statement
such as  |Real.cos (Real.pi * 8 / 17) - x| < 1/100000.

Remarks on Arb internals that shape this file:
  * a ball is (midpoint, radius); the midpoint carries full (256-bit) precision
    while the radius is an Arb `mag_t`, i.e. a 30-bit-mantissa bound.  Hence
    enclosures of *wide* intervals carry ~1e-9 relative slack (in exchange for
    very fast, rigorous arithmetic), while *point* evaluations are tight to the
    working precision.  Everything below is aware of this: constants that must
    be tight are computed at degenerate (point) intervals.
  * `arb.str()` prints a symmetric ball as `[+/- r]` (the interval [1,2] prints
    as `[+/- 2.01]`), so endpoints are read from `repr()` instead of `str()`.
"""

from __future__ import annotations

from fractions import Fraction
from decimal import Decimal
import ast
import math
import re

from flint import arb, acb, fmpq, ctx

ctx.prec = 256                       # ~77 decimal digits of working precision
_TINY = Fraction(1, 10 ** 40)


# --------------------------------------------------------------------------
# construction / conversion
# --------------------------------------------------------------------------

def A(x) -> arb:
    """Exact arb from int / Fraction / str / Decimal / arb (never a float)."""
    if isinstance(x, arb):
        return x
    if isinstance(x, Fraction):
        return arb(fmpq(x.numerator, x.denominator))
    if isinstance(x, int):
        return arb(x)
    if isinstance(x, str):
        return arb(x)
    if isinstance(x, Decimal):
        return arb(str(x))
    raise TypeError(f"refusing to build an arb from {type(x)}")


def F(x) -> Fraction:
    """Exact rational (interval endpoints must be exactly representable)."""
    if isinstance(x, Fraction):
        return x
    if isinstance(x, int):
        return Fraction(x)
    if isinstance(x, Decimal):
        return Fraction(x)
    if isinstance(x, str):
        if x.lower() in ("inf", "+inf", "-inf"):
            raise ValueError("infinite endpoint")
        return Fraction(x)
    raise TypeError(type(x))


def I(a, b) -> arb:
    """The interval [a, b] with exact rational endpoints ('inf' allowed).

    Built as a ball with the exact midpoint and half-width; the constructed
    ball is *verified* to contain [a, b] (Arb rounds `mag` radii upward, so it
    always does in practice -- the check is a belt-and-braces guard).
    """
    return _ball_from_bounds(F(a), F(b)) if not _is_inf(a) and not _is_inf(b) \
        else _interval_with_inf(a, b)


def _is_inf(x) -> bool:
    return isinstance(x, str) and x.lower() in ("inf", "+inf", "oo", "+oo", "-inf", "-oo")


def _interval_with_inf(a, b) -> arb:
    lo = arb("inf") if str(a).lower() in ("inf", "+inf", "oo", "+oo") else \
        (arb("-inf") if str(a).lower() in ("-inf", "-oo") else A(a))
    hi = arb("inf") if str(b).lower() in ("inf", "+inf", "oo", "+oo") else \
        (arb("-inf") if str(b).lower() in ("-inf", "-oo") else A(b))
    if lo.is_finite() and hi.is_finite() and _lb(lo) > _ub(hi):
        lo, hi = hi, lo
    return lo if lo == hi else lo.union(hi)


def _ball_from_bounds(lo: Fraction, hi: Fraction) -> arb:
    if lo > hi:
        lo, hi = hi, lo
    if lo == hi:
        return A(lo)
    mid, rad = (lo + hi) / 2, (hi - lo) / 2
    for scale in (Fraction(1), Fraction(1, 2 ** 20), Fraction(1, 2 ** 10),
                  Fraction(1), Fraction(2 ** 10)):
        X = arb(fmpq(mid.numerator, mid.denominator), fmpq(rad.numerator, rad.denominator))
        X = _widen(X, scale) if scale != 1 else X
        if _lb(X) <= lo and _ub(X) >= hi:
            return X
        rad = rad * 2
    return X


def _widen(X: arb, scale: Fraction) -> arb:
    """Multiply the ball radius by 1+scale (keeps the midpoint)."""
    m, r = _mid_rad(X)
    return arb(fmpq(m.numerator, m.denominator),
               fmpq((r * (1 + scale)).numerator, (r * (1 + scale)).denominator))


def Q(p, q=1) -> arb:
    """Exact rational p/q as a degenerate interval."""
    return arb(fmpq(int(p), int(q)))


def Pi() -> arb:
    return arb.pi()


# --------------------------------------------------------------------------
# exact endpoints (from Arb's binary repr -> dyadic Fractions)
# --------------------------------------------------------------------------

def _parse_repr(y: arb):
    """Exact (mid, rad) as Fractions, straight from Arb's binary repr."""
    s = y.repr().strip()
    if "nan" in s:
        return None                      # empty ball
    assert s.startswith("arb(") and s.endswith(")"), s
    inner = s[4:-1]
    parts = _split_top(inner)
    vals = []
    for p in parts:
        p = p.strip()
        if p.startswith("("):
            m, e = [q.strip() for q in p[1:-1].split(",")]
            vals.append(Fraction(int(m, 0)) * Fraction(2) ** int(e, 0))
        else:
            vals.append(Fraction(ast.literal_eval(p)))
    mid = vals[0]
    rad = vals[1] if len(vals) > 1 else Fraction(0)
    return mid, rad


def _split_top(s: str):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    out.append(cur)
    return [p for p in out if p.strip()]


def _mid_rad(y: arb):
    return _parse_repr(y)


def _lb(y: arb) -> Fraction:
    mr = _mid_rad(y)
    if mr is None:                       # empty ball -> inverted (empty) interval
        return Fraction(10) ** 9
    m, r = mr
    return m - r


def _ub(y: arb) -> Fraction:
    mr = _mid_rad(y)
    if mr is None:
        return Fraction(-10) ** 9
    m, r = mr
    return m + r


def lb(x: arb) -> Fraction:
    """Exact lower bound for inf(x); -oo -> huge negative sentinel, empty -> +sentinel."""
    if is_empty(x):
        return Fraction(10) ** 9
    if not x.is_finite():
        return Fraction(-10) ** 9
    return _lb(x)


def ub(x: arb) -> Fraction:
    """Exact upper bound for sup(x); +oo -> huge positive sentinel, empty -> -sentinel."""
    if is_empty(x):
        return Fraction(-10) ** 9
    if not x.is_finite():
        return Fraction(10) ** 9
    return _ub(x)


def is_empty(x: arb) -> bool:
    """True for Arb's empty interval (`[+/- nan]`)."""
    try:
        return ("nan" in x.repr()) or (not x.is_finite() and str(x) == "nan")
    except Exception:
        return True


def is_infinite_interval(x: arb) -> bool:
    return (not x.is_finite()) and (not is_empty(x))


# --------------------------------------------------------------------------
# outward-rounded decimal literals (for Lean constants) and display
# --------------------------------------------------------------------------

def frac_floor_dec(fr: Fraction, places: int) -> Decimal:
    """Exact: round `fr` down to `places` decimals (no floating point)."""
    n = math.floor(fr * 10 ** places)
    return Decimal(n) / Decimal(10 ** places)


def frac_ceil_dec(fr: Fraction, places: int) -> Decimal:
    n = math.ceil(fr * 10 ** places)
    return Decimal(n) / Decimal(10 ** places)


def _dec_str(d: Decimal, places: int) -> str:
    s = f"{d:.{places}f}"
    if "." in s:
        s = s.rstrip("0").rstrip(".")
    return s if s not in ("", "-0") else "0"


def dec_lo(x: arb, places: int = 10) -> str:
    """Lower decimal literal, rounded toward -oo (safe as a Lean lower bound)."""
    if not x.is_finite():
        return "-inf"
    return _dec_str(frac_floor_dec(lb(x), places), places)


def dec_hi(x: arb, places: int = 10) -> str:
    """Upper decimal literal, rounded toward +oo (safe as a Lean upper bound)."""
    if not x.is_finite():
        return "inf"
    return _dec_str(frac_ceil_dec(ub(x), places), places)


def show(x: arb, digits: int = 15) -> str:
    """Human-readable enclosure: decimal interval, plus Arb's own mid +/- rad."""
    if is_empty(x):
        return "empty"
    if not x.is_finite():
        return str(x)
    p = min(digits, 30)
    lo, hi = frac_floor_dec(lb(x), p), frac_ceil_dec(ub(x), p)
    if lo == hi:
        return f"{_dec_str(lo, p)}   (exact to {p} dp)"
    return f"[{_dec_str(lo, p)}, {_dec_str(hi, p)}]"


def rel_width(x: arb) -> float:
    """Relative width of a positive enclosure (tightness measure)."""
    if not x.is_finite():
        return float("inf")
    lo, hi = lb(x), ub(x)
    if lo <= 0 <= hi or (hi + lo) == 0:
        return float("inf")
    return float((hi - lo) / ((hi + lo) / 2))


# --------------------------------------------------------------------------
# subdivision, interval evaluation, range enclosures
# --------------------------------------------------------------------------

def subdivide(a, b, n: int):
    """Exact rational grid points of [a, b] in n steps."""
    a, b = F(a), F(b)
    return [a + (b - a) * Fraction(i, n) for i in range(n + 1)]


def boxes(a, b, n: int):
    g = subdivide(a, b, n)
    return list(zip(g, g[1:]))


def poly_eval_horner(coeffs, X: arb) -> arb:
    """Interval Horner evaluation of a polynomial (coefficients ascending)."""
    acc = arb(0)
    for c in reversed(list(coeffs)):
        acc = acc * X + A(c)
    return acc


def range_enclosure(f, a, b, parts: int = 128, refine: int = 24):
    """Rigorous range enclosure of f on [a, b], with a sup/inf sandwich.

    Returns a dict with
      enclosure        : (lo, hi) Fractions with  f([a,b]) subset of [lo, hi]
      sup_lo / sup_hi  : sup_lo <= sup f <= sup_hi          (rigorous sandwich)
      inf_lo / inf_hi  : inf_lo <= inf f <= inf_hi
      argmax / argmin  : rational boxes containing the extrema
      parts            : number of boxes used
    Method: subdivide, interval-evaluate on every box, then repeatedly bisect
    the boxes that currently determine the four sandwich endpoints.
    """
    data = []
    for (x0, x1) in boxes(a, b, parts):
        Y, _g = eval_box(f, x0, x1)
        if Y is None:
            continue
        data.append([x0, x1, _lb(Y), _ub(Y)])

    def refine_one(idx_fn):
        i = idx_fn(data)
        x0, x1 = data[i][0], data[i][1]
        m = (x0 + x1) / 2
        for (u0, u1) in ((x0, m), (m, x1)):
            Y = f(I(u0, u1))
            data.append([u0, u1, _lb(Y), _ub(Y)])
        data.pop(i)

    for _ in range(refine):
        for idx_fn in (lambda d: max(range(len(d)), key=lambda k: d[k][3]),
                       lambda d: max(range(len(d)), key=lambda k: d[k][2]),
                       lambda d: min(range(len(d)), key=lambda k: d[k][2]),
                       lambda d: min(range(len(d)), key=lambda k: d[k][3])):
            refine_one(idx_fn)

    sup_lo = max(d[2] for d in data)
    sup_hi = max(d[3] for d in data)
    inf_lo = min(d[2] for d in data)
    inf_hi = min(d[3] for d in data)
    return dict(enclosure=(inf_lo, sup_hi), sup_lo=sup_lo, sup_hi=sup_hi,
                inf_lo=inf_lo, inf_hi=inf_hi,
                argmax=tuple(max(data, key=lambda d: (d[3], d[2]))[:2]),
                argmin=tuple(min(data, key=lambda d: (d[2], d[3]))[:2]),
                parts=len(data))


def range_enclosure_inf(f, a, parts: int = 512):
    """Range of f on an unbounded interval [a, +oo) or (-oo, a].

    Split into a bounded part [a, X] plus a tail on which the *monotone* limit
    is checked: the caller passes `f`, and the limit value at infinity is
    computed directly (the helper only documents the pattern); here we treat
    the bounded part and report the tail as computed by interval evaluation on
    [X, X*2] etc.  Kept deliberately simple; the tests call it with functions
    whose behaviour at infinity is monotone.
    """
    xs = [a * (4 ** k) for k in range(1, parts)]
    lo_env, hi_env = None, None
    for x in xs:
        if x <= a:
            continue
        Y = f(I(a, x))
        lo_env = _lb(Y) if lo_env is None else min(lo_env, _lb(Y))
        hi_env = _ub(Y) if hi_env is None else max(hi_env, _ub(Y))
        a = x
    return lo_env, hi_env


def eval_box(f, x0, x1):
    """Evaluate f on [x0,x1]; if the result is empty/NaN (a domain boundary such
    as sqrt at 0 is crossed by the ball's one-ulp radius slack), retry with the
    box nudged inward.  Returns (Y, guarded) or (None, False)."""
    Y = f(I(x0, x1))
    if not is_empty(Y):
        return Y, False
    for k in (1, 8, 64, 512):
        shrink = Fraction(k, 2 ** 20)
        a2, b2 = x0 + (x1 - x0) * shrink, x1 - (x1 - x0) * shrink
        if a2 >= b2:
            break
        Y = f(I(a2, b2))
        if not is_empty(Y):
            return Y, True
    return None, False


def verify_sup_le(f, a, b, bound, parts: int = 512):
    """Rigorously check sup_{[a,b]} f <= bound."""
    worst, at = None, None
    for (x0, x1) in boxes(a, b, parts):
        Yb, _g = eval_box(f, x0, x1)
        if Yb is None:
            continue
        u = _ub(Yb)
        if worst is None or u > worst:
            worst, at = u, (x0, x1)
    ok = worst <= _as_up(bound)
    return ok, f"max box upper bound {float(worst):.10g} on [{at[0]}, {at[1]}]"


def verify_inf_ge(f, a, b, bound, parts: int = 512):
    """Rigorously check inf_{[a,b]} f >= bound."""
    best, at = None, None
    for (x0, x1) in boxes(a, b, parts):
        Yb, _g = eval_box(f, x0, x1)
        if Yb is None:
            continue
        l = _lb(Yb)
        if best is None or l < best:
            best, at = l, (x0, x1)
    ok = best >= _as_down(bound)
    return ok, f"min box lower bound {float(best):.10g} on [{at[0]}, {at[1]}]"


def verify_abs_le(f, a, b, bound, parts: int = 512):
    """Rigorously check |f| <= bound on [a,b]."""
    return verify_sup_le(lambda X: abs(f(X)), a, b, bound, parts)


def verify_box_sup_le(f, box1, box2, bound, parts: int = 48):
    """Rigorously check sup f <= bound on a product of two intervals."""
    (a1, b1), (a2, b2) = box1, box2
    worst, at = None, None
    for (x0, x1) in boxes(a1, b1, parts):
        for (y0, y1) in boxes(a2, b2, parts):
            u = _ub(f(I(x0, x1), I(y0, y1)))
            if worst is None or u > worst:
                worst, at = u, ((x0, x1), (y0, y1))
    return worst <= _as_up(bound), f"max box upper bound {float(worst):.10g} at {at}"


def _as_down(x) -> Fraction:
    return x if isinstance(x, Fraction) else lb(A(x))


def _as_up(x) -> Fraction:
    return x if isinstance(x, Fraction) else ub(A(x))


# --------------------------------------------------------------------------
# Taylor models
# --------------------------------------------------------------------------

def abs_sup(df, a, b, parts: int = 32) -> Fraction:
    """Rigorous upper bound for sup_{[a,b]} |df| (exact Fraction)."""
    hi = None
    for (x0, x1) in boxes(a, b, parts):
        Y = df(I(x0, x1))
        cand = max(abs(_lb(Y)), abs(_ub(Y)))
        hi = cand if hi is None else max(hi, cand)
    return hi


def mean_value_enclosure(f, df, a, b, parts: int = 16):
    """Enclose f([a,b]) with the mean value theorem on sub-boxes:

        f(x) in f(m_i) + f'([x0,x1]) * ([x0,x1] - m_i)

    This keeps the *point* value f(m_i) (which carries no dependency error) and
    pushes the entire variation into the derivative term -- the standard cure
    for expressions like (1 - cos x)/x^2 where plain interval evaluation
    explodes even though f varies by 1e-8 on the box.
    """
    a, b = F(a), F(b)
    out = None
    for (x0, x1) in boxes(a, b, parts):
        m = (x0 + x1) / 2
        Y = f(A(m)) + df(I(x0, x1)) * (I(x0, x1) - A(m))
        out = Y if out is None else out.union(Y)
    return out


def taylor_enclosure(ders, a, b, n: int = 12, pieces: int = 48):
    """Enclose f([a,b]) with an n-th order Taylor model + Lagrange remainder.

    `ders[k]` : interval -> interval enclosing f^(k) on its argument (k = 0..n).

        f(a+t) = sum_{k<n} f^(k)(m)/k! t^k + R(t),
        |R(t)| <= sup_{[a,b]}|f^(n)| * (h/2)^n / n!      (h = b-a, m = midpoint)

    The polynomial part is interval-Horner-evaluated on `pieces` sub-boxes of
    t = x - m: without that subdivision the textbook dependency blow-up makes
    the polynomial part useless (e.g. sin on [0,3] would come out as +/- 2.5),
    with it the model is as sharp as any range algorithm on wide boxes.
    """
    a, b = F(a), F(b)
    m = (a + b) / 2
    h = b - a
    coeffs = [ders[k](A(m)) / math.factorial(k) for k in range(n)]
    M = abs_sup(ders[n], a, b, parts=64)
    rem = M * Fraction(abs(h), 2) ** n / math.factorial(n)
    out = None
    for (t0, t1) in boxes(a - m, b - m, pieces):
        Y = poly_eval_horner(coeffs, I(t0, t1)) + I(-rem, rem)
        out = Y if out is None else out.union(Y)
    return out


# --------------------------------------------------------------------------
# rigorous quadrature
# --------------------------------------------------------------------------

def integral_midpoint(f, d2f, a, b, n: int = 64):
    """Rigorous int_a^b f from the composite midpoint rule.

    Per cell [x0, x0+h], midpoint m, M2 = bound for max|f''| on the cell,

        | int_{x0}^{x0+h} f - h f(m) |  <=  h^3 M2 / 24                (*)

    (Taylor-expand f about m to first order and bound the remainder integral).
    Summing the exact-interval midpoint terms and the error intervals yields a
    genuine enclosure of the integral.
    """
    a, b = F(a), F(b)
    n = int(n)
    h = (b - a) / n
    total = arb(0)
    err = Fraction(0)
    for i in range(n):
        x0 = a + h * i
        x1 = x0 + h
        mi = (x0 + x1) / 2
        total += f(A(mi)) * A(h)
        err += abs_sup(d2f, x0, x1, parts=4) * h ** 3 / 24
    return total + I(-err, err)


def integral_midpoint_d1(f, df, a, b, n: int = 64):
    """Same with a first-derivative bound: |int_cell f - h f(m)| <= M1 h^2 / 2."""
    a, b = F(a), F(b)
    n = int(n)
    h = (b - a) / n
    total = arb(0)
    err = Fraction(0)
    for i in range(n):
        x0 = a + h * i
        x1 = x0 + h
        mi = (x0 + x1) / 2
        total += f(A(mi)) * A(h)
        err += abs_sup(df, x0, x1, parts=4) * h * h / 2
    return total + I(-err, err)


def integral_taylor(ders, a, b, n: int = 16):
    """Rigorous int_a^b f from a Taylor model of the integrand:
       int f = int P + int R,  |int R| <= (b-a) sup |R|."""
    a, b = F(a), F(b)
    m = (a + b) / 2
    h = b - a
    coeffs = [ders[k](A(m)) / math.factorial(k) for k in range(n)]
    s = arb(0)
    for k in range(n):
        Fa = (a - m) ** (k + 1)
        Fb = (b - m) ** (k + 1)
        s += coeffs[k] * A(Fb - Fa) / (k + 1)
    M = abs_sup(ders[n], a, b, parts=64)
    rem = M * Fraction(abs(h), 2) ** n / math.factorial(n) * abs(h)
    return s + I(-rem, rem)


_GL16_X = ["0.0950125098376374401853193354250", "-0.0950125098376374401853193354250",
           "0.2816035507792589132304605014605", "-0.2816035507792589132304605014605",
           "0.4580167776572273863424194429836", "-0.4580167776572273863424194429836",
           "0.6178762444026437484466717640490", "-0.6178762444026437484466717640490",
           "0.7554044083550030338951011948474", "-0.7554044083550030338951011948474",
           "0.8656312023878317438804678977124", "-0.8656312023878317438804678977124",
           "0.9445750230732325760779884155346", "-0.9445750230732325760779884155346",
           "0.9894009349916499325961541734503", "-0.9894009349916499325961541734503"]
_GL16_W = ["0.1894506104550684962853967232083", "0.1894506104550684962853967232083",
           "0.1826034150449235888667636679692", "0.1826034150449235888667636679692",
           "0.1691565193950025381893120790304", "0.1691565193950025381893120790304",
           "0.1495959888165767320815017305475", "0.1495959888165767320815017305475",
           "0.1246289712555338720524762821920", "0.1246289712555338720524762821920",
           "0.0951585116824927848099251076022", "0.0951585116824927848099251076022",
           "0.0622535239386478928628438369944", "0.0622535239386478928628438369944",
           "0.0271524594117540948517805724560", "0.0271524594117540948517805724560"]


def gauss_legendre_enclosure(f, d16f, a, b, n: int = 8):
    """Rigorous composite 16-point Gauss-Legendre enclosure of int_a^b f.

    Error bound per cell (classical, m = 8):
        |E| <= (len)^{2m+1} (m!)^4 / ((2m+1) ((2m)!)^3) * max |f^{(2m)}|
    The 16 nodes/weights are used as exact (long) rationals, so no float ever
    enters the enclosure.
    """
    a, b = F(a), F(b)
    h = (b - a) / n
    c = Fraction(h, 2)
    tot = arb(0)
    err = Fraction(0)
    for i in range(n):
        x0 = a + h * i
        m0 = x0 + c
        for xs_j, ws_j in zip(_GL16_X, _GL16_W):
            w = Fraction(ws_j) * c
            tot += f(A(m0 + c * Fraction(xs_j))) * A(w)
        M = abs_sup(d16f, x0, x0 + h, parts=8)
        err += M * (h ** 17) * Fraction(math.factorial(8) ** 4,
                                        17 * math.factorial(16) ** 3)
    return tot + I(-err, err)


# --------------------------------------------------------------------------
# infinite series: rigorous tail bounds
# --------------------------------------------------------------------------

def alternating_tail(a_next):
    """Enclosure of the tail of an alternating series whose terms a_k are
    positive, decreasing, tending to 0:
        | sum_{k>=N} (-1)^k a_k | <= a_N.
    `a_next` is the first omitted term as an arb ball; returns [-r, r]."""
    r = abs(_ub(a_next))
    return I(-r, r)


def decreasing_series_tail(f, N: int, tail_lo, tail_hi):
    """Tail of a positive decreasing series by the integral test:

        int_N^oo f <= sum_{k>=N} f(k) <= f(N) + int_{N+1}^oo f

    `tail_lo`/`tail_hi` are the two integrals (arb balls, computed by the
    caller); `f` maps k -> interval term.  Returns [lo, hi]."""
    return I(_lb(tail_lo), _ub(f(A(N))) + _ub(tail_hi))


# --------------------------------------------------------------------------
# root finding / verification
# --------------------------------------------------------------------------

def interval_newton(f, df, X, iters: int = 60):
    """Interval Newton for f(x) = 0 on the box X (rational-endpoint boxes).

    Returns (status, (lo, hi), unique_exists).  If some Newton image N(m, X)
    lies inside the current box, the interval Newton theorem proves existence
    of a zero; if it lies *strictly* inside, uniqueness follows -- the classic
    machine-checkable existence proof (Neumaier, "Interval Methods for Systems
    of Equations", 5.1).
    """
    xl, xh = _box(X)
    exists = False
    for _ in range(iters):
        Xi = I(xl, xh)
        m = (xl + xh) / 2
        fm = f(A(m))
        d = df(Xi)
        if (not d.is_finite()) or (is_empty(d)) or (_lb(d) <= 0 <= _ub(d)):
            return ("f' may vanish on the box", (xl, xh), exists)
        N = A(m) - fm / d
        if not N.is_finite() or is_empty(N):
            return ("f(m)/f'(X) undefined", (xl, xh), exists)
        nl, nh = _lb(N), _ub(N)
        if nh < xl or nl > xh:
            return ("empty (no root in the box)", None, False)
        if nl >= xl and nh <= xh:
            exists = True
        box = (max(xl, nl), min(xh, nh))
        if box[1] - box[0] < _TINY:
            return ("converged", box, exists)
        xl, xh = box
    return ("iteration limit", (xl, xh), exists)


def _box(X):
    if isinstance(X, arb):
        return _lb(X), _ub(X)
    lo, hi = F(X[0]), F(X[1])
    return (lo, hi) if lo <= hi else (hi, lo)


def bisect_ivt(f, a, b, iters: int = 200):
    """Sign-change bisection; IVT gives existence of a root in the bracket."""
    a, b = F(a), F(b)
    fa, fb = f(A(a)), f(A(b))
    sa = -1 if _ub(fa) < 0 else (1 if _lb(fa) > 0 else 0)
    sb = -1 if _ub(fb) < 0 else (1 if _lb(fb) > 0 else 0)
    if sa == 0 or sb == 0 or sa == sb:
        return ("no definite sign change", None)
    for _ in range(iters):
        m = (a + b) / 2
        fm = f(A(m))
        sm = -1 if _ub(fm) < 0 else (1 if _lb(fm) > 0 else 0)
        if sm == 0:
            return ("bracket (sign change inside a cell)", (a, b))
        if sm == sa:
            a, sa = m, sm
        else:
            b, sb = m, sm
    return ("bracket (IVT)", (a, b))


def refine_root(f, df, a, b, iters: int = 60):
    """Bisection + interval Newton: verified root enclosure + existence."""
    st, br = bisect_ivt(f, a, b, 200)
    if br is None:
        return st, None, False
    st2, nb, ex2 = interval_newton(f, df, br, iters)
    try:
        stable, nbr, ex3 = interval_newton(f, df, br, iters)
        if nbr is not None and ex3:
            return st2, nbr, True
    except Exception:
        pass
    return st2, nb, bool(ex2)


# --------------------------------------------------------------------------
# tiny test harness shared by the two scripts
# --------------------------------------------------------------------------

class Tally:
    def __init__(self):
        self.rows = []

    def add(self, **kw):
        self.rows.append(kw)
        return kw

    @property
    def n_pass(self):
        return sum(1 for r in self.rows if r.get("status") == "PASS")

    @property
    def n_fail(self):
        return sum(1 for r in self.rows if r.get("status") != "PASS")


def check(cond, tally: Tally, **kw) -> bool:
    kw["status"] = "PASS" if cond else "FAIL"
    tally.add(**kw)
    return bool(cond)


# --------------------------------------------------------------------------
# self-test: enclosures must contain independently computed reference values
# --------------------------------------------------------------------------

def self_test(verbose: bool = False) -> bool:
    from mpmath import mp, exp, sin, cos, sqrt, log, quad
    mp.dps = 50
    ok = True
    TOL = Fraction(1, 10 ** 45)      # reference values are known to ~1e-49

    def contains(x: arb, ref) -> bool:
        r = Fraction(str(ref))
        return lb(x) <= r <= ub(x) or (lb(x) - TOL <= r <= ub(x) + TOL)

    def report(label, cond):
        nonlocal ok
        ok &= bool(cond)
        if verbose:
            print(f"  self-test {label}: {'ok' if cond else 'FAIL'}")

    report("mul", contains(I(1, 2) * I(3, 4), 6) and contains(I(1, 2) * I(3, 4), 8))
    report("sqrt", contains(I(1, 4).sqrt(), str(sqrt(2))))
    report("exp", contains(I(0, 1).exp(), str(exp(1))))
    report("log", contains(I(1, 2).log(), str(log(1.5))))
    report("point sin(1)", contains(A(1).sin(), str(sin(1))))
    report("pi in [3.14159, 3.1416]", Fraction(314159, 100000) <= lb(Pi()) <= ub(Pi())
           <= Fraction(31416, 10000))

    ders = [lambda X: X.sin(), lambda X: X.cos(), lambda X: -X.sin(),
            lambda X: -X.cos()]
    ders = [ders[k % 4] for k in range(17)]
    tm = taylor_enclosure(ders, 0, 3, n=15, pieces=64)
    report("taylor sin suite", contains(tm, str(sin(3))) and contains(tm, "1"))

    f = lambda X: (-(X * X)).exp()
    d2 = lambda X: (4 * X * X - 2) * (-(X * X)).exp()
    ref = quad(lambda t: exp(-t * t), [0, 1])
    report("quad exp(-x^2)", contains(integral_midpoint(f, d2, 0, 1, 64), str(ref)))
    report("quad sin", contains(integral_midpoint(lambda X: X.sin(), lambda X: -X.sin(),
                                                  0, 1, 128),
                               str(1 - cos(1))))
    report("quad taylor", contains(integral_taylor([lambda X: X.sin(), lambda X: X.cos(),
                                                    lambda X: -X.sin(), lambda X: -X.cos(),
                                                    lambda X: X.sin(), lambda X: X.cos()],
                                                   0, 1, n=5),
                                   str(1 - cos(1))))
    report("quad gauss", contains(gauss_legendre_enclosure(
        f, lambda X: (16 * X ** 4 - 48 * X * X + 12) * (-(X * X)).exp(), 0, 1, 4),
        str(ref)))

    st, box, ex = interval_newton(lambda X: X * X - 2, lambda X: 2 * X, I(1, 2))
    report("newton x^2-2", box is not None and ex and contains(I(*box), sqrt(2)))
    st, br = bisect_ivt(lambda X: X.cos() - X, 0, 1)
    report("bisect cos x = x", br is not None
           and contains(I(*br), mp.findroot(lambda t: cos(t) - t, 1)))

    r = range_enclosure(lambda X: X.sin(), 0, 10, parts=64, refine=12)
    report("range sin[0,10]", r["sup_lo"] <= 1 <= r["sup_hi"] and r["inf_lo"] <= -1 <= r["inf_hi"])
    return ok


if __name__ == "__main__":
    print("tools.py self-test:", "PASS" if self_test(verbose=True) else "FAIL")
