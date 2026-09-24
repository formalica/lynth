#!/usr/bin/env python3
"""
Generate `Test/IntervalArith/*.lean` for the lynth `exp_spark` branch from the
Arb certificates in `certificates.json` (produced by `validate_lean_tests.py`).

Nothing here talks to Lean: it only writes text.  Every constant that ends up in
a docstring comes from the validated certificates, so the Lean goal text and the
Arb ground truth cannot drift apart.

Outputs (mirrored):
  * `lynth/Test/IntervalArith/*.lean`  (workspace copy, persists)
  * `REPO/Test/IntervalArith/*.lean`   (the cloned lynth repo, if present)

Run:  python3 gen_lean_tests.py [--repo /tmp/lynth]
"""

import argparse
import json
import re
import os
import shutil
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import compositions  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
WS_DIR = os.path.normpath(os.path.join(HERE, "..", "lynth"))
CERT_PATH = os.path.join(HERE, "certificates.json")


# --------------------------------------------------------------------------
# declaration table: id -> (file, lean name, subtype binder, what it tests)
# --------------------------------------------------------------------------

SPECS = [
    # ---- Basic.lean : point values -------------------------------------
    ("T01", "Basic.lean", "cos_eight_pi_over_seventeen", "x : Rat",
     "`cos (8 * pi / 17)` — the example from the request. An exact rational "
     "multiple of `pi`: the natural implementation reduces `pi` algebraically "
     "instead of evaluating an interval `pi`."),
    ("T02", "Basic.lean", "sin_eight_pi_over_seventeen", "x : Rat",
     "`sin (8 * pi / 17)` with an **irrational tolerance** `pi / 100`: the "
     "tolerance itself is an interval quantity."),
    ("T03", "Basic.lean", "exp_two", "x : Rat",
     "`exp 2` — the elementary transcendental value (compare `Test/Corpus.lean` "
     "style goals, now with a rational witness)."),
    ("T04", "Basic.lean", "log_pi_over_hundred", "x : Rat",
     "`log (pi / 100)` — negative value, irrational argument."),
    ("T05", "Basic.lean", "rpow_two_one_third", "x : Rat",
     "`2 ^ (1/3)` — real power (`Real.rpow`), i.e. Arb's `root 3` / `pow` path."),
    ("T06", "Basic.lean", "sqrt_two", "x : Rat",
     "`sqrt 2` — algebraic value, 10-digit tolerance, needs ~20 digits of "
     "working precision to place a rational witness."),

    # ---- Ranges.lean : range (sup, inf) witnesses ----------------------
    ("T07", "Ranges.lean", "range_sin_zero_one_tenth", "p : Rat × Rat",
     "Range of `sin` on `[0, 1/10]`: `p.1 ~ sup`, `p.2 ~ inf` (the shape from "
     "the request, with the `x.2` typo fixed)."),
    ("T08", "Ranges.lean", "range_cos_zero_three_halves", "p : Rat × Rat",
     "Range of `cos` on `[0, 3/2]`: the supremum `1` is attained at the left "
     "endpoint, the infimum at the right one."),
    ("T09", "Ranges.lean", "range_exp_neg_one_one", "p : Rat × Rat",
     "Range of `exp` on `[-1, 1]`: `e` and `1/e`."),
    ("T10", "Ranges.lean", "range_tan_zero_one", "p : Rat × Rat",
     "Range of `tan` on `[0, 1]` (no pole): `tan 1` and `0`."),
    ("T11", "Ranges.lean", "range_exp_sin_cos_sq", "p : Rat × Rat",
     "Range of `exp (sin x) * cos (x^2)` on `[-1, 1]`: the maximum is an "
     "**interior** extremum (`x ~ 0.704247`), the minimum sits at `x = -1`. "
     "Plain interval evaluation is not enough — subdivision/refinement is "
     "required (the tolerances are correspondingly wider)."),

    # ---- Sums.lean : finite sums, series -------------------------------
    ("T12", "Sums.lean", "sum_exp_cos", "x : Rat",
     "`sum_{k<5} exp (-k) * cos k` — interval accumulation of five terms."),
    ("T13", "Sums.lean", "sum_geometric_half_powers", "x : Rat",
     "`sum_{k<100} (1/2)^(k+1)` with tolerance `1e-30`. The exact value is the "
     "rational `1 - 2^-100`, so this one is provable by exact rational "
     "arithmetic alone (Arb certifies it independently)."),
    ("T14", "Sums.lean", "sum_sin_pi_over_seven", "x : Rat",
     "`sum_{k=1..5} sin (pi k / 7)` — finite sum of exact `pi`-rationals."),
    ("B01", "Sums.lean", "series_inv_sq_tail", None,
     "**Bonus / theorem form.** `|sum_{j=1..1000} 1/j^2 - pi^2/6| < 1/500`: an "
     "infinite series handled by an exact partial sum plus an integral tail "
     "bound (the tail is `~1/1000`)."),
    ("B02", "Sums.lean", "sum_telescoping", None,
     "**Bonus / theorem form.** `sum_{k<n} 1/((k+1)(k+2)) = 1 - 1/(n+1)` for "
     "every `n` — the exact telescoping closed form."),
    ("B03", "Sums.lean", "alternating_series_pi_over_four", None,
     "**Bonus / theorem form.** `|sum_{k<100} (-1)^k/(2k+1) - pi/4| < 1/100` — "
     "Leibniz' alternating series: the tail bound is the first omitted term "
     "(`1/201`), the value is `pi/4`."),

    # ---- Integrals.lean : quadrature ----------------------------------
    ("T15", "Integrals.lean", "integral_exp_neg_sq", "x : Rat",
     "`integral_0^1 exp (-x^2)` — non-elementary integrand; rigorous "
     "quadrature (midpoint rule with an interval error term)."),
    ("T16", "Integrals.lean", "integral_sin", "x : Rat",
     "`integral_0^pi sin = 2` — the integration endpoint is `Real.pi` itself."),
    ("T17", "Integrals.lean", "integral_x_sin", "x : Rat",
     "`integral_0^pi x * sin x = pi` — irrational value, irrational endpoint."),

    # ---- Special.lean : special functions, roots ----------------------
    ("T18", "Special.lean", "gamma_quarter", "x : Rat",
     "`Gamma (1/4)` — Arb's rigorous Gamma (reflection/AGM based)."),
    ("T19", "Special.lean", "zeta_three", "x : Rat",
     "`(riemannZeta 3).re` — Apéry's constant; `riemannZeta` is `ℂ → ℂ`, so "
     "the goal reads off the real part."),
    ("T20", "Special.lean", "pi_rational", "x : Rat",
     "`pi` to within `1/1000`: the classical rational witness is `355/113` "
     "(continued fractions / interval bisection)."),
    ("B06", "Special.lean", "root_cube_two", "x : Rat",
     "**Bonus.** A certified root: `|x^3 - 2| < 1e-7` (interval Newton on "
     "`[5/4, 13/10]`, existence certified by bisection)."),

    # ---- Linear.lean : interval linear algebra ------------------------
    ("B04", "Linear.lean", "det_two_by_two", "d : Rat",
     "**Bonus.** `det !![1, 2; 3, 4] = -2` — a matrix entry point (Arb's "
     "`arb_mat.det`)."),
    ("B05", "Linear.lean", "linear_system_witness", "v : Rat × Rat",
     "**Bonus.** A 2x2 linear system as a refinement goal: the residual form "
     "`|2 v.1 + v.2 - 1| < 1/1000 ∧ |v.1 + 3 v.2 - 2| < 1/1000` pins down "
     "`(1/5, 3/5)` (Arb's `arb_mat.solve`)."),

    # ---- Theorems.lean : plain theorems -------------------------------
    ("P21", "Theorems.lean", "exp_mul_cos_le_three", None,
     "`exp x * cos x <= 3` on `[0, 1]` — the request's example theorem (the "
     "true supremum is `exp (pi/4) * cos (pi/4) = 1.5509`)."),
    ("P22", "Theorems.lean", "exp_mul_cos_ge_one", None,
     "`1 <= exp x * cos x` on `[0, 1]` — equality at `x = 0`, so the proof "
     "needs the exact endpoint value, not just a coarse box."),
    ("P23", "Theorems.lean", "abs_exp_mul_sin_le", None,
     "`|exp x * sin x| <= 23/10` on `[0, 1]` — an absolute-value bound "
     "(`sup = e sin 1 = 2.2874`)."),
    ("P24", "Theorems.lean", "cos_ge_half_on_unit", None,
     "`1/2 <= cos x` on `[-1, 1]` — even function, infimum `cos 1 = 0.5403`."),
    ("P25", "Theorems.lean", "log_le_sub_one", None,
     "`log x <= x - 1` for all `x >= 1` — **unbounded** domain: the standard "
     "certificate is the derivative sign (`1/x - 1 <= 0`) plus `log 1 - 1 + 1 "
     "= 0`; interval subdivision alone cannot reach infinity."),
    ("P26", "Theorems.lean", "le_sqrt_on_unit", None,
     "`x <= sqrt x` on `[0, 1]` — equality at both endpoints and a stationary "
     "point at `1/4`: derivative signs + exact endpoint values."),
    ("P27", "Theorems.lean", "bilinear_box_le_three", None,
     "`x * y + x + y <= 3` on the unit square — a 2-D box, the maximum is "
     "attained at the corner `(1, 1)`."),
    ("P28", "Theorems.lean", "gamma_bounds", None,
     "`13/5 <= Gamma (1/3) ∧ Gamma (1/4) <= 37/10` — direct rigorous "
     "special-function enclosures."),
    ("P29", "Theorems.lean", "tanh_ge_on_one_two", None,
     "`19/25 <= tanh x` on `[1, 2]` — monotone special function."),
    ("P30", "Theorems.lean", "geometric_partial_lt_one", None,
     "`sum_{i<n} (1/2)^(i+1) < 1` for every `n` — the exact rational closed "
     "form `1 - 2^-n` settles all `n` at once."),
]

# --------------------------------------------------------------------------
# composition tests (arb/compositions.py + arb/CERTIFICATES.md)
#
# The coverage requirement is met by *composition*, not by conjoining separate
# statements: every declaration below is one expression tree in which several
# special functions appear (`f (g x + h x)`), plus the discrete
# `{ n : Nat // n = ⌊f x⌋₊ }` shape.  No function is ever nested inside its own
# inverse (`arcsin (sin x)`), and `arb/compositions.py:audit_no_inverse_pairs()`
# checks that mechanically.
# --------------------------------------------------------------------------

COMP_FILE = {"point": "Compositions.lean", "nat": "Discrete.lean",
             "ceil": "Discrete.lean", "sign": "Discrete.lean",
             "range": "Ranges.lean"}

for _c in compositions.ALL_COMPS:
    SPECS.append((_c["id"], COMP_FILE[_c["kind"]], _c["name"], None,
                  f"composition of {_c['functions']} at `{_c['at']}`"))

FILES = ["Basic.lean", "Ranges.lean", "Sums.lean", "Integrals.lean",
         "Special.lean", "Linear.lean", "Theorems.lean", "Compositions.lean",
         "Discrete.lean"]

# ids whose (name, binder, description) come from the certificates
CERT_DRIVEN = {c["id"] for c in compositions.ALL_COMPS}

FILE_HEADERS = {
    "Compositions.lean": """The coverage layer, by **composition**: each declaration is a
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
Ground truth: `arb/CERTIFICATES.md` (MP01-MP35).""",
    "Discrete.lean": """The discrete layer: rounding and exact integer answers of composed
expressions, in the shape

  `def name : { n : Nat // n = ⌊<composition>⌋₊ } := by lynth`
  `def name : { s : ℤ // Real.sign <composition> = (s : ℝ) } := by lynth`

`⌊·⌋₊` is mathlib's `Nat.floor : ℝ → ℕ` (the plain `⌊·⌋` is `Int.floor` and
would make the `Nat` goal ill-typed).  The certificate is a strict enclosure:
the Arb ball of the composition has to sit inside `(n, n+1)` for a floor and
inside `(n-1, n)` for a ceiling, with the margin recorded in
`arb/CERTIFICATES.md`.  MD05 is an exact integer identity
(`Nat.gcd (fib 10) (fib 15) = 5`, certified by the Bezout expression
`fib 15 - 11 * fib 10`); MD06 certifies a *sign*, not a value.
Ground truth: `arb/CERTIFICATES.md` (MD01-MD07).""",
    "Basic.lean": """T01-T06: point values -- the request's shape
  `def name : { x : Rat // |<expr> - x| < <tolerance> } := by lynth`
over `cos`/`sin` of rational multiples of `pi`, `exp`, `log`, real powers
and `sqrt`.  Tolerances range from `1e-10` to the irrational `pi / 100`.
Ground truth: `arb/CERTIFICATES.md` (Arb, 256-bit, python-flint 0.9.0).""",
    "Ranges.lean": """T07-T11 + MR01-MR03: range tests -- the shape
  `def name : { p : Rat × Rat // |sup f - p.1| < tol ∧ |inf f - p.2| < tol } := by lynth`
where `sup`/`inf` are the supremum and infimum of `f` over a closed box
(`rangeSup`/`rangeInf` below, via `sSup`/`sInf`).  T07-T11 use elementary
functions; MR01-MR03 use *compositions* (`exp (sin r + cos r)`,
`arctan (sin r + cos r)`, `exp (cos r) * sin r`) whose extrema are interior
points, so plain interval evaluation is not enough.
Ground truth: `arb/CERTIFICATES.md` (subdivision + refinement of the
extremal boxes).""",
    "Sums.lean": """T12-T14 + B01-B03: finite sums and (via tail bounds) infinite series.
T12-T14 are refinement goals; B01-B03 are plain theorems about series.
Ground truth: `arb/CERTIFICATES.md` / `arb/RESULTS.md` (A13-A16, B03, B04).""",
    "Integrals.lean": """T15-T17: interval integrals `∫ y in a..b, ...` of non-elementary
integrands and with `Real.pi` as an endpoint; the certificates come from
rigorous quadrature (see `arb/tools.py: integral_midpoint`).
Ground truth: `arb/CERTIFICATES.md` / `arb/RESULTS.md` (A17, A18).""",
    "Special.lean": """T18-T20 + B06: special functions (`Gamma`, `zeta`, `pi`) and a
certified algebraic root.  Ground truth: `arb/CERTIFICATES.md`; the Arb
surface behind these is `arb.gamma`, `arb.zeta`, `arb.const_pi` and
interval Newton (`arb/tools.py: interval_newton`).""",
    "Linear.lean": """B04-B05: interval linear algebra -- a determinant value and a 2x2
linear system posed as a refinement goal (Arb's `arb_mat.det` /
`arb_mat.solve`; see `arb/tests_arb.py` C05).""",
    "Theorems.lean": """P21-P30: plain theorems (no witness returned), the second half of the
20/10 split requested.  They cover: range bounds by subdivision, an
unbounded-domain derivative certificate (P25), a stationary-point case
(P26), a 2-D box (P27), special-function bounds (P28, P29) and an exact
rational closed form (P30).
Ground truth: `arb/CERTIFICATES.md` / `arb/tests_arb.py` A21-A30.""",
}

PRELUDE = {
    "Ranges.lean": """
/-- Supremum of `f` over the closed interval `[a, b]` (`sSup` of the image;
junk value for an empty set, which cannot occur for `a <= b`). -/
noncomputable def rangeSup (f : ℝ → ℝ) (a b : ℝ) : ℝ := sSup (f '' Set.Icc a b)

/-- Infimum of `f` over the closed interval `[a, b]`. -/
noncomputable def rangeInf (f : ℝ → ℝ) (a b : ℝ) : ℝ := sInf (f '' Set.Icc a b)
""",
}

HEADER = """import Mathlib
import Lynth

/-!
{header}
-/

namespace IntervalArith
"""

FOOTER = """
end IntervalArith

-- The repository convention (`Test/*.lean`, `Test/Grind/README.md`) pins the
-- axiom footprint of every declaration once the goals go through.  Uncomment
-- (and keep the `info` docstring in sync) when a goal starts closing:
--
-- /-- info: '{name}' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- #guard_msgs in
-- #print axioms {name}
"""


def wrap(text, width=96, indent=""):
    words, lines, cur = text.split(), [], ""
    for w in words:
        if cur and len(indent) + len(cur) + 1 + len(w) > width:
            lines.append(indent + cur)
            cur = w
        else:
            cur = f"{cur} {w}".strip()
    if cur:
        lines.append(indent + cur)
    return "\n".join(lines)


def cert_summary(cert):
    """One-line Arb certificate for a docstring."""
    if cert["kind"] == "witness":
        enc = cert["enclosure"]
        if isinstance(enc, list) or isinstance(enc, tuple):
            enc = "; ".join(enc)
        bits = [f"enclosure `{enc}`"]
        if cert["witness"]:
            bits.append(f"witness `{cert['witness']}`")
        if cert["err"]:
            bits.append(f"worst error `{cert['err']}` < `{cert['tol_lo']}`")
        return ", ".join(bits)
    return "; ".join(cert.get("notes", []))


def cert_docstring(cert):
    """Docstring for a generated (certificate-driven) declaration."""
    fid = cert["id"]
    name = cert.get("name", fid.lower())
    kind = cert["kind"]
    fns = cert.get("functions", "")
    at = cert.get("at", "")
    disp = ", ".join(t for t in fns.split(", ")
                     if t not in ("floor", "ceil", "sign")) or fns
    if kind == "point":
        head = wrap(f"**{fid}** — `{name}`: `{fns}` composed in one expression, "
                    f"evaluated at `{at}`.")
        paras = [head,
                 wrap(f"`x` is the *unknown*: the tactic has to produce a rational witness "
                      f"inside the tolerance `{cert.get('tol_disp', '-')}`.  Arb encloses the "
                      f"composition in `{cert['enclosure'][0]}` / `{cert['enclosure'][1]}` "
                      f"(it is far narrower than the tolerance), which is the certificate that "
                      f"such an `x` exists; the concrete witness Arb found -- "
                      f"`{cert.get('witness', '')}`, within `{cert.get('err', '0')}` -- is "
                      f"recorded here only, never in the goal."),
                 wrap(cert.get("note_extra", "") + ".")]
    elif kind == "range":
        head = wrap(f"**{fid}** — `{name}`: the range of `{fns}` on the closed box, as a "
                    f"`Rat × Rat` of `(sup, inf)`.")
        paras = [head] + [wrap(n) for n in cert.get("notes", [])]
        if cert.get("note_extra"):
            paras.append(wrap(cert["note_extra"] + "."))
    elif cert.get("decision") == "exact":
        head = wrap(f"**{fid}** — `{name}`: an exact integer identity over `{disp}` "
                    f"(inputs `{at}`), returned as a `Nat`.")
        paras = [head, wrap(cert["notes"][0] + "."),
                 wrap(cert.get("note_extra", "") + ".")]
    elif cert.get("decision") == "sign":
        head = wrap(f"**{fid}** — `{name}`: the sign of `{disp}` composed at `{at}`, returned "
                    f"as an `Int`.")
        paras = [head, wrap(cert["notes"][0] + "."),
                 wrap(cert.get("note", "") + f": {cert.get('note_extra', '')}.")]
    else:
        what = cert.get("decision", "floor")
        head = wrap(f"**{fid}** — `{name}`: the {what} of `{disp}` composed at `{at}`, "
                    f"returned as a `Nat`.")
        paras = [head, wrap(cert["notes"][0] + "."),
                 wrap(cert.get("note", "") + f": {cert.get('note_extra', '')}.")]
    paras.append(wrap("Arb ground truth: `arb/CERTIFICATES.md` "
                      "(`arb/validate_lean_tests.py`, table `arb/compositions.py`)."))
    return "/-- " + "\n\n".join(paras) + " -/"


def cert_declaration(cert):
    """`def <name> : { <binder> // <goal> } := by lynth`.

    The subtype's bound variable must occur in the goal: baking the witness into
    the goal instead would make the declaration meaningless (the tactic would
    have nothing to produce).  Checked here, and again over the written files in
    `main()`."""
    binder = cert.get("binder", "x : Rat")
    goal = cert["goal"].replace("\n", "\n    ")
    var = binder.split(":")[0].strip()
    if not re.search(r"\b" + re.escape(var) + r"\b", cert["goal"]):
        raise ValueError(f"{cert['id']}: binder `{binder}` unused in the goal "
                         f"`{cert['goal'][:70]}`")
    return f"def {cert['name']} : {{ {binder} // {goal} }} := by lynth"


def docstring(spec, cert):
    if spec[0] in CERT_DRIVEN:
        return cert_docstring(cert)
    tid, _file, _name, _binder, what = spec
    paras = [wrap(f"**{tid}** — {what}"),
             wrap(cert_summary(cert) + ".")]
    if cert.get("note"):
        paras.append(wrap(cert["note"] + "."))
    paras.append(wrap("Arb ground truth: `arb/CERTIFICATES.md` "
                      "(`arb/validate_lean_tests.py`)."))
    body = "\n\n".join(paras)
    return "/-- " + body + " -/"


def declaration(spec, cert):
    if spec[0] in CERT_DRIVEN:
        return cert_declaration(cert)
    tid, _file, name, binder, _what = spec
    goal = cert["goal"]
    if cert["kind"] == "theorem":
        return f"theorem {name} : {goal} := by lynth"
    return f"def {name} : {{ {binder} // {goal} }} := by lynth"


def build_file(fname, specs, certs):
    parts = [HEADER.format(header=FILE_HEADERS[fname])]
    if fname in PRELUDE:
        parts.append(PRELUDE[fname])
    for spec in specs:
        cert = certs[spec[0]]
        parts.append("\n" + docstring(spec, cert))
        parts.append(declaration(spec, cert))
    parts.append(FOOTER.format(name=specs[-1][2]))
    return "\n".join(parts).rstrip("\n") + "\n"


README = """# `Test/IntervalArith/` — interval-arithmetic tests for `lynth`

81 `by lynth` goals whose expected behaviour was **computed first with Arb**
(python-flint 0.9.0, 256-bit balls) and frozen in `arb/CERTIFICATES.md`.  No Lean
has been run on these files: the tactic is expected to grow the capability they
describe.

* **36 numbered tests** — T01–T20 (computational, `{ x : Rat // ... }` /
  `{ p : Rat × Rat // ... }`), P21–P30 (plain theorems), B01–B06 (bonus).
  This is the 20/10 split of the request.
* **45 composition tests** — MP01–MP35 (point compositions), MD01–MD07
  (discrete: rounding and exact integers) and MR01–MR03 (ranges of composed
  functions).  Coverage of the special-function surface is by **composition**:
  every declaration is one expression tree in which several functions appear
  (`Real.exp (Real.sin x + Real.cos x)`, `Real.arcsin (Real.tanh a * Real.cos b)`,
  `Real.sqrt ((Complex.digamma 3).re + Real.exp (-1))`, ...), never a list of
  separate statements joined by `∧`.  `arb/compositions.py` holds the same 49
  expressions (45 mirrored here + 4 Arb-only) and
  `audit_no_inverse_pairs()` checks mechanically that no function is nested
  inside its own inverse (`arcsin (sin x)` would be `simp`-provable and would
  test nothing).

  In every point test the subtype's `x` is the **unknown**: the goal is
  `abs (<composition> - x) < tol`, so the tactic has to produce the rational
  witness.  The witness Arb found (and its distance to the enclosure) lives in
  the docstring and in `arb/CERTIFICATES.md` only -- never in the goal, which
  would make the declaration vacuous.  `binder_audit()` in the validator and
  `audit_binders()` in the generator both fail loudly if a bound variable does
  not occur in its goal.

## Layout

| file | ids | count | goal shape |
|---|---|---|---|
| `Basic.lean` | T01–T06 | 6 | `{ x : Rat // abs (f - x) < tol }` for `cos`/`sin` of `k·pi`, `exp`, `log`, `rpow`, `sqrt` |
| `Ranges.lean` | T07–T11, MR01–MR03 | 8 | `{ p : Rat × Rat // abs (rangeSup f a b - p.1) < tol ∧ abs (rangeInf f a b - p.2) < tol }` |
| `Sums.lean` | T12–T14, B01–B03 | 6 | finite sums; series by exact partial sums + integral/Leibniz tails |
| `Integrals.lean` | T15–T17 | 3 | `{ x : Rat // abs ((∫ y in a..b, f y) - x) < tol }`, incl. `Real.pi` endpoints |
| `Special.lean` | T18–T20, B06 | 4 | `Gamma`, `riemannZeta`, `pi` (witness `355/113`), certified root of `x^3 - 2` |
| `Linear.lean` | B04–B05 | 2 | determinant value; 2×2 linear system as a refinement goal |
| `Theorems.lean` | P21–P30 | 10 | `theorem <name> : ∀ x ∈ Set.Icc a b, f x ≤ c := by lynth` |
| `Compositions.lean` | MP01–MP35 | 35 | **composed** special functions, `{ x : Rat // abs (<composition> - x) < tol }` |
| `Discrete.lean` | MD01–MD07 | 7 | `{ n : Nat // n = ⌊<composition>⌋₊ }`, `{ n : Nat // n = ⌈<composition>⌉₊ }`, `{ s : ℤ // Real.sign <composition> = (s : ℝ) }` |

Tolerances run from `1e-30` (exact geometric sum) through `1e-10`, `1e-8`,
`1e-7`, `1e-6`, `1e-5`, `1/500`, `1/1000`, `1/10000`, `1/100000`, up to the
irrational `Real.pi / 100`, `Real.pi / 1000` and `Real.pi / (10 : ℝ) ^ 7`.

## Composition coverage of the special functions

Every mathlib declaration the suite is meant to exercise occurs in at least one
composition (checked automatically: `arb/compositions.py:function_coverage()`):

{coverage_table}

The Arb-only compositions exercise functions mathlib has no declaration for at
the pinned rev — they are the same kind of test, run only on the Arb side
(`arb/tests_arb.py` group E, `arb/RESULTS.md`):

{arb_only_table}

## The Arb surface behind the Lean tests

`arb/function_zoo.py` walks Arb's whole `arb` surface: every attribute is
exercised somewhere (audited against `dir(arb)`), grouped into 14 families
(D01–D14) with 170 entry-point checks against independent references (mpmath at
40 digits, exact rationals, FLINT-style two-precision agreement).  The
composition tests above are the Lean-facing layer of the same inventory: each
one is a single Arb evaluation of a nested expression, and its certificate
records the enclosure, the rational witness and the margin to the tolerance.

## Running

```sh
for f in Test/IntervalArith/*.lean; do lake env lean "$f" || echo "FAILED $f"; done
```

The files are deliberately **not** wired into `.github/workflows/lean_action_ci.yml`
yet (same treatment as `Test/ProgSynth/`, whose goals wait for a capability): the
interval-arithmetic procedure they describe does not exist in `lynth` at the time
of writing, so they are expected to fail until it lands.

## What each goal needs from the tactic

* **Point values (T01–T06, T18–T20, MP01–MP29).** Rigorous evaluation to ~20
  decimal digits plus a rational-witness search in the tolerance ball; the
  composition goals additionally need the evaluation to *compose* (each function
  consumes the ball produced by the previous one) rather than to be specialised
  per function.  `cos (8*pi/17)` and `tan (pi/4)` want *exact* `pi`-reduction
  (Arb: `cos_pi_fmpq`/`sin_pi_fmpq`), otherwise the enclosure degrades by the
  radius of `pi`'s ball.
* **Discrete answers (MD01–MD07).** A decision, not a value: the enclosure has to
  be compared strictly against the two neighbouring integers (`Nat.floor`:
  `⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1`), which is exactly the Arb certificate; MD05
  is an exact integer identity and MD06 certifies one-signedness.
* **Ranges (T07–T11, MR01–MR03, P21–P24, P27, P29).** Subdivision of the box plus
  refinement of the extremal boxes; a single interval evaluation is not enough
  (T11's and MR01–MR03's maxima are interior, P27's is at a corner).
* **Equality-tight bounds (P22, P26).** The bound is attained, so the certificate
  needs the *exact* endpoint value (`exp 0 * cos 0 = 1`, `sqrt 0 = 0`) in addition
  to the numerical sandwich.
* **Unbounded domains (P25).** Interval subdivision cannot cover `[1, ∞)`: the
  certificate is a derivative-sign bound on a finite window plus a value at the cut.
* **Sums (T12–T14, B01–B03, P30).** Exact rational accumulation where the closed
  form is rational (`1 - 2^-n`, telescoping), and partial sum + rigorous tail bound
  (integral test, Leibniz) where it is not.
* **Integrals (T15–T17).** Quadrature with an interval error term; `Real.pi`
  endpoints are interval quantities.
* **Dependency/cancellation.** `arb/RESULTS.md` C01–C02 record the two classical
  traps (`x - x` gives `[-1, 1]` on `[0, 1]`; `(1 - cos x)/x^2` on `[-1e-3, 1e-3]`
  needs a cancellation-free primitive) — a subdivision-only tactic will miss goals
  of that kind.

## Certificates

`arb/validate_lean_tests.py` recomputes every number here from Arb and checks
`max(|enclosure - witness|) < tolerance` with **rational** arithmetic (irrational
tolerances are bounded below by an Arb enclosure of `pi`); theorem certificates
are re-verified by interval subdivision / derivative-sign checks, the range
certificates by 16384-box subdivision with refinement of the extremal boxes, and
the discrete ones by a strict enclosure between the two neighbouring integers.
`arb/gen_lean_tests.py` writes these files from those certificates, so the goal
text and the Arb ground truth cannot drift apart.  Current status: 81/81
certificates validated (`arb/tests_arb.py`: 108/108 Arb tests).
"""


DECL_RE = re.compile(r"^(def|theorem)\s+(\w+)\s*:\s*\{(.+?)//(.*?)\}\s*:=\s*by lynth",
                     re.M | re.S)


def audit_binders(out_dir):
    """Every generated `{ v : T // <goal> }` must use `v` in the goal."""
    bad = []
    for fname in FILES:
        text = open(os.path.join(out_dir, fname)).read()
        for m in DECL_RE.finditer(text):
            binder, goal = m.group(3).strip(), m.group(4)
            var = binder.split(":")[0].strip()
            if not re.search(r"\b" + re.escape(var) + r"\b", goal):
                bad.append(f"{fname}:{m.group(2)}")
    return bad


def coverage_table():
    """function -> composition test -> Lean declaration (the composition coverage)."""
    import re
    rows = ["| mathlib declaration | composition tests (Arb) | Lean declaration | value at |",
            "|---|---|---|---|"]
    cov = {}
    for c in compositions.ALL_COMPS:
        cov.setdefault(c["id"], c)
    for name in compositions.MATHLIB_FUNCTIONS:
        ids = [c["id"] for c in compositions.ALL_COMPS
               if name in compositions.lean_goal_text(c)]
        if not ids:
            continue
        decls = ", ".join("`" + cov[i]["name"] + "`" for i in ids[:3])
        if len(ids) > 3:
            decls += f", +{len(ids) - 3}"
        at = "; ".join(dict.fromkeys(cov[i]["at"] for i in ids[:3]))
        disp = name.strip()
        if disp == "^":
            disp = "`^` (real power)"
        elif disp == "⌊":
            disp = "`⌊·⌋₊` (`Nat.floor`)"
        elif disp == "⌈":
            disp = "`⌈·⌉₊` (`Nat.ceil`)"
        rows.append(f"| `{disp}` | {', '.join(ids)} | {decls} | {at} |")
    return "\n".join(rows)


def arb_only_table():
    """The Arb-only compositions: functions mathlib has no declaration for."""
    rows = ["| Arb-only test | functions | value |",
            "|---|---|---|"]
    for c in compositions.ARB_ONLY:
        rows.append(f"| `{c['id']}` `{c['name']}` | {c['functions']} | {c['at']} |")
    return "\n".join(rows)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default="/tmp/lynth")
    args = ap.parse_args()

    with open(CERT_PATH) as fh:
        certs = {c["id"]: c for c in json.load(fh)}

    targets = [os.path.join(WS_DIR, "Test", "IntervalArith")]
    repo_dir = os.path.join(args.repo, "Test", "IntervalArith")
    if os.path.isdir(args.repo):
        targets.append(repo_dir)

    for out in targets:
        os.makedirs(out, exist_ok=True)
        for fname in FILES:
            specs = [s for s in SPECS if s[1] == fname]
            text = build_file(fname, specs, certs)
            with open(os.path.join(out, fname), "w") as fh:
                fh.write(text)
        with open(os.path.join(out, "README.md"), "w") as fh:
            fh.write(README.replace("{coverage_table}", coverage_table())
                    .replace("{arb_only_table}", arb_only_table()))
        bad = audit_binders(out)
        print(f"wrote {len(FILES)} files + README.md -> {out}"
              + ("" if not bad else f"  !! UNUSED BINDERS: {bad}"))


if __name__ == "__main__":
    main()
