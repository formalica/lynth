# `Test/IntervalArith/` — interval-arithmetic tests for `lynth`

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

| mathlib declaration | composition tests (Arb) | Lean declaration | value at |
|---|---|---|---|
| `Real.exp` | MP01, MP02, MP09, MP10, MP12, MP13, MP14, MP15, MP16, MP20, MP22, MP23, MP27, MP28, MD01, MD06, MD07, MR01, MR03 | `exp_sin_add_cos`, `sin_exp_mul_cos`, `arccos_sinh_mul_exp`, +16 | x = 1/2 |
| `Real.log` | MP04, MP17, MP22, MP23, MP30 | `log_gamma_add_sqrt`, `log_chebyshev_u_add_three`, `arctan_log_ten_mul_exp`, +2 | x = 1/4, 2; n = 4, x = 1/3; x = log 10 / e |
| `Real.logb` | MP15 | `logb_exp_sin` | base 2, x = 1 |
| `Real.log 10` | MP22 | `arctan_log_ten_mul_exp` | x = log 10 / e |
| `Real.log 2` | MP23, MP30 | `log_two_gamma_div_exp`, `log_mul_hypergeometric` | x = 1/4; a = b = 1, c = 2, x = 1/2 |
| `Real.sqrt` | MP04, MP18, MP21, MP24, MP25, MP26, MP27, MD03, MD04 | `log_gamma_add_sqrt`, `cos_euler_add_sqrt`, `cos_bernoulli_four_add_sqrt`, +6 | x = 1/4, 2; x = gamma + sqrt 2; n = 4 |
| `Real.sinc` | MP10 | `sinc_exp_mul_sin` | x = 1 |
| `Real.sin` | MP01, MP02, MP03, MP05, MP06, MP09, MP10, MP11, MP13, MP14, MP15, MP16, MP19, MP29, MD01, MR01, MR02, MR03 | `exp_sin_add_cos`, `sin_exp_mul_cos`, `gamma_sin_add_two`, +15 | x = 1/2 |
| `Real.cos` | MP01, MP02, MP05, MP06, MP07, MP08, MP12, MP18, MP21, MD01, MD06, MD07, MR01, MR02, MR03 | `exp_sin_add_cos`, `sin_exp_mul_cos`, `tan_sinh_mul_cos`, +12 | x = 1/2; x = 1/3 |
| `Real.tan` | MP05, MP08, MP24, MD03 | `tan_sinh_mul_cos`, `arcsin_tanh_mul_cos`, `sqrt_pi_mul_tanh`, +1 | x = 1/3; x = 1/2, 1/3; x = 1/2 |
| `Real.cot` | MP11 | `cot_sinh_add_two` | x = 1/2 |
| `Real.arcsin` | MP08 | `arcsin_tanh_mul_cos` | x = 1/2, 1/3 |
| `Real.arccos` | MP09 | `arccos_sinh_mul_exp` | x = 1/2 |
| `Real.arctan` | MP06, MP22, MR02 | `cosh_sin_add_arctan`, `arctan_log_ten_mul_exp`, `range_arctan_sin_add_cos` | x = 1; x = log 10 / e; r in [0, 2] |
| `Real.sinh` | MP05, MP09, MP11, MP19 | `tan_sinh_mul_cos`, `arccos_sinh_mul_exp`, `cot_sinh_add_two`, +1 | x = 1/3; x = 1/2 |
| `Real.cosh` | MP06 | `cosh_sin_add_arctan` | x = 1 |
| `Real.tanh` | MP08, MP24, MD03 | `arcsin_tanh_mul_cos`, `sqrt_pi_mul_tanh`, `floor_hundred_tanh_sqrt_two` | x = 1/2, 1/3; x = 1/2; x = sqrt 2 |
| `Real.arsinh` | MP12 | `arsinh_cos_mul_exp` | x = 1/2 |
| `Real.arcosh` | MP13 | `arcosh_exp_add_sin` | x = 1/2 |
| `Real.artanh` | MP14 | `artanh_sin_mul_exp` | x = 1/4 |
| `Real.Gamma` | MP03, MP04, MP23, MD02 | `gamma_sin_add_two`, `log_gamma_add_sqrt`, `log_two_gamma_div_exp`, +1 | x = 1/2; x = 1/4, 2; x = 1/4 |
| `riemannZeta` | MP07 | `zeta_cos_add_three` | s = cos(1/3) + 3 |
| `Real.pi` | MP24 | `sqrt_pi_mul_tanh` | x = 1/2 |
| `Real.eulerMascheroniConstant` | MP18 | `cos_euler_add_sqrt` | x = gamma + sqrt 2 |
| `Complex.digamma` | MP27 | `sqrt_digamma_add_exp` | x = 3 |
| `NNReal.agm` | MP26 | `sqrt_agm` | x = 1, y = 2 |
| `ascPochhammer` | MP28 | `pochhammer_four_third_mul_exp` | n = 4, x = 1/3 |
| `Polynomial.Chebyshev.T` | MP16 | `exp_chebyshev_t_add_sin` | n = 4, x = 1/3 |
| `Polynomial.Chebyshev.U` | MP17 | `log_chebyshev_u_add_three` | n = 4, x = 1/3 |
| `Polynomial.bernoulli` | MP20 | `exp_bernoulli_poly` | n = 2, x = 1/3 |
| `bernoulli` | MP20, MP21 | `exp_bernoulli_poly`, `cos_bernoulli_four_add_sqrt` | n = 2, x = 1/3; n = 4 |
| `Nat.bell` | MP19 | `sinh_bell_over_hundred` | n = 5 |
| `Nat.choose` | MP25 | `choose_div_factorial_mul_sqrt` | n = 7, k = 3 |
| `Nat.factorial` | MP25 | `choose_div_factorial_mul_sqrt` | n = 7, k = 3 |
| `Nat.fib` | MD05 | `gcd_of_fib` | n = 10, 15 |
| `Nat.gcd` | MD05 | `gcd_of_fib` | n = 10, 15 |
| `Real.sign` | MD06 | `sign_exp_sub_cos` | x = 1, 1/2 |
| `ordinaryHypergeometric` | MP30 | `log_mul_hypergeometric` | a = b = 1, c = 2, x = 1/2 |
| `regularizedGaussHGFun` | MP31 | `regularized_gauss_hypergeometric_neg5` | a = 1, b = 2, c = 3, z = -5 |
| `regularizedHGFun` | MP32, MP33, MP34, MP35 | `regularized_pfq_3f2`, `regularized_pfq_2f3`, `regularized_pfq_4f3`, +1 | 3F2: a = (1, 1, 1), b = (2, 2), z = 1/2; 2F3: a = (1, 2), b = (3, 4, 5), z = 1/4; 4F3: a = (1, 1, 1, 1), b = (2, 2, 2), z = 1/4 |
| ``⌊·⌋₊` (`Nat.floor`)` | MD01, MD02, MD03, MD04 | `floor_exp_two_add_sin_div_cos`, `floor_gamma_quarter_add_gamma_third`, `floor_hundred_tanh_sqrt_two`, +1 | x = 2, 1; x = 1/4, 1/3; x = sqrt 2 |
| ``⌈·⌉₊` (`Nat.ceil`)` | MD07 | `ceil_ten_exp_cos` | x = 1 |
| ``^` (real power)` | MP29 | `rpow_sin_exponent` | base 2, exponent sin(1/2) + 1/4 |

The Arb-only compositions exercise functions mathlib has no declaration for at
the pinned rev — they are the same kind of test, run only on the Arb side
(`arb/tests_arb.py` group E, `arb/RESULTS.md`):

| Arb-only test | functions | value |
|---|---|---|
| `ME01` `arb_erf_exp_add_sin` | erf, exp, sin | x = 1 |
| `ME02` `arb_bessel_j_cosh_add_sqrt` | bessel_j, cosh, sqrt | x = 1/2, 3 |
| `ME03` `arb_lambertw_exp_add_cos` | lambertw, exp, cos | x = 1 |
| `ME04` `arb_polylog_cos_half` | polylog, cos | x = 1/2 |

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
