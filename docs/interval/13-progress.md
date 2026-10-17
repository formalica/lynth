# 13 — Progress (living document)

Update at every milestone.  Keep "Next" pointing at the lowest unfinished item.

## Numerical integration update — 2026-10-17

The Real Petras/Gauss-Legendre engine is implemented in Integral/ and
Goals/Integral.lean. It synthesizes rational witnesses, checks integrability,
handles selected improper endpoints/tails, and proves recognized divergence.
The one-dimensional regressions include the migrated tests, selected real
FLINT examples, orientation and evaluator regressions. The ten-dimensional
cube remains in TestFailures. Recursive real integrals are handled by the
separate fallback described in [15-nested-integrals.md](15-nested-integrals.md):
dependent bounds, recursive sampling, shared tables and memoized certificate
replay, half-lines/whole lines, and certified endpoint transformations.
There are 23 nested integration regressions and five certificate rejection
groups. The passing integration suite has 87 declarations/groups; full FLINT 16
remains in TestFailures because of its runtime. Every testcase retains its
own measured +5% heartbeat cap.

The third performance pass documented in
[16-integration-performance.md](16-integration-performance.md) completes all
six formerly slow FLINT targets (8, 9, 12, 15, 16 and 32) at their original
statements and tolerances. FLINT 8 uses a general reciprocal-phase endpoint
bound. Cases 8 and 32 are in Test; FLINT 16 retains its full [0,8]
interval in TestFailures because it still takes about 90 seconds overall. Native bit-length primitives,
local expression sharing, cheaper powers, reuse of the search estimate and
chunked certificate compilation reduce numerical work. The final checker
still independently replays every certificate. A signed-shift allocation
regression was caught by the existing nested caps and corrected before the
final measurement. The performance log records timings and validation.

Proof status is explicitly provisional under the user's authorization:
78 Mathlib-only obligations in /tmp/intgrl and 19 Lynth-dependent adapter gaps.
The mathematical packets elaborate independently; no Lynth-dependent theorem
is included in the proof handoff. Heavy certificates follow the existing
auto/native trust policy, and their axiom footprints are recorded in tests.
See [14-gauss-legendre-plan.md](14-gauss-legendre-plan.md) for algorithms,
coverage, validation, and remaining limits. Older non-integration milestone
rows below have not been audited against the current implementation.

## Milestones

| id | content | status |
|---|---|---|
| M0 | spec (`docs/interval/*`), test statement fixes | in progress |
| M1 | `Num/`: vendored Dyadic, `Dy` rounding ops, `Ival`, `NIval`, `CBox` + proofs | todo |
| M2 | `Core/`: Ty, Ctx, Fn records, Env, Expr, denote, eval, eval_sound, PropExpr | todo |
| M3 | Registry attribute, reifier, exact evaluator, trust driver, Approx + Closed handlers; arithmetic, π, ln2, exp, log, sqrt | todo |
| M4 | trig, arctan, arcsin/arccos, hyperbolic, rpow, logb, sinc; complex basics (M4c); Basic.lean + M4 Compositions green | todo |
| M5 | discrete answers, finite sums; Discrete/Sums/Special(T20) | todo |
| M6 | branch & bound, box goals, roots | todo |
| M7 | AD + monotone leaves | todo |
| M8 | ranges, extrema | todo |
| M9 | Taylor models + Taylor capabilities | todo |
| M10 | Real Petras quadrature and integrability implemented; proofs and complex integral extension remain | in progress |
| M11 | infinite series (AIA, tails, non-summability); M11c | todo |
| M12 | meta adaptive (convergence caps); M12c | todo |
| M13 | meta integral + piecewise polynomials | todo |

## Done

Real numerical integration engine and the test migrations described above.

## Next

Integration: complete the portable mathematical proofs and local adapters;
extend function capabilities and uniform majorants for the remaining real
examples. Public complex paths and product-domain/Fubini normalization remain
separate work. Benchmark evaluator crossovers before treating them as tuned.

## Known gaps / risks

* Kernel speed ≈ 4000 Taylor steps/s (200-bit integers, measured
  2026-09-30 with a structural-recursion exp series).  Heavy certificates must
  go native under `auto`.
* Computability of `Fn1` records containing `Real.*` in `Prop` fields must be
  confirmed in M2 (see 03 §3).

## Deferred notes (special functions, for later phases)

* Gamma: IMPLEMENTED (`Lynth/Interval/Fns/Gamma.lean`, registry `gammaR`)
  via Stirling + shifting + reflection (FLINT design), fully proved
  (Stirling analysis in `Fns/StirlingExpansion.lean`, no axioms).
  The old incomplete-gamma plan (shift into
  `(0,1]`, split `Real.Gamma_eq_integral` at `X = 40`) was benchmarked out:
  120+ transcendental evals per point and ~2^16 cancellation vs ~60 interval
  ops for Stirling.  T18, P28, MP03, MP04, MP23 close (standard footprint).
  MD02 additionally needs `Nat.floor` (registered).  Future work:
  endpoint-tight wide intervals via certified monotonicity pieces.
* zeta (real `s > 1`): `zeta_eq_tsum_one_div_nat_add_one_cpow`, partial sums +
  integral-test tail.
* Euler γ: IMPLEMENTED (`Lynth/Interval/Fns/EulerGamma/Eval.lean`,
  registry `eulerR`) via Brent–McMillan B3 (FLINT design:
  `γ ≈ A_N/B_N − K/B_N² − log m`, joint `A`/`B` fold + `K` fold,
  analytic radius + `24·e^{−8m}` main bound), fully proved
  (`EulerGamma/Bound`, `SeriesBounds`, `Eval`, no axioms).
  The old `eulerMascheroniSeq` bracketing (width ~ 1/n) is kept in
  `Fns/Const.lean` (`eulerIvalN`) for reference only.
* digamma at naturals: `Complex.digamma_nat_add_one` (`H_n - γ`).
* agm: `NNReal.agmSequences_fst_le_agm`, `NNReal.agm_le_agmSequences_snd`.
* Hypergeometric (|z| < 1): coefficient lemma
  `coeff_regularizedGaussHGFunSeries`, ratio-test tails.
