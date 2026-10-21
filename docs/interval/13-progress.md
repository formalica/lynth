# 13 — Progress (living document)

Update at every milestone.  Keep "Next" pointing at the lowest unfinished item.

## Real integral and sum composition — 2026-10-20

Real arithmetic can now contain integral and finite/infinite sum values. A
recursive enclosure handler combines membership proofs, preserves local real
parameter boxes, expands finite binders hygienically, and composes uniform
geometric/power tail bounds. Both nesting orders are covered, including
index-dependent bounded integration endpoints and arithmetic around aggregates.

`Test/IntervalArith/IntegralInExpression.lean` covers these shapes, shadowed
binders, local hypotheses, long prefixes, higher precision, kernel checking,
integrability/summability fields, and rejection of a divergent series.
It compiles alongside the existing `Integrals`, `InfiniteSums`,
`NestedIntegrals`, and `IntegralKernelCertificates` regressions. The axiom
audit confirms standard axioms for the new tail and remainder lemmas.
The new lemmas introduce no admissions; the existing nested integration
checker still has its documented mathematical proof dependencies. See
[20 — Composition](20-composition.md) for the supported scope and limits.

## Complex integrands over real ranges — 2026-10-18

The previous special-function and internal-proof work is committed as `90b9fa5`.
Complex-valued functions now compile to certified real and imaginary projections
and reuse real Gauss–Legendre/Petras integration, including real nested bounds
and absolutely integrable half-lines/whole lines. Exact affine-phase primitives,
principal-branch splits, and logarithmic endpoint bounds cover ten of the
seventeen supplied elementary NIntegrate examples. Seven remaining cases are
tracked in `TestFailures/ComplexIntervalArith/Integrals.lean`; Bessel-J is absent
from the installed Mathlib and has no Lynth evaluator.

`Test/ComplexIntervalArith/Integrals.lean` adds twenty numerical declarations and
two convergence-preservation checks. Each passing and failing testcase has its
own measured heartbeat cap with 5% headroom. Five mathematical obligations and
their pure supporting syntax are copied to `/tmp/intgrl`; all fourteen standalone
modules compile with Lynth unavailable. The new local interval adapters are
proved; the previous three unfinished internal adapters remain unchanged.
See [19-complex-real-integrals.md](19-complex-real-integrals.md).

## Internal integration proofs — 2026-10-18

Sixteen of the 19 Lynth-dependent integration placeholders now have proofs,
including all one-dimensional panel, node-table and finite assembly adapters,
plus nested samples, direct panels and canonical memo replay. Three nested
internal placeholders remain: recursive integral range evaluation, analytic
extensions and assembly. Supporting proofs now cover binder transport,
complete formula dispatch, real-value complex-fallback arithmetic, scaled
endpoint arithmetic, and numerical endpoint moments/remainders. A binder-capture
bug in the power-integral formula recognizer and empty memo environments are
covered by measured regressions. The 95 previously handed-off portable
mathematical obligations stay unchanged. See
[18-internal-integration-proofs.md](18-internal-integration-proofs.md) for the
exact completed and remaining theorem lists.

The requested extraction adds 16 portable obligations in `NestedEnvelope`
(Mathlib only) and `NestedChange` (the small pure expression specifications).
Their standalone copies and dependencies typecheck in `/tmp/intgrl`.
The local `collapse` and scaled real unary/rational-power proofs now consume
these contracts. Whole-line split assembly is proved after adding a separate
check for inner convergence at the split point; its rejection regression uses
454 heartbeats with an individual cap of 477. The three top-level adapters
still have unfinished parts, as listed in the proof-status document.

## Special functions — 2026-10-18

Independent real and complex erf, Si, Dirichlet eta and Airy Ai definitions
and integer evaluators are implemented. Real integration recognizes all four;
new regression files cover numeric expressions and FLINT 25/26/30/37 at their
original domains. See [17-special-functions.md](17-special-functions.md).
There are 27 new numeric checks and eight new integration checks (95 passing
integration checks in total), each with measured +5% heartbeat caps. Seventeen
new generic mathematical obligations are mirrored in the Mathlib-only
SpecialFunctions, SpecialKernel and SpecialBounds packets under /tmp/intgrl. The interval
adapters and generated problem proofs have no new project-specific gaps.

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
At that milestone there were 78 Mathlib-only obligations in /tmp/intgrl and
19 Lynth-dependent adapter gaps; the updates above supersede those counts.
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
