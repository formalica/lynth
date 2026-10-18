# Certified numerical integration: implementation plan

Investigation: 2026-10-16. Implementation started: 2026-10-17.
The Petras engine and integral goal handler are implemented with explicitly
authorized mathematical proof placeholders. These are not completed proofs.

Current modules are in Lynth/Interval/Integral/ and Goals/Integral.lean.
The checker uses exact dyadic arithmetic; only the untrusted search uses floats.
It checks sign brackets, shared node tables, analytic bounds, individual panel
errors, the partition, uncertain endpoints and the final strict inequality.
The GL panel theorem composes the affine analytic error theorem with interval
sample and remainder bounds. Remaining Ival adapters are marked with sorry.
Tail adapters consume both the finite-panel proof and the portable tail theorem.

Implemented numerical paths include fixed-point Bonnet recurrence with delayed
division, endpoint/parity series with rectangular splitting, asymptotic
evaluation, geometric-precision Newton refinement, a maximum-error heap,
degree/ellipse search, branch specialization, and explicit tail bounds.
Evaluator crossover thresholds are provisional: no fastest-implementation
claim is made before comparative benchmarks.

The subsequent performance pass is documented in
[16-integration-performance.md](16-integration-performance.md). Previously
timed-out FLINT cases 8, 9, 12 (at `10⁻⁹²`), 15 and 32 now complete and have
passing regression tests. Full case 16 computes the correct result but remains
in TestFailures because its runtime is still about 90 seconds overall.

Node tables carry outward weight intervals as literal certificate data.
The checker compares them with its computed weight enclosures once, and panels
reuse those literals. Symmetric brackets and weights use one half of the rule.
Newton refinement reuses its midpoint derivative. For floor(x), the search cuts
at integer jumps and specializes on panel interiors; endpoint values are
irrelevant to the Lebesgue integral. No closed-form integral answer is inserted.

Remaining project-specific proof gaps are seven numeric/analytic adapters in
Panel.lean, partition/endpoints in finiteAssembly_sound, three improper
transport adapters in Engine.lean, and conditionCheck_sound in Divergence.lean.
These adapters consume the actual panel and mathematical tail proofs.

Current API limits: the integration compiler covers the elementary expression
language in Math/Integrand.lean. General registry extension metadata, nested
integrals inside arithmetic expressions, pure relative goals, multivariate
integrals, other special-function integrands and complex contour goals remain work
for later milestones. Failure of quadrature never selects divergence;
only a separately checked analytic non-integrability rule does that.
Real erf/Si/eta/Airy integration is covered by the 2026-10-18 extension in
[17-special-functions.md](17-special-functions.md).

T15-T21 compile through lynth with their original tolerances and are moved
to Test/IntervalArith/Integrals.lean. The portable handoff has 50 obligations
in 11 modules; all elaborate with Mathlib alone. Further validation is recorded
below as tests are migrated.

All eight convergent one-dimensional IC cases and all ten ID divergence cases
also typecheck and are moved to Test/IntervalArith/ImproperIntegrals.lean.
Only IC09, the ten-dimensional cube, remains in TestFailures. User predicates
and tolerances are preserved; expected axiom messages include sorryAx.

Eight FLINT real cases and two orientation cases are added to the passing
Integrals test file. At 64 bits their accepted certificates use:

| FLINT case | Panels | Cached node counts |
|---|---:|---|
| 0: sin on [0,100] | 1 | 46 |
| 1: 1/(1+x²) on [0,1] | 1 | 16 |
| 3: sqrt(1-x²) on [0,1] | 24 | 6, 4, 2 |
| 4: sin(x+exp(x)) on [0,8] | 20 | 90, 64 |
| 5: floor on [1,101] | 100 | none (direct interior bounds) |
| 6: absolute polynomial times exp | 32 | 6, 4, 2, 1 |
| 24: max(sin,cos) on [0,pi] | 38 | 4 |
| 31: x*sin(x)/(1+cos²(x)) on [0,pi] | 4 | 16, 8 |

The original 25 cases plus these ten regressions exercise the actual lynth
goal handler and theorem compositions. These counts are validation results,
not a comparison claiming FLINT-equivalent throughput.

Final checks on 2026-10-17 passed: lake build Lynth, both integration test
modules, Test.IntervalArith.Basic, Test.IntervalArith.Compositions, and the
standalone 11-module proof packet checker. The packet sources match the
project's Math/ copies apart from import paths. Validation scratch sources
and logs are in /tmp/lynth-integration-validation; /tmp/intgrl contains only
the portable proof package and its compiled packet modules.

Implement the **Petras method used by FLINT**: direct interval enclosure,
adaptive bisection, and degree-adaptive Gauss-Legendre quadrature certified by
complex analytic bounds. Use ordinary real evaluation at quadrature nodes.
No Taylor models, integrand jets, or high derivatives of the integrand are
required. This replaces the integration design in 07-integrals.md.

## Baseline before implementation (2026-10-16)

- Dyadic arithmetic, outward-rounded real intervals, and complex rectangles:
  Num/Dy.lean, Num/Ival.lean, Num/CBox.lean.
- Real and complex elementary evaluators, and complex Gamma, digamma and zeta.
  Reuse these kernels rather than introducing a second arithmetic backend.
- An open function registry, reified expression evaluation and soundness,
  rational witness generation, and the kernel/native certificate driver.
- Series goal handling provides a useful pattern for subtype and PSum handling.
- **No implemented quadrature, integral expression constructor, integral goal
  handler, or compositional measurability/analyticity capability.**
  Fn records certify value enclosure only. A finite complex value enclosure
  does not certify holomorphicity.
- Test/IntervalArith/Integrals.lean and ImproperIntegrals.lean are empty.
  TestFailures contains the substantive tests. Existing design/progress
  documents describe planned features and are not implementation evidence.
- Mathlib v4.34.0 contains shifted Legendre polynomials and Chebyshev tools,
  including a weighted Chebyshev-Gauss formula. It does not supply the
  unweighted Legendre quadrature/error API needed here.
- The user's changes to TestFailures/IntervalArith/Integrals.lean are inputs
  to this plan. Preserve the tighter tolerances and added result types.

## Exact FLINT behavior to retain

Relevant local sources:

- /tmp/flint/examples/integrals.c: callbacks, all 39 examples, and manual tails.
- /tmp/flint/src/acb_calc/integrate.c: direct enclosure, work queue, bisection.
- /tmp/flint/src/acb_calc/integrate_gl_auto_deg.c: ellipse/degree search,
  node cache and quadrature.
- /tmp/flint/src/arb_hypgeom/legendre_p_ui{,_rec,_zero,_one,_asymp,_root}.c:
  hybrid polynomial evaluation and root/weight generation.

For a panel [a,b], m=(a+b)/2 and d=(b-a)/2:

1. Bound f on the real panel, giving the direct integral enclosure
   (b-a) f([a,b]). This also handles bounded, measurable nonanalytic pieces.
2. Find an analytic extension F around the panel. Bound it on a rectangle
   containing a Bernstein ellipse. For normalized ellipse semiaxes X,Y,
   rho=X+Y>1 and Y=sqrt(X²-1).
3. With M=d sup|F|, FLINT's n-node error bound is

   E = 64 M / (15 (rho-1) rho^(2n-1)).

   The transformed half-length occurs **once**. Node/weight uncertainty and
   numerical evaluation/roundoff are additional interval errors.
4. Choose the least expensive certified degree, evaluate its nodes once,
   and widen the result by E. Otherwise bisect.

FLINT's callback order=0 means value enclosure; order=1 additionally
requires analyticity. It is not a first derivative request in this algorithm.
Its default degree limit is floor(min(precision,goal)/2)+60. Its cached degree
sequence starts 1,2,4,6,8,12,16,22,32,46,64,90,128,...
and then grows approximately by sqrt(2).

Use FLINT's proven design as the performance baseline. Any crossover or
heuristic changes must be justified by measurements of Lean execution and
kernel verification, not by difficulty of proving an algorithm.

## Fast nodes, weights and polynomial evaluation

Use a **hybrid implementation from the outset**:

| Situation | Selected evaluator |
|---|---|
| Modest degree and precision, away from endpoint cancellation | Bonnet recurrence in integer fixed-point arithmetic, with an a priori roundoff bound |
| Near x=1 | Terminating hypergeometric expansion in (x-1)/2, with early truncation and a certified tail; evaluate the derivative directly |
| Near x=0 or high precision where recurrence loses to series | Parity-aware polynomial expansion about zero |
| Large degree where an error estimate permits it | Large-degree asymptotic expansion with an explicit remainder |
| Series evaluation | Rectangular splitting, shared powers for value/derivative, batched small-integer divisions |

Do not propagate interval radii through the recurrence at every step:
dependency inflation would require O(n) extra bits. Fixed-point recurrence
admits O(n² * 2^(-p)) error with only O(log n) guard bits. Reuse P_(n-1)
to form P'_n away from endpoints. Use local first/second derivative bounds
to transport midpoint evaluations to root intervals.

Generate root candidates with cosine/asymptotic approximations. Their
accuracy is untrusted. Certify disjoint sign brackets and refine with
interval Newton, increasing precision geometrically. An existing root is
preserved by the Newton enclosure; contraction alone is not an existence
proof. If a seed is poor, widen/reseed or bisect its bracket.

At a certified root x_i use

  w_i = 2 / ((1-x_i²) P'_n(x_i)²).

Generate and store only one half of the nodes/weights and reconstruct the
other half by symmetry; the odd-degree central node is exactly zero. Cache
by degree and certified precision. Reuse a higher precision entry by outward
rounding, and grow cache precision geometrically on upgrades.

For the kernel path, certify each node table once and share its theorem
across panels and declarations where possible. Search/refinement history
does not belong in each integral certificate.

## Analytic extensions and integration semantics

Add companion capabilities to the function registry, leaving existing
closed-expression clients usable:

- A compositional measurability certificate for the original real function.
- A real-to-complex extension rule: real agreement on a panel, complex
  evaluation, and analyticity under explicit domain checks.
- Separate range evaluation and analytic evaluation modes.

Start with constants, arithmetic, natural powers, exp, sin/cos, hyperbolic
functions, reciprocal/division away from zero, and positive-argument log,
sqrt and real powers. Reuse the current complex numerical kernels.

For abs/max/min, select an analytic branch using certified real range
information. For floor, certify a constant branch on the panel interior.
The selected extension can be analytic beyond the branch's real domain;
the proof needs agreement on the integration panel, not agreement with a
globally fixed complex formula. Interior or almost-everywhere agreement
allows harmless jumps at partition endpoints.

Real.log on negative inputs, Real.sqrt on nonpositive inputs, and powers
on negative bases need the appropriate real-semantics extension. A blind
replacement of every Real function by its principal complex counterpart
is incorrect. Conjugation, complex norm and real/imaginary projections are
not holomorphic complex operations; use a justified extension or direct
real enclosure.

For an analytic leaf, continuity of the extension plus interior agreement
proves integrability. For a nonanalytic direct leaf, use measurability and
a finite bound. Prove all accepted leaves integrable and compose the proofs.
Keep interval-integral orientation; normalize Icc/Ioc/Ioo bounded set
integrals using null endpoints. A zero-length interval is an exact zero.

For pi or another inexact endpoint, first enclose it tightly. Integrate
between exact dyadic anchors and include the short endpoint corrections,
bounded by length times a range bound, with signed orientation. When the
endpoint is singular, use an integrable majorant instead of a finite
supremum. Increasing quadrature degree cannot fix endpoint uncertainty.

## Adaptive search, error control and checking

Native search is untrusted; the kernel checks a compact final certificate.
Use a mutable array-backed binary heap with the largest current error first;
retain the cheaper stack strategy as a measured alternative for easy cases.
Compile/reify the body once, share constants and common subexpressions, and
use real arithmetic for real quadrature samples. Bound the complex extension
only for ellipse tests.

Search several ellipse sizes before evaluating quadrature samples. Predict
the needed degree with cheap approximate logarithms, round up to a cached
degree, and verify the error inequality with outward arithmetic. Sample only
the chosen rule. Failed analytic-domain checks trigger subdivision.

Candidate optimization: dyadic rho values give exact dyadic semiaxes
(rho+1/rho)/2 and (rho-1/rho)/2 when rho is a power of two, avoiding square
roots in ellipse geometry. Also compare FLINT's X-based search: the changed
domain sizes can change the number of function evaluations. Keep whichever
wins for the relevant workload. A small bounded-precision magnitude type
is another candidate for cheap upper bounds and degree search.

Keep a **global** enclosure/error budget, including:

- quadrature remainder on all leaves;
- node/weight and function-evaluation uncertainty;
- interval summation roundoff;
- uncertain endpoints;
- truncated endpoint strips and infinite tails.

FLINT's local tolerance/status is a search guideline, not a theorem that
the final sum meets a strict user tolerance. In Lynth, success requires
checking the **complete returned enclosure** against the requested rational
witness and strict inequality. Use balanced accumulation; require slack.
If rounding dominates, raise precision and replay the current partition
before adding more panels. Severe cancellation and tiny relative targets
need guard bits. Pure relative accuracy near zero may remain undecided.

Certificate shape: shared node-table certificates plus a binary partition
whose leaves are direct bounds, analytic GL panels, or independently
certified endpoint/tail estimates. The checker verifies geometry, branch
conditions, arithmetic, integrability, additivity and the final enclosure.
It does not replay unsuccessful searches.

Integration uses the existing kernel/native/auto trust driver with an estimate
of root, analytic-bound and sample costs scaled by precision. Large checks in
auto mode use native_decide; its per-declaration auxiliary axioms are recorded
explicitly in the tests. Setting lynth.interval.trust to "kernel" requests
kernel replay. The 25 migrated original cases were also checked through the
kernel path before enabling the cost estimate; expensive cases exceeded the
60-second per-declaration target.

The user explicitly authorized temporary sorry proofs on 2026-10-17; migrated
tests consequently expect sorryAx. No checker result is assumed using sorry.
Mathematical statements and Ival bridge proofs remain placeholders until
proofs are supplied.

## Improper integrals and divergence

The current Integrals.lean already requires these, so they are part of the
requested scope, not a distant optional feature.

Use finite GL integration plus a library of certified majorants:

- Gaussian tail <= exp(-R²)/(2R), R>0; use the integration-by-parts
  recurrence for polynomial times Gaussian tails.
- Polynomial times exp(-x): exponential times a finite polynomial, evaluated
  by a scaled recurrence/Horner scheme.
- Reciprocal-square tails <= C/R; general power tails use p>1.
- sech tails: (2^k/k) exp(-kR) for sech(x)^k, k>=1 and R>=0.
- Logarithmic endpoints: integral_0^eps |log x| = eps(1-log eps).
- Algebraic endpoint bounds C x^alpha with alpha>-1.

Tail contracts must establish integrability as well as an error estimate.
Choose truncation points by cheap estimates and verify their bounds.
Use substitutions where they improve conditioning while retaining GL;
for x^4/sqrt(1-x²), x=sin(theta) removes the endpoint singularities.
For reciprocal-phase oscillation, use the cancellation estimate
`|integral_0^delta x^n sin(omega/x)| <= 2 delta^(n+2)/|omega|` for nonzero
omega and natural n. It establishes integrability and lets direct panels
discard a much larger endpoint strip. Global sine bounds remain the fallback.

For non-integrability use proved local comparisons against C/x or power
laws with exponent <=-1 at an endpoint, and harmonic/power comparisons at
infinity. Supply the tangent pole argument. Mathlib already proves basic
reciprocal/power integrability criteria. Periodic functions with a positive
integral of their absolute value over one period give the sine-tail
non-integrability test; a pointwise inverse lower bound is insufficient
because sine has zeros. Failure, timeout, a branch cut or
an infinite interval enclosure must return unknown, never divergence.

The test notion is Lebesgue integrability. In particular, an odd principal
value for 1/x on [-1,1] is not convergence in these goal types.

## Coverage of the requested examples

| Input family | Requirement |
|---|---|
| Integrals.lean T15-T17 | Proper real GL, pi endpoint corrections, rational witnesses, integrability |
| Integrals.lean T18-T19, T21 | Certified non-integrability for reciprocal, tangent and harmonic tail |
| Integrals.lean T20 | Finite Gaussian quadrature plus tail and half-line integrability |
| ImproperIntegrals IC01-03, IC08 | Same proper engine; polynomial exactness and narrow-peak adaptation |
| ImproperIntegrals IC04-07 | Exponential/Gaussian tails, endpoint substitution, logarithmic endpoint |
| ImproperIntegrals ID01-10 | Local/tail comparisons, interval normalization and set restriction |
| ImproperIntegrals IC09 | Separate finite-sum/Fubini reduction for the ten-dimensional cube; avoid tensor quadrature |
| FLINT 0,1,4,10,12,13,15,31,32 | Finite elementary GL; oscillation, cancellation, large/small magnitudes, narrow peaks |
| FLINT 3,5,6,8,9,16,24,27 | Bounded endpoint singularities and piecewise extensions; floor/abs/max, direct residual strips |
| FLINT 2,14,17,18,19,20 | Elementary improper integrals with verified explicit truncation |
| FLINT 25,26,30,37 | Implemented real erf, Airy and Si evaluators, analytic bounds and Airy tail |
| FLINT 23,33,34,36,38 | Remaining real special-function evaluators and domain/tail certificates |
| FLINT 7,11,21,22,28,29,35 | Complex-valued integrands/paths and branch-aware extensions |

These groups partition the 39 FLINT cases. There are 32 real-valued cases;
the remaining seven cannot all be expressed as a Real-to-Real API.
Retain a complex-valued panel core so they can be supported without changing
the integration algorithm. Parameterize straight complex segments by a
real t, including the complex path derivative. Piecewise paths compose.

Additional special-function work is substantial and separate from GL:
Lambert W, ordinary and scaled modified Bessel evaluators;
reciprocal Gamma across its removable zeros; and zeta derivative/quotient,
Weierstrass p and Hardy theta for the contour examples. Gamma/zeta numerical
support exists; the general pFq interval evaluator is currently real-valued.
Bessel I has a project definition but lacks the required fast certified
scaled complex evaluator. Avoid unscaled exp(-x)*I_0(x/k)^k at large x:
the scaled evaluator is needed for useful enclosures.

The current complex sqrt evaluator only handles the right half-plane.
The negative-axis contour cases 28 and 35 require a broader evaluator:
certify each side of the cut and use a bounded direct enclosure for a
short crossing piece. Merely registering its analyticity would not suffice.

Source discrepancies to resolve when porting benchmarks:

- FLINT 30's description and tail concern exp(-x) Ai(-x), but the local
  f_exp_airy callback calls acb_exp(t,z), giving exp(+x) Ai(-x). Record the
  intended mathematical benchmark and correct this discrepancy explicitly.
- FLINT 32's executable callback is sin((0.001+(1-x)^2)^(-3/2)).
  Its description string places the power outside sin. Follow the callback
  formula when defining this benchmark and document the corrected label.

## Implementation order and reviewable milestones

| Step | Deliverable | Acceptance gate |
|---|---|---|
| 1 | Mathematical GL foundation; hybrid Legendre evaluators, certified node/weight cache | Root brackets, symmetry, weights, polynomial exactness, all evaluator regimes and rounding contracts |
| 2 | Measurable/analytic extension capabilities; panel checker and global assembler | Single-panel tests, near poles and branch cuts, inexact/reversed/zero endpoints |
| 3 | Adaptive native search and Integral goal handler | T15-T17 plus unrelated analytic/oscillatory/peaked functions; strict tolerance and axiom checks |
| 4 | Endpoint/tail capability and proof-producing divergence | All current T15-T21, real one-dimensional improper tests and elementary FLINT groups |
| 5 | Special-function capabilities and complex segment composition | Remaining real special-function cases, then the seven complex cases with their own prerequisites |
| 6 | Benchmark tuning and optional Fubini normalization | Measured performance across precisions, preserved proof footprint, ten-dimensional separable test |

Proposed modules under Lynth/Interval:

- Integral/Math/{Legendre,GaussError,Bounds,Improper}.lean: imported proofs.
- Integral/Legendre/{FixedPoint,Series,Asymptotic,Roots,Cache}.lean.
- Integral/{Analytic,Measurable,Panel,Cert,Search,Tail,Divergence}.lean.
- Goals/Integral.lean, dispatched before generic rational witness handling.
- Fns companion extension registrations, reusing existing evaluators.

Recognize subtypes with integrability conjuncts, PSum alternatives, and
user-defined two-constructor results such as IntegralAnswer and
IntegralAnswerOn structurally through constructor types. Do not hard-code
the test namespace or infer a divergence constructor from numerical failure.
Initially handle integral goals directly; then add a certified integral
expression node if nested closed arithmetic expressions require it.

## Proof handoff and validation

Prepared in /tmp/intgrl:

| File | Purpose | Dependencies beyond Mathlib |
|---|---|---|
| IntgrlDefs.lean | Small mathematical definitions | None |
| Legendre.lean | Roots, weights, positivity, exactness | IntgrlDefs |
| GaussError.lean | Ellipse geometry and analytic GL error | IntgrlDefs |
| LegendreEval.lean | Stable fixed-point contract, derivative bounds, fast series/asymptotics | IntgrlDefs |
| RootRefinement.lean | Sign brackets, Newton preservation, derivative transport | None |
| IntegralBounds.lean | Direct/partition bounds, endpoints, tails, substitution | None |
| Divergence.lean | General inverse comparisons and tangent pole | None |
| Integrand.lean | Small expression/region definitions, measurability, holomorphicity, real agreement | None |
| FixedPoint.lean | Delayed-division integer Bonnet evaluation and error contract | IntgrlDefs, LegendreEval |
| DivergenceRules.lean | Recognized analytic non-integrability rules | Integrand, Divergence |
| Tails.lean | Tail expressions and half-line/whole-line assembly | Integrand, IntegralBounds |

Definitions are small and copyable. No file imports Lynth or its registry,
interval types, tactic machinery, Gamma implementation or pFq development.
Lynth-specific evaluator/certificate plumbing stays in the project.
The theorem files deliberately contain sorry: elaboration checks statement
syntax/types only, not mathematical truth or completed proofs. Proofs must
replace these placeholders and pass axiom checks before removing sorryAx
from the integration tests. The user authorized importing the placeholders
during implementation.

Validation of the eventual engine should include all 39 correctly specified
FLINT cases at representative precisions (64,128,256,1024,4096 bits), cold
and warm node caches, and separate search/checker timings. Report panel
counts, analytic-bound calls, real sample calls, precision retries, node
generation cost, proof size and axiom footprint. Include cases where limits
are insufficient: they must return unknown with no fabricated proof.
No implementation speed or FLINT timings are claimed by this investigation.

Primary references:

- [FLINT calculus documentation](https://flintlib.org/doc/acb_calc.html).
- [Johansson: Numerical integration in arbitrary-precision ball arithmetic](https://arxiv.org/abs/1802.07942).
- [Johansson and Mezzarobba: Fast and rigorous arbitrary-precision computation of Gauss-Legendre quadrature nodes and weights](https://arxiv.org/abs/1802.03948).
- [Trefethen: Is Gauss Quadrature Better than Clenshaw-Curtis?](https://people.maths.ox.ac.uk/trefethen/publication/PDF/2008_127.pdf).
