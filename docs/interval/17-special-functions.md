# Special-function evaluation and real integration

Public functions are `Real.erf`, `Real.Si`, `Real.dirichletEta`,
`Real.airyAi` and their `Complex` counterparts. Both sets are defined in
`Lynth/Analysis/SpecialFunctions.lean`, with Mathlib as their only dependency.
The sine integral has its removable value at zero; eta is continued through
one with value `log 2`. These are separate real and complex definitions.

## Evaluation

Real power series run an integer loop with two directed endpoints. Complex
power series have a separate loop with four endpoints. A real evaluation
never constructs or evaluates a complex box. Both loops include a checked
geometric tail and return no enclosure if the work budget is exhausted.
They use extra working bits to account for cancellation. These series are
function-evaluation algorithms; integration remains Petras/Gauss–Legendre.

Real erf uses oddness, a power series near the origin, and the Gaussian
tail at large arguments. Real Si uses oddness, a convergent series, and a
Laplace-integral asymptotic expansion with an explicit remainder at large
arguments. Airy Ai uses its two entire series and certified Gamma-based
normalizing constants. The common path caches rational constant bounds;
higher working precision falls back to Gamma evaluation.

Eta uses a finite Euler transform of its alternating Dirichlet series.
The weights are generated in linear time and lie between -1 and 1; the
implementation does not form large cancelling binomial sums. Integrating
by parts in the finite-difference Laplace representation gives a uniform
error estimate for arbitrary real part. The real path needs no complex
Gamma computation. The complex path bounds the Gamma ratio through its
Weierstrass product. This handles boxes crossing zero or one.

Function records give the trust driver an evaluator cost, in addition to
expression size. The new large kernels select native checking in default
auto mode. Explicit `lynth.interval.trust = "kernel"` remains available.
The generated theorem still composes enclosure, registry and problem proofs.

## Real integration

The univariate compiler recognizes all four functions, including compositions.
Real Gauss nodes use the real evaluators. Ellipse bounds use separate complex
bounds, with phase-independent bounds for erf/Si and vertical ODE transport
for Airy. Eta uses a local analytic bound around one when available and a coarse
Euler-transform magnitude bound elsewhere; it does not run a precise eta
evaluator to choose an ellipse. The
exponentially damped Airy tail is bounded by exp(-R), using |Ai(x)| <= 1 on
the real axis. Nested expression memo keys include the four new operators.
Complex contour integration is outside this change.

## Proof handoff and tests

Hard mathematical results are provisional `sorry` contracts in the three
portable modules mirrored as `/tmp/intgrl/SpecialFunctions.lean` and
`SpecialKernel.lean`, plus `SpecialBounds.lean`. The last two import just the
first, which imports
only Mathlib. The interval arithmetic adapters, registry soundness and
integration proof construction have no new project-dependent placeholders.
The updated portable Integrand/Tails packets include the four operators and
the Airy tail model. Test declarations contain no per-problem placeholders.

`Test/IntervalArith/SpecialFunctionValues.lean` checks real values, nonreal
complex values, rational complex arguments, large real arguments, eta at
zero/one and a composition involving all four functions.
`SpecialFunctionIntegrals.lean` includes elementary interval checks, eta
across zero/one and FLINT examples 25, 26, 30 and 37 at their original domains.
Each test has a separate measured heartbeat cap, set to ceil(1.05*count).
Heartbeat counts bound Lean work; native execution also needs wall timings.
Reference numbers were computed independently with mpmath and cross-checked
against the compiled FLINT examples.


## Measured integration regressions

| Test | Heartbeats | Cap (+5%) |
|---|---:|---:|
| erfUnit | 710 | 746 |
| siUnit | 612 | 643 |
| airyUnit | 771 | 810 |
| etaRange | 15,335 | 16,102 |
| erfBent | 3,806 | 3,997 |
| airyRange | 4,289 | 4,504 |
| airyDamped | 5,059 | 5,312 |
| siRange | 10,400 | 10,920 |

The separate eta integral process took 17.7 seconds including Lean startup,
compared with 60.9 seconds before replacing accurate complex ellipse evaluation
with the coarse analytic magnitude bound. Initial standalone FLINT 25/26/30/37
processes took 9.4/9.8/10.6/15.4 seconds, including Lean startup. The complete
8-case Mathlib heartbeat recount took 28.3 seconds. These are local process
timings, not kernel-only or cross-machine benchmarks.

Validation artifacts, reference values, the final cap records and a script
for repeating the Mathlib heartbeat recount are in `/tmp/lynth-special/`.
The 27 numeric tests include a complex eta argument close to a negative
integer. Both new files check that every generated problem proof depends
on the expected generic mathematical placeholders and exactly one native
computation axiom. An independent forced-kernel erf-zero check adds no
native axiom. All 23 portable packets elaborate; there are 17 new generic
mathematical obligations, with no new Lynth-dependent proof placeholders.

Final validation passed: `lake build Lynth`,
`lake build Test.IntervalArith Test.ComplexIntervalArith`, all 35 new tests
at their measured caps, the expected axiom guards, the independent forced
kernel check, all 23 portable modules, and `git diff --check`. All existing
caps were retained. Final records are `final-heartbeats.json` and
`final-validation.json` in the artifact directory.
