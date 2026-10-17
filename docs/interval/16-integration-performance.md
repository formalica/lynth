# Integration performance work, 2026-10-17

This log records two passes. The second-pass changes and results follow the
historical first-pass measurements below.

The first optimization pass targets numerical search and repeated interval
evaluation. The earlier investigation found that these dominate the slow
FLINT examples; checking the final theorem applications is much cheaper.

## Changes

- Specialize only operations that need a real branch decision. Cache the
  specialized expression per pending panel and share it across ellipse trials.
- Keep the selected Gauss remainder instead of recomputing the analytic bound
  during search. Certificate replay still recomputes it independently.
- Share the unused enclosure-width budget among pending panels. Retain the
  previous length-based allowance as a lower bound. Every accepted answer
  still passes the full strict absolute-error checker.
- Choose an initial precision from the requested tolerance and five sampled
  integrand magnitudes. This is an untrusted hint; small-valued integrands
  can retain low precision. Case 12 starts at 384 bits instead of spending
  its budget on an impossible 64-bit roundoff target.
- Reuse the replayed enclosure when selecting a rational witness, removing
  one full numerical replay. The authoritative certified check remains.
- Allow large real sine/cosine phases, with a representation-size work guard.
  Growth in the imaginary component retains its magnitude guard.
- Evaluate half-integer powers through square roots and integer powers.
  The new real and complex enclosure lemmas in `Integral/Powers.lean` have
  checked proofs, including negative exponents.
- Specialize inverse cosh as `2t/(1+t²)`, choosing the decaying exponential
  on each real panel. Also use `cosh(x) ≥ 1` in real range evaluation.
- Quote long certificate lists with balanced append trees and short literal
  chunks, reducing expression depth without changing certificate data.

These are general expression/search changes. No integral answer is inserted
as a closed-form rule. Default kernel/native trust selection is unchanged.
The pre-existing authorized mathematical/adapter proof placeholders remain;
there are no new `sorry` declarations in this optimization pass. The inverse
cosh rewrite extends the contract of the existing `specialize_sound` adapter.
Both real rewrite identities were also proved in the Mathlib-only helper
`/tmp/intgrl/HyperbolicRewrite.lean` for the proof handoff.

## First-pass results

Each case ran in a fresh process with its original statement and tolerance.
The 90-second timeout includes imports. Successful goal times exclude imports,
include numerical search, certificate checking and theorem elaboration, and
use synchronous declaration checking (`Elab.async = false`). Timings are
approximate: some validation jobs overlapped on the same host.

| FLINT case | Before | Goal after changes | Process after changes |
|---|---|---:|---:|
| 9: `x sin(1/x)`, error `10⁻⁵` | timeout at 90 s | 19.0 s | 28.1 s |
| 12: cancellation, error `10⁻⁹²` | timeout at 90 s | 34.7 s | 42.3 s |
| 15: three inverse-cosh peaks, error `10⁻⁵` | timeout at 90 s | 26.9 s | 35.3 s |
| 8: `sin(1/x)` | timeout at 90 s | still exceeds budget | timeout at 90 s |
| 16: fractional exponential times sine | timeout at 90 s | still exceeds budget | timeout at 90 s |
| 32: sine of a negative half-integer power | timeout at 90 s | still exceeds budget | timeout at 90 s |

Case 9 uses 21 panels instead of 2,041 in the original extended run. Case 12
uses one 182-node panel at 384 bits. Case 15 uses 16 panels at 64 bits.
The general search/evaluation changes were benchmarked for 8 and 16; the
subsequent inverse-cosh/half-integer paths do not occur in those integrands.
Case 32 was rerun with the half-integer path and still timed out.

Cases 9, 12 and 15 are now regression declarations in
`Test/IntervalArith/Integrals.lean`, including integrability, absolute error,
axiom footprints and numerical witness guards. `IntegralOptimizations.lean`
adds smaller end-to-end tests for the large-phase and both half-integer paths.
No timed-out case is added to the passing suite.

## First-pass validation and artifacts

`lake build Lynth` and the four existing integration suites passed with their
original heartbeat caps after the implementation changes. Counts are then
remeasured with Mathlib's `#count_heartbeats in` on temporary source copies;
each final cap is `ceil(105 * count / 100)`. Heartbeats track Lean allocation
work and do not impose a native computation wall-clock limit.

All five integration test modules passed with the updated caps: `Integrals`,
`ImproperIntegrals`, `NestedIntegrals`, `NestedCertificates` and
`IntegralOptimizations`. All 77 per-case caps match the fresh Mathlib counts
and the exact requested 5% margin. `git diff --check` also passed.

Original investigation: `/tmp/lynth-integral-profile/REPORT.md`.
Optimization probes, logs, JSON timings, old-cap validation and heartbeat
measurements: `/tmp/lynth-integral-opt/`. These scratch paths are local
artifacts; the regression specifications and measured caps live in the repo.

Remaining priorities are faster elementary interval kernels, oscillatory
endpoint tail bounds for case 8, and better handling of the thousands of
floor discontinuities in case 16. Case 32 still needs fewer or cheaper
oscillatory panels. These cases have supported syntax but remain too slow
for the current benchmark budget.

## Second-pass changes

The second pass replaces the elementary sine, cosine and exponential series
loops used by integration with integer fixed-point endpoint arithmetic.
Reduced arguments are rounded once; each term uses directed integer division
and the uncomputed tail has a geometric bound. Tiny sine arguments retain
the original relative-precision kernel. General quadrature remains Petras
with Gauss–Legendre panels.

The point-kernel microbenchmark evaluates 1,000 arguments at each precision:

| Kernel | 64-bit original / fixed | 384-bit original / fixed |
|---|---:|---:|
| sine | 874 / 57 ms | 5,332 / 163 ms |
| exponential | 1,454 / 143 ms | 8,188 / 286 ms |

These are point-kernel measurements, not whole-integral speedups. Dense
checks compared 1,616 enclosures with 300-digit mpmath values. The new
`IntegralKernelCertificates` tests independently compare fixed-point bounds
with exact rational series enclosures (75 cases), and binary Gauss remainder
bounds with the exact rational formula (144 cases).

Other numerical changes:

- Use `exp(|Im z|)` for complex sine/cosine moduli and `exp(Re z)` for an
  exponential modulus. Product bounds compose without evaluating the real
  oscillatory phase. These modulus inequalities have completed proofs.
- For binary ellipse parameters, compute the Gauss remainder with exact
  binary scaling and one directed scalar division. Degree trials share the
  base coefficient; they no longer repeat interval exponentiation.
- Use dependency-aware complex squares and avoid multiplication by one for
  small powers. All new complex power enclosure lemmas have checked proofs.
- Share evaluation of `a - floor(a)` and intersect it with `[0,1]`. Around
  `floor(exp x)` jumps, split using rigorous logarithm brackets and replay
  both smooth sides and the narrow intervening band normally.
- Reuse a cached rule of at most twice the requested degree for its first
  eight requests. Frequently requested degrees receive their own table.
  Recursive integration retains its original table selection. The certified
  checker always uses the actual table and recomputes its error.

The cached-rule change fixes a heartbeat regression detected during the
pass: the half-line arctangent briefly grew to 3,422 heartbeats and exceeded
its old 2,923 cap. The corrected search uses two tables instead of five and
measured 2,342 heartbeats in the full-file measurement. Its old cap passes.

## Second-pass results and proof status

FLINT 32 now completes with 371 panels at 64 bits. The final run measured
69.6 seconds for the goal and 78.9 seconds including imports; an earlier
separate run measured 67.5 and 76.7 seconds. This passes
the 90-second investigation budget but remains above the earlier 60-second
per-declaration target. Its original interval, integrand and `10⁻⁵` tolerance
are preserved in the new `nearEssentialSin` regression.

| FLINT case | First-pass goal | Final goal | Final process |
|---|---:|---:|---:|
| 9 | 19.0 s | 8.4 s | 17.5 s |
| 12, error `10⁻⁹²` | 34.7 s | 16.6 s | 25.5 s |
| 15 | 26.9 s | 9.2 s | 17.7 s |
| 32, error `10⁻⁵` | timeout at 90 s | 69.6 s | 78.9 s |

Intervals and tolerances are unchanged. Some measurements overlap other
validation processes; use the recorded heartbeat counts for exact per-case
regression thresholds.

FLINT 8 and 16 still exceed 90 seconds. The short `[0,2]` jump-isolation
regression is explicitly separate from FLINT 16 on `[0,8]`; it does not
claim to solve the full case.

A new stage probe of FLINT 16 spent the remaining 80-plus seconds after
imports in its first 64-bit numerical search, without reaching enclosure
replay or final proof certification. Repeated expression evaluation and
handling many discontinuities remain the immediate targets there.

This pass adds two authorized generic mathematical proof placeholders:
`fixedTrigBounds_sound` and `fixedExpBounds_sound`. Their definitions and
statements are in `/tmp/intgrl/FixedTrig.lean` and `FixedExp.lean`, with only
Mathlib imports. `/tmp/intgrl/ComplexMagnitude.lean` contains completed
modulus proofs. All 18 portable packet modules typecheck. The pending count
is now 76 Mathlib-only obligations; the existing 19 project adapters remain.
Per-problem integrability/error proof construction and the kernel/native
trust policy are retained.

Second-pass probes, exact-reference checks, timings, old-cap failures and
their fixes, final heartbeat counts and build logs are retained in
`/tmp/lynth-integral-opt2/`.

Final validation passed: `lake build Lynth`, all six integration test modules
(82 test declarations/groups), all 18 portable packet modules, and
`git diff --check`. Every case has its own newly measured
`ceil(105 * heartbeats / 100)` cap. All fresh counts for pre-existing cases
are below their previous caps; the arctangent also passed its old hard cap
after the regression fix. The six final test modules pass their updated
hard caps.


## Third-pass implementation

The native numerical backend now uses Lean's `Nat.log2` runtime primitive
for mantissa bit lengths. A compiler-simplification equality preserves the
existing bounded binary-search kernel definition, including its 65536-bit
cap. Directed shifts also have proved compiler rewrites. Microbenchmarks
caught an allocation regression for negative `Int` bit shifts: left shifts
allocated 1000 versus 400 heartbeat units per 100,000 calls, and right shifts
700 versus 400. The final hybrid uses GMP arithmetic for negative values and
bit shifts for nonnegative values. The first version's nested-test cap
regressions are retained in `/tmp/lynth-integral-opt3/pre-hybrid-heartbeats.json`.

`Integral/Memo.lean` adds local common-subexpression evaluation with completed
cache-invariant and enclosure proofs. A prepared evaluator selects caching
only when an expensive subexpression repeats; every quadrature input starts
with an empty cache. This shares the exponential across the fractional part
and sine phase of FLINT 16. Small natural powers use direct formulas, and
complex square roots share the real component with the imaginary-component
calculation. The new power and square-root adapter proofs are complete.

Search returns an untrusted enclosure estimate alongside its certificate.
Witness selection uses that estimate and no longer replays the entire
partition first. The authoritative checker still independently verifies the
nodes, weights, partition, analyticity, samples, remainders and final error.
Improper and endpoint-transform estimates include the same tail allowances.
No assertion is attached to the search estimate.

Reciprocal-phase endpoint panels use a generic integration-by-parts bound
for `x^n sin(omega/x)`, including negative frequency. The interval adapter is
proved and composes that theorem into the existing direct-panel proof.
The general quadrature method is still Gauss-Legendre/Petras.

FLINT 16 originally completed numerical search in about 56 seconds but failed
native compilation at `maxRecDepth = 10000`. Constructor backtracking could
repeat that search and consume the process budget. Large certificate lists
are now compiled as checked constant chunks of 64 panels. This keeps the
checker declaration small and completes certification at the existing depth
limit. These constants carry data only; the final numerical check remains.
The large-case axiom regression checks the complete permitted set plus
exactly one native-decide axiom belonging to that declaration. Its generated
numeric suffix varies between ordinary asynchronous elaboration and the
synchronous Mathlib heartbeat wrapper, so that suffix is not compared.

Two generic proof obligations are added in Mathlib-only packets:
`BitLength.lean` (bounded-search/native bit-length equality) and
`Oscillatory.lean` (integrability and endpoint cancellation). There are 78
pending portable obligations and the existing 19 project adapter gaps.
All 20 portable modules elaborate with their expected sorry warnings.
The runtime regression groups compare native bit lengths with the original
bounded search, signed shifts with exact arithmetic, and cached evaluation
with ordinary evaluation on multiple precisions and input boxes.

The search estimate also retains endpoint uncertainty when distinct endpoints
have the same rounded midpoint. A regression with endpoints differing by
10^(-100), tolerance 10^(-110), now retries to 384 bits in the one-dimensional
engine rather than failing a doomed low-precision certification.

## Third-pass measurements

Fresh processes use the original statements and tolerances with synchronous
declaration checking (`Elab.async = false`). Goal times include search,
numerical certification and proof elaboration; process times include imports. Some runs overlapped validation jobs, so timings are approximate.

| FLINT case | Second-pass goal | Third-pass goal | Process |
|---|---:|---:|---:|
| 8 | timeout at 90 s | 3.4 s | 12.2 s |
| 9 | 8.4 s | 1.4 s | 9.4 s |
| 12, error 10^(-92) | 16.6 s | 5.3 s | 13.5 s |
| 15 | 9.2 s | 3.6 s | 12.6 s |
| 16, original [0,8] | timeout at 90 s | 80.8 s | 89.9 s |
| 32 | 69.6 s | 24.6 s | 34.9 s |

Case 8 uses 32 panels, case 9 uses 10, case 16 uses 5,959, and case 32
retains 371. Case 16 completes within the investigation budget but is close
to its 90-second process limit and remains above the earlier 60-second goal
target. Faster elementary interval arithmetic and more efficient handling
of many discontinuities remain worthwhile. Final kernel proof checking was
not separately reprofiled for these final timings; native certification
includes numerical replay and compiler work.

This pass measured 88 integration declarations/groups: 27 main integrals,
22 improper integrals, 23 nested integrals, five nested rejection groups,
six optimization regressions and five numeric-kernel validation groups.
Every cap is exactly ceil(105 * freshly counted heartbeats / 100).
All pre-existing cases have measured counts within their prior hard caps;
the negative-shift regressions were fixed rather than covered by larger
budgets. The 88 source caps were independently checked against the saved
Mathlib counts.

The new generic proof packets and all previous portable modules typecheck.
Benchmarks, stage logs, regression measurements, primitive microbenchmarks,
exact cap records and build logs are in `/tmp/lynth-integral-opt3/`.


Final validation passed: `lake build Lynth`, all 23 modules in
`Test.IntervalArith` (including all 88 integration declarations/groups at
fresh measured-plus-5% caps), all 20 portable proof packets, and
`git diff --check`. The last main-file recount moved a few measurements by
one or two heartbeats; their exact caps were updated and the complete target
passed again. Final records are `final-heartbeats.json`, `final-results.json`,
`final-validation.json` and `final-cap-build.log` in the artifact directory.


### Regression classification

Cases 8 and 32 remain in `Test/IntervalArith/Integrals.lean`. Full case 16
moves to `TestFailures/IntervalArith/Integrals.lean` because of its runtime;
its statement, axiom check, numerical result guard and measured +5% heartbeat
cap are preserved. The passing suite now contains 87 integration checks,
including 26 main integrals; case 16 is retained separately as a performance
regression. The 88-case measurements above include that retained case.
