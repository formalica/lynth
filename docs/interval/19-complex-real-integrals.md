# Complex-valued integration over real variables

The complex integration handler accepts ordinary Mathlib interval and set
integrals `ℝ → ℂ`. Integration variables and their bounds remain real, including
bounds that depend on outer real variables. This does not add contour integrals
with a complex integration variable or conditionally convergent improper limits.
A contour already parametrized by a real variable is accepted in that form.

```lean
import Mathlib
import Lynth

open MeasureTheory

-- The result includes ordinary complex interval integrability and a norm error.
example : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) volume 0 1 ∧
    ‖(∫ x in (0 : ℝ)..1, Complex.exp ((x : ℂ) * Complex.I)) -
      ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 10000} := by
  lynth
```

## Compilation and certificates

`ComplexReify` reconstructs an equality from the user's function to `CExpr`, a
small mathematical syntax with real binder levels and complex values. Its
supported operations are real casts, `I`, arithmetic, natural powers, `exp`,
`sin`, `cos`, `sinh`, `cosh`, principal `log` and `sqrt`, powers with exponent
`1/2 : ℂ`, and complex powers with a positive rational constant base. Real
functions inside a real cast retain the real integration engine's vocabulary.

The mathematical projection produces two real `NExpr` expressions. Each
component is independently searched and checked by the existing real
Gauss–Legendre/Petras engine. Every successful result carries convergence and
an absolute error certificate for both components. Their sum bounds the complex
norm error. The final testcase proofs are reconstructed theorem applications;
no testcase solution is admitted.

Recursive convergence is retained when arithmetic could otherwise erase an
inner integral, for example multiplication by zero. Projection commutes with
Bochner integration only after convergence of both components is established.
The ordinary Mathlib default-zero value of a divergent integral is not used as
an approximation certificate.

The real numerical algorithms remain separate from complex expression
compilation. The scalar endpoint evaluator gains logarithmic growth envelopes,
sign-preserving bounds for `log(t)`, and a first-order bound for `log(1-t)`.
The local interval adapters for these additions have proofs.

## Reductions and branches

Before quadrature, a mathematical syntax transformation applies linearity and
exact affine-phase primitives for exponential and trigonometric integrands.
This makes long oscillatory affine phases and their separable iterated forms
cheap. Every reduction transports convergence and the integral's value back to
the original expression.

Principal square roots and logarithms preserve Mathlib's upper-side convention
on the negative real axis. A real binder's branch step can be resolved on each
side of zero with an exact interval split. Unit-interval logarithm signs can
also be resolved. These changes affect only null endpoints and are restricted
to bodies without remaining recursive integrals. The square root of a
reciprocal and the reciprocal of a square root retain their different imaginary
signs on negative real inputs.

Complex analytic bounds for real `arctan` are enabled on boxes with imaginary
part strictly between -1 and 1. This provides Gauss–Legendre error bounds for the
real argument formulas used by complex logarithms.

`lynth.interval.complexIntegralSteps` bounds subdivisions and recursive integral
searches per component (default 16384). `lynth.interval.maxPrec` retains its
existing meaning. These are search controls; the checker independently verifies
all accepted certificates.

## Proof handoff

The mathematical obligations are copied under `/tmp/intgrl`:

- `ComplexIntegral.lean`: `CExpr.parts_sound`.
- `ComplexReduction.lean`: `NExpr.reduceComplexIntegral_sound`.
- `ComplexEndpoint.lean`: `real_sqrt_log_scaled`,
  `real_log_log_scaled_bound`, `real_log_one_sub_div_bounds`.

`ComplexClean.lean` and `ComplexBranch.lean` contain pure supporting definitions.
The bundle imports Mathlib and the small mathematical syntax modules; it imports
no numerical interval types, search, certificates, or tactic implementation.
The existing three unfinished internal nested-integral adapter proofs remain
separate from these new mathematical obligations.

## Measured coverage

The passing test file contains twenty numerical declarations and two checks that
recursive convergence is retained. Ten numerical declarations are the supplied
NIntegrate examples; the others cover dependent bounds, orientation, equal
endpoints, finite set integrals, whole-line Gaussians, aliases, kernel trust, and
the two reciprocal/square-root branch conventions. Each mathematical test
includes ordinary integrability and a complex norm error below `10⁻⁴`.

Measurements use Mathlib's `#count_heartbeats in` on copies of the actual test
commands. The test files omit that wrapper, which disables limits. Limits are
exactly `ceil(105 * measured / 100)` for every declaration. The passing tests
use 64-bit arithmetic and a 512-step native search budget; the known failures
use a 16-step search budget to keep repeated unsuccessful runs bounded.
Heartbeats count elaboration/kernel allocations; native wall time also depends
on the search budget and is not bounded by maxHeartbeats alone.

| Item | Declaration | Status | Heartbeats | Cap |
|---|---|---|---:|---:|
| 4 | `circular` | passes | 26466 | 27790 |
| 5 | `logLog` | passes | 29286 | 30751 |
| 6 | `sqrtLog` | passes | 14841 | 15584 |
| 10 | `sqrtCut` | passes | 5499 | 5774 |
| 11 | `logCut` | passes | 50505 | 53031 |
| 13a | `oscExp` | passes | 4680 | 4914 |
| 13b | `oscPower` | passes | 8119 | 8525 |
| 15a | `gaussianExp` | passes | 14422 | 15144 |
| 15b | `gaussianPower` | passes | 15299 | 16064 |
| 18a | `doubleExp` | passes | 5307 | 5573 |
| 7 (=22–24) | `inverseSqrtSin` | TestFailures | 2542 | 2670 |
| 8 | `shiftedSqrtLog` | TestFailures | 3216 | 3377 |
| 9 | `inverseSqrtCosXY` | TestFailures | 2582 | 2712 |
| 12 | `sqrtSquare` | TestFailures | 2870 | 3014 |
| 18b | `doublePower` | TestFailures | 8418 | 8839 |
| 21 | `inverseSqrtSinXY` | TestFailures | 3136 | 3293 |
| 25 | `sqrtReciprocalTrig` | TestFailures | 3435 | 3607 |

The remaining limitations are:

- Items 7, 9, 21, 25: algebraic singularities inside intervals or moving along
  two-dimensional curves require further partitioning and remainder bounds.
- Item 8: the shifted complex logarithm requires additional interior branch-point
  endpoint bounds.
- Item 12: the square root over a square needs stronger parametric bounds through
  the branch cut, including cancellation in the component square-root formula.
- Item 18b: the exact inner primitive is available, but the remaining outer
  high-frequency cancellation needs a stronger oscillatory algorithm. An early
  512-step attempt reached the 90-second wall timeout.
- Item 17: `Complex.besselJ` does not exist in this installed Mathlib version,
  and Lynth has no Bessel-J evaluator. No statement using an undefined symbol
  was added.

The failure statements contain the original domains and functions and a real
`lynth` attempt. They have no admitted problem-specific solution proofs.

Measurement and diagnostic logs are in `/tmp/lynth-complex-integrals/`:
`count-passing-final.log`, `count-signs.log`, `count-failing-final.log`,
`heartbeats.json`, and the per-example `.log`/`.json` files. The isolated handoff
check is recorded in `portable-isolated.log`.

## Validation

`lake build Test.IntervalArith Test.ComplexIntervalArith` passed (18,628 jobs).
All existing heartbeat caps are unchanged. The 22 new passing declarations
passed with their individual measured caps, including the forced-kernel case
whose axiom footprint contains no native checker axiom. The seven failure
statements still fail by ordinary solver rejection, with no heartbeat, parser,
unknown-symbol, or kernel type-checking errors.

All fourteen files in `/tmp/intgrl` were compiled with the Lynth build directory
removed from `LEAN_PATH`; the five new mathematical handoff sources also match
the repository sources exactly except for import paths. `git diff --check`
passed. These checks establish the executable/certificate composition while
the five new mathematical obligations and three pre-existing internal adapter
holes remain admitted.
