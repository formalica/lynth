import Mathlib
import Lynth

/-!
Known unsupported complex integrals over real ranges. These are genuine solver
failures, without admitted testcase proofs. Each attempt has its own
maxHeartbeats cap of ceil(1.05 * the baseline #count_heartbeats).
Passing cases live in Test/ComplexIntervalArith/Integrals.lean.

Items 7, 9, 21 and 25 need enclosures across moving algebraic singularities;
item 8 needs further branch-point endpoint bounds; item 12 needs stronger
parametric bounds across the square-root cut; item 18b needs oscillatory
cancellation after the exact inner primitive. See docs/interval/19-complex-real-integrals.md.

Item 17 is omitted: Complex.besselJ is absent from this Mathlib version and
Lynth has no Bessel-J evaluator.
-/
namespace ComplexIntervalArith.Integrals
open MeasureTheory
set_option maxRecDepth 10000

set_option maxHeartbeats 2670 in -- measured: 2542; +5%
/-- NIntegrate item 7 (=22–24).

Even the direct FLINT calculation failed to produce a finite answer (0.041 s).
Split at the sine zeros 0, π, 2π and 3π, then substitute x = c ± t² near each
zero c. At c = 0 this changes dx / sqrt(sin x) into
2t / sqrt(sin(t²)) dt, which approaches 2 instead of becoming infinite.
Evaluate it as 2 / sqrt(sinc(t²)) to cancel the zero before interval evaluation.
Split between neighboring zeros so both singular endpoints are handled.
Keep the negative imaginary factor where sin x < 0, since the inverse is
outside the principal complex square root.

These symbolic changes made FLINT reach the required error in about 1.2 ms.
FLINT did not discover the changes automatically; the benchmark supplied them
by hand. Results use 64-bit arithmetic, error < 1/10000, and median calculation
time over five runs, excluding process startup and Lean proof checking.
Code and logs for all six comparisons: /tmp/flint-complex-bench/README.md.
-/
def inverseSqrtSin : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => ((Complex.sin (x:ℂ))^(1/2:ℂ))⁻¹) volume (0) (10) ∧
    ‖(∫ x in (0:ℝ)..(10), ((Complex.sin (x:ℂ))^(1/2:ℂ))⁻¹)-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

set_option maxHeartbeats 3377 in -- measured: 3216; +5%
/-- NIntegrate item 8.

Even the direct FLINT calculation returned no finite answer (0.035 s).
Split at x = 7 and x = 8. Near 7, substitute x = 7 ± exp(-t). On the left,
sqrt(log(x-7)) dx becomes sqrt(-t + iπ) exp(-t) dt; on the right it becomes
i sqrt(t) exp(-t) dt, with the integration direction accounted for.
The exponential makes the transformed tails small. Truncating the left tail
at t = 32 omits at most exp(-32) * (34 + π), which must be added as an error
bound. The right-hand integral from 7 to 8 is exactly i sqrt(π) / 2.
For x from 8 to 20, substitute x = 7 + exp(u²), giving the regular integrand
2u² exp(u²) on [0, sqrt(log 13)]. The part from 0 to 6 is already regular.

After supplying these symbolic changes by hand, FLINT reached error < 1/10000
in about 1.6 ms (64-bit arithmetic, median of five calculation times).
Thus the missing splitting, substitutions and tail bounds should make this
converge faster; merely increasing arithmetic precision does not remove the
singularity. See /tmp/flint-complex-bench/README.md for code and logs.
-/
def shiftedSqrtLog : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => (Complex.log ((x:ℂ)-7))^(1/2:ℂ)) volume (0) (20) ∧
    ‖(∫ x in (0:ℝ)..(20), (Complex.log ((x:ℂ)-7))^(1/2:ℂ))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

set_option maxHeartbeats 2712 in -- measured: 2582; +5%
/-- NIntegrate item 9.

Even FLINT timed out after 90 s when an outer numerical integration called
another numerical integration for the original inner integral.
Substitute t = x*y and interchange the absolutely integrable variables:
  ∫ x in 0..5, ∫ y in 0..5, 1 / sqrt(cos(x*y))
    = ∫ t in 0..25, log(25/t) / sqrt(cos t).
This replaces the nested calculation by one integral with fixed singularities.
Split at t = π/2 + kπ and use t = c ± h*u² near each zero c, cancelling the
square-root zero through sinc as in item 7. Preserve the negative imaginary
factor on intervals where cos t < 0.
For the logarithmic endpoint on [0,d], d = π/4, use t = d*exp(-u). Truncate at
u = 32 and add the bound 2d*exp(-32)*(log(25/d)+33) for the omitted part.

Supplying these symbolic changes by hand made FLINT reach error < 1/10000 in
about 6.1 ms (64-bit arithmetic, median of five calculation times).
This measures these particular callbacks, not every possible FLINT approach.
Code, formulas and logs: /tmp/flint-complex-bench/README.md.
-/
def inverseSqrtCosXY : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => ∫ y in (0:ℝ)..5, ((Complex.cos ((x:ℂ)*(y:ℂ)))^(1/2:ℂ))⁻¹) volume (0) (5) ∧
    ‖(∫ x in (0:ℝ)..(5), ∫ y in (0:ℝ)..5, ((Complex.cos ((x:ℂ)*(y:ℂ)))^(1/2:ℂ))⁻¹)-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

set_option maxHeartbeats 3014 in -- measured: 2870; +5%
/-- NIntegrate item 12.

Even the direct nested FLINT calculation missed error < 1/10000: after 13.5 s
its complex error radius was about 0.000362. Instead, integrate in y exactly.
The primitive is (2 / (3i)) * (x + iy)^(3/2), but for x < 0 split at y = 0
to respect the principal square-root branch. The correct inner integral is
  (2 / (3i)) * ((x+2i)^(3/2) - (x-2i)^(3/2))
    + (if x < 0 then (4/3)*(-x)^(3/2) else 0).
Integrate the first term numerically in x; the second term contributes exactly
(8/15)*2^(5/2). Omitting this branch correction would give the wrong answer.

After supplying this symbolic inner integration by hand, FLINT reached the
required error in about 0.7 ms (64-bit arithmetic, median of five calculation
times). This removes repeated numerical inner integrations and should make
Lynth converge faster too. Code and logs: /tmp/flint-complex-bench/README.md.
-/
def sqrtSquare : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => ∫ y in (-2:ℝ)..2, ((x:ℂ)+(y:ℂ)*Complex.I)^(1/2:ℂ)) volume (-2) (2) ∧
    ‖(∫ x in (-2:ℝ)..(2), ∫ y in (-2:ℝ)..2, ((x:ℂ)+(y:ℂ)*Complex.I)^(1/2:ℂ))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

set_option maxHeartbeats 8839 in -- measured: 8418; +5%
/-- NIntegrate item 18b.

Even direct numerical nesting with FLINT timed out after 90 s.
Let a = log 2 and B = 10000. Integrate in y exactly:
  ∫ y in 1..B, exp(i*a*x*y) = (exp(i*a*B*x) - exp(i*a*x)) / (i*a*x).
After changing variables in the two resulting terms, the original integral is
  (1/(i*a)) * (∫ t in a*B..a*B², exp(i*t)/t
                - ∫ t in a..a*B, exp(i*t)/t).
Numerically integrate only the short interval [a,32]. For the long oscillating
parts, integrate by parts 12 times and evaluate the resulting endpoint terms.
With F(t) = exp(i*t) * ∑ k=0..11, k!/(i*t)^(k+1), the answer is approximated by
  (F(a*B²) - 2*F(a*B) + F(32) - ∫ t in a..32, exp(i*t)/t) / (i*a),
with error at most 11! * ((a*B)^(-12) + 32^(-12)) / a.
This avoids sampling the millions of oscillations in the original expression.

Supplying these symbolic changes and the explicit remainder bound by hand
made FLINT reach error < 1/10000 in about 1.1 ms (64-bit arithmetic, median of
five calculation times). It uses elementary functions and Gauss–Legendre,
without requiring Ci evaluation or Taylor integration.
Code and logs: /tmp/flint-complex-bench/README.md (benchmark item 180).
-/
def doublePower : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => ∫ y in (1:ℝ)..10000, (2:ℂ)^(Complex.I*(x:ℂ)*(y:ℂ))) volume (1) (10000) ∧
    ‖(∫ x in (1:ℝ)..(10000), ∫ y in (1:ℝ)..10000, (2:ℂ)^(Complex.I*(x:ℂ)*(y:ℂ)))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

set_option maxHeartbeats 3293 in -- measured: 3136; +5%
/-- NIntegrate item 21.

Even FLINT timed out after 90 s with direct numerical nesting.
Substitute t = x²+y and interchange the absolutely integrable variables:
  ∫ x in -5..5, ∫ y in -5..5, 1 / sqrt(sin(x²+y))
    = ∫ t in -5..30, W(t) / sqrt(sin t),
where W(t) = 2 * (sqrt(min(25,t+5)) - sqrt(max(0,t-5))).
This replaces two numerical integrations by one. Split at the sine zeros kπ
and at -5, 5, 20 and 30, where the weight's formula changes. Use quadratic
substitutions t = c ± h*u² to cancel the inverse square-root singularities via
sinc. At a square-root endpoint of the weight, simplify sqrt(h*u²) to sqrt(h)*u
for u ≥ 0 before interval evaluation. Preserve the negative imaginary factor
where sin t < 0.

Supplying these symbolic changes by hand made FLINT reach error < 1/10000 in
about 8.2 ms (64-bit arithmetic, median of five calculation times).
These changes remove the moving inner singularities and should make Lynth
converge faster. Code and logs: /tmp/flint-complex-bench/README.md.
-/
def inverseSqrtSinXY : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => ∫ y in (-5:ℝ)..5, ((Complex.sin ((x:ℂ)^2+(y:ℂ)))^(1/2:ℂ))⁻¹) volume (-5) (5) ∧
    ‖(∫ x in (-5:ℝ)..(5), ∫ y in (-5:ℝ)..5, ((Complex.sin ((x:ℂ)^2+(y:ℂ)))^(1/2:ℂ))⁻¹)-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

set_option maxHeartbeats 3607 in -- measured: 3435; +5%
/-- NIntegrate item 25. -/
def sqrtReciprocalTrig : {p : ℚ × ℚ //
    IntervalIntegrable (fun x : ℝ => ∫ y in (0:ℝ)..5, ((Complex.cos (5*(x:ℂ))*Complex.sin (5*(y:ℂ))-1/2)⁻¹)^(1/2:ℂ)) volume (0) (5) ∧
    ‖(∫ x in (0:ℝ)..(5), ∫ y in (0:ℝ)..5, ((Complex.cos (5*(x:ℂ))*Complex.sin (5*(y:ℂ))-1/2)⁻¹)^(1/2:ℂ))-((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖ < 1/10000} := by
  lynth

end ComplexIntervalArith.Integrals
