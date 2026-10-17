import Mathlib
import Lynth

/-!
T15-T21: adaptive Gauss-Legendre/Petras integration, improper Gaussian
tails, and proof-producing divergence. The historical Arb bounds below are
reference data; `lynth` computes its own certificates and rational witnesses.
The integration proof obligations currently use the explicitly permitted `sorry`.

Each integration testcase has its own finite heartbeat limit. The recorded
counts come from Mathlib's `#count_heartbeats in` on a temporary copy; each
limit is `ceil(count * 105 / 100)`. The counting wrapper is deliberately absent
here because it disables the limit. Heartbeats do not bound native wall time.
-/

namespace IntervalArith

open MeasureTheory

inductive IntegralAnswer (f : ℝ → ℝ) (a b : ℝ) (ε : ℚ) : Type
  | approx (x : ℚ)
      (integrable : IntervalIntegrable f volume a b)
      (close : |(∫ y in a..b, f y) - (x : ℝ)| < (ε : ℝ))
  | diverges
      (not_integrable : ¬ IntervalIntegrable f volume a b)


/-- **T15** — `integral_0^1 exp (-x^2)` — non-elementary integrand; rigorous quadrature (midpoint
rule with an interval error term).

enclosure `0.7468234841568766047004146; 0.7468285237444967084030623`, witness
`0.7468241328124270253994674361318530053545`, worst error `4.390932069732768135866298e-06` <
`0.001000000000000000020816682`.

composite midpoint rule n=128, error <= h^3 M2/24 with interval M2; enclosure
[0.74682348415687665446, 0.74682852374449675817].

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
noncomputable def expNegSq (y : ℝ) : ℝ := Real.exp (-(y ^ 2))

set_option maxHeartbeats 18394 in -- measured: 17518; +5%
def integral_exp_neg_sq :
    { x : ℚ //
      IntervalIntegrable expNegSq volume 0 1 ∧
      |(∫ y in (0 : ℝ)..1, expNegSq y) - (x : ℝ)| < 1 / 100000 } := by
  lynth
/-- info: 'IntervalArith.integral_exp_neg_sq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_exp_neg_sq

set_option maxHeartbeats 17562 in -- measured: 16725; +5%
/-- **T16** — `integral_0^pi sin = 2` — the integration endpoint is `Real.pi` itself.

enclosure `1.999999387362327185613253; 2.000101013209477862631047`, witness `2`, worst error
`0.0001010132094780230116535386` < `0.001000000000000000020816682`.

exact value 2; quadrature on [0, arb pi] = [1.99999938736232712394, 2.00010101320947802301].

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def integral_sin : { x : Rat // abs ((∫ y in (0 : ℝ)..Real.pi, Real.sin y) - x) < 1 / 100000 } := by
  lynth
/-- info: 'IntervalArith.integral_sin' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_sin

/-- **T17** — `integral_0^pi x * sin x = pi` — irrational value, irrational endpoint.

enclosure `3.141520695921368400149731; 3.141822320107618082829504`, witness
`3.14152069592136821316`, worst error `0.000301624186249682679772377` <
`0.01000000000000000020816682`.

exact value pi = 3.141592653589793238462643383279502884197; quadrature =
[3.14152069592136821316, 3.14182232010761789585].

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
noncomputable def xSin (y : ℝ) : ℝ := y * Real.sin y

set_option maxHeartbeats 17955 in -- measured: 17100; +5%
def integral_x_sin :
    { x : ℚ //
      IntervalIntegrable xSin volume 0 Real.pi ∧
      |(∫ y in (0 : ℝ)..Real.pi, xSin y) - (x : ℝ)| < 1 / 10000 }
    ⊕' ¬ IntervalIntegrable xSin volume 0 Real.pi := by
  lynth
/-- info: 'IntervalArith.integral_x_sin' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_x_sin

/-- **T18** — `integral_0^1 1/x` diverges (non-integrable singularity at `0`). -/
noncomputable def invFun (y : ℝ) : ℝ := y⁻¹

set_option maxHeartbeats 204 in -- measured: 194; +5%
def integral_inv : IntegralAnswer invFun 0 1 (1 / 10000) := by
  lynth
/-- info: 'IntervalArith.integral_inv' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_inv

/-- **T19** — `integral_0^(pi/2) tan` diverges (non-integrable singularity at `pi/2`). -/
noncomputable def tanFun (y : ℝ) : ℝ := Real.tan y

set_option maxHeartbeats 1841 in -- measured: 1753; +5%
def integral_tan : IntegralAnswer tanFun 0 (Real.pi / 2) (1 / 10000) := by
  lynth
/-- info: 'IntervalArith.integral_tan' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_tan

inductive IntegralAnswerOn (f : ℝ → ℝ) (S : Set ℝ) (ε : ℚ) : Type
  | approx (x : ℚ)
      (integrable : IntegrableOn f S volume)
      (close : |(∫ y in S, f y) - (x : ℝ)| < (ε : ℝ))
  | diverges
      (not_integrable : ¬ IntegrableOn f S volume)

set_option maxHeartbeats 50196 in -- measured: 47805; +5%
/-- **T20** — `∫₀^∞ exp(-y²) dy = √π / 2 ≈ 0.8862`, convergent half-line integral. -/
def integral_exp_neg_sq_inf :
    { x : ℚ //
      IntegrableOn expNegSq (Set.Ioi 0) volume ∧
      |(∫ y in Set.Ioi (0 : ℝ), expNegSq y) - (x : ℝ)| < 1 / 1000 }
    ⊕' ¬ IntegrableOn expNegSq (Set.Ioi 0) volume := by
  lynth
/-- info: 'IntervalArith.integral_exp_neg_sq_inf' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_exp_neg_sq_inf

set_option maxHeartbeats 174 in -- measured: 165; +5%
/-- **T21** — `integral_1^∞ 1/y` diverges (harmonic tail). -/
def integral_inv_inf :
    IntegralAnswerOn invFun (Set.Ioi 1) (1 / 100) := by
  lynth
/-- info: 'IntervalArith.integral_inv_inf' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_inv_inf

-- Axiom footprint checks.

end IntervalArith

/-!
Real examples from /tmp/flint/examples/integrals.c, plus orientation checks.
Witnesses are synthesized from the computed enclosures. The existing auto
trust policy selects native checking for expensive certificates; the axiom
checks below record those auxiliary axioms explicitly.
FLINT 1 and 3 display four times the integrals tested here.
-/

set_option maxRecDepth 10000

namespace IntervalArith.Flint

open MeasureTheory

set_option maxHeartbeats 10370 in -- measured: 9876; +5%
/-- FLINT 1: the arctangent derivative. -/
def atan01 :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => 1 / (1 + x^2)) volume (0) (1) ∧
      |(∫ x in (0 : ℝ)..(1), 1 / (1 + x^2)) - (q : ℝ)| < 1/100000} := by
  lynth
/-- info: 'IntervalArith.Flint.atan01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms atan01

set_option maxHeartbeats 1863 in -- measured: 1774; +5%
/-- FLINT 3: a quarter circle, with a square-root endpoint. -/
def circle01 :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => Real.sqrt (1-x^2)) volume (0) (1) ∧
      |(∫ x in (0 : ℝ)..(1), Real.sqrt (1-x^2)) - (q : ℝ)| < 1/100000} := by
  lynth
/-- info: 'IntervalArith.Flint.circle01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, circle01._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms circle01

set_option maxHeartbeats 8351 in -- measured: 7953; +5%
/-- FLINT 5: integer jumps; the integral is 5050. -/
def floor101 :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => ((⌊x⌋ : ℤ) : ℝ)) volume (1) (101) ∧
      |(∫ x in (1 : ℝ)..(101), ((⌊x⌋ : ℤ) : ℝ)) - (q : ℝ)| < 1/1000} := by
  lynth
/-- info: 'IntervalArith.Flint.floor101' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floor101

set_option maxHeartbeats 8946 in -- measured: 8520; +5%
/-- FLINT 24: switching analytic branches. -/
def maxSinCos :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => max (Real.sin x) (Real.cos x)) volume (0) (Real.pi) ∧
      |(∫ x in (0 : ℝ)..(Real.pi), max (Real.sin x) (Real.cos x)) - (q : ℝ)| < 1/100000} := by
  lynth
/-- info: 'IntervalArith.Flint.maxSinCos' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, maxSinCos._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms maxSinCos

set_option maxHeartbeats 18475 in -- measured: 17595; +5%
/-- Reversed interval orientation. -/
def reverseGaussian :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => Real.exp (-(x^2))) volume (1) (0) ∧
      |(∫ x in (1 : ℝ)..(0), Real.exp (-(x^2))) - (q : ℝ)| < 1/100000} := by
  lynth
/-- info: 'IntervalArith.Flint.reverseGaussian' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reverseGaussian

set_option maxHeartbeats 598 in -- measured: 569; +5%
/-- An interval with equal endpoints. -/
def zeroWidth :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => Real.exp (-(x^2))) volume (1) (1) ∧
      |(∫ x in (1 : ℝ)..(1), Real.exp (-(x^2))) - (q : ℝ)| < 1/100000} := by
  lynth
/-- info: 'IntervalArith.Flint.zeroWidth' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zeroWidth

set_option maxHeartbeats 4217 in -- measured: 4016; +5%
/-- FLINT 31: a rational trigonometric expression. -/
def trigRational :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => x * Real.sin x / (1 + (Real.cos x)^2)) volume (0) (Real.pi) ∧
      |(∫ x in (0 : ℝ)..(Real.pi), x * Real.sin x / (1 + (Real.cos x)^2)) - (q : ℝ)| < 1/100000} := by
  lynth
/-- info: 'IntervalArith.Flint.trigRational' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, trigRational._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms trigRational

set_option maxHeartbeats 5848 in -- measured: 5569; +5%
/-- FLINT 6: absolute values of a polynomial times exp. -/
def helfgott01 :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => |x^4 + 10*x^3 + 19*x^2 - 6*x - 6| * Real.exp x) volume (0) (1) ∧
      |(∫ x in (0 : ℝ)..(1), |x^4 + 10*x^3 + 19*x^2 - 6*x - 6| * Real.exp x) - (q : ℝ)| < 1/100000} := by
  lynth
/-- info: 'IntervalArith.Flint.helfgott01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, helfgott01._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms helfgott01

set_option maxHeartbeats 3212 in -- measured: 3059; +5%
/-- FLINT 0: oscillation over a long interval. -/
def sin100 :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => Real.sin x) volume (0) (100) ∧
      |(∫ x in (0 : ℝ)..(100), Real.sin x) - (q : ℝ)| < 1/100000} := by
  lynth
/-- info: 'IntervalArith.Flint.sin100' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, sin100._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms sin100

set_option maxHeartbeats 41431 in -- measured: 39458; +5%
/-- FLINT 4: Rump's increasingly oscillatory example. -/
def rump08 :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => Real.sin (x + Real.exp x)) volume (0) (8) ∧
      |(∫ x in (0 : ℝ)..(8), Real.sin (x + Real.exp x)) - (q : ℝ)| < 1/100000} := by
  lynth
/-- info: 'IntervalArith.Flint.rump08' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, rump08._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms rump08

set_option maxHeartbeats 3209 in -- measured: 3056; +5%
/-- FLINT 12: cancellation on a symmetric interval at absolute tolerance `10⁻⁵`.
The residual is about `2.453 × 10⁻⁸⁷`, so zero is a valid witness at this
tolerance. Resolving that residual to relative precision is not tested here. -/
def cancellationAbsolute :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => Real.sin x + Real.exp (-200-x^2)) volume (-10) 10 ∧
      |(∫ x in (-10 : ℝ)..10, Real.sin x + Real.exp (-200-x^2)) - (q : ℝ)| <
        1 / 100000} := by
  lynth
/-- info: 'IntervalArith.Flint.cancellationAbsolute' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, cancellationAbsolute._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms cancellationAbsolute
#guard |cancellationAbsolute.val| < 1 / 100000

set_option maxHeartbeats 39585 in -- measured: 37700; +5%
/-- FLINT 10: the original unscaled integrand `x^1000 exp(-x)` on `[0, 10000]`.
The result is approximately `1000! ≈ 4.024 × 10^2567`; the absolute tolerance
`10^2562` is about `2.5 × 10⁻⁶` of its value. -/
def factorial1000 :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => x^1000 * Real.exp (-x)) volume 0 10000 ∧
      |(∫ x in (0 : ℝ)..10000, x^1000 * Real.exp (-x)) - (q : ℝ)| < (10 : ℝ)^2562} := by
  lynth
/-- info: 'IntervalArith.Flint.factorial1000' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, factorial1000._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms factorial1000
#guard |factorial1000.val / (Nat.factorial 1000 : ℚ) - 1| < 1 / 100000

set_option maxHeartbeats 46896 in -- measured: 44662; +5%
/-- FLINT 13: a tiny nonzero integral, resolved to absolute error `10⁻⁴⁴⁵`.
Its value is approximately `2.30437715094936 × 10⁻⁴³⁹`. -/
def tinyExp :
    {q : ℚ //
      IntervalIntegrable Real.exp volume (-1020) (-1010) ∧
      |(∫ x in (-1020 : ℝ)..(-1010), Real.exp x) - (q : ℝ)| < 1 / (10 : ℝ)^445} := by
  lynth
/-- info: 'IntervalArith.Flint.tinyExp' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tinyExp
#guard 0 < tinyExp.val
#guard |tinyExp.val * 10^439 - (23043771509493634424 / 10^19 : ℚ)| < 1 / 1000000

set_option maxHeartbeats 49880 in -- measured: 47504; +5%
/-- FLINT 27: a floor expression multiplied by switching trigonometric branches.
The integral is approximately `-0.142818642026328`. -/
def floorMax :
    {q : ℚ //
      IntervalIntegrable
        (fun x : ℝ => (x - ((⌊x⌋ : ℤ) : ℝ) - 1/2) * max (Real.sin x) (Real.cos x))
        volume 0 10 ∧
      |(∫ x in (0 : ℝ)..10,
        (x - ((⌊x⌋ : ℤ) : ℝ) - 1/2) * max (Real.sin x) (Real.cos x)) - (q : ℝ)| <
          1 / 100000} := by
  lynth
/-- info: 'IntervalArith.Flint.floorMax' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, floorMax._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms floorMax
#guard |floorMax.val - (-14281864202632808 / 10^17 : ℚ)| < 1 / 100000

end IntervalArith.Flint
