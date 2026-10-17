import Mathlib
import Lynth

/-!
One-dimensional integral tests: finite intervals, improper endpoints,
infinite domains, and divergence. The ten-dimensional cube remains in
TestFailures/IntervalArith/ImproperIntegrals.lean.

`IntegralConverges` records Lebesgue integrability on the integration set.
The two-constructor result has a rational approximation in its left branch
and a non-convergence proof in its right branch. Expected values are kept in
comments, not in the predicates.
-/

namespace IntervalArith

/-- A one-dimensional integral is convergent when its integrand is integrable
on the specified integration set. -/
def IntegralConverges (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  MeasureTheory.IntegrableOn f s
/-- info: 'IntervalArith.IntegralConverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegralConverges

/-- A two-constructor result for an integral. -/
def IntegralConvergenceResult
    (f : ℝ → ℝ) (s : Set ℝ) (tol : ℝ) : Type :=
  { x : Rat //
      IntegralConverges f s ∧
      abs ((∫ y in s, f y) - x) < tol }
  ⊕' (¬ IntegralConverges f s)
/-- info: 'IntervalArith.IntegralConvergenceResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegralConvergenceResult

/-- Common tolerance for the rational witnesses. -/
noncomputable def integralTolerance : ℝ := 1 / 100000
/-- info: 'IntervalArith.integralTolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integralTolerance

noncomputable def cubicLinear (x : ℝ) : ℝ :=
  x ^ 3 + 2 * x
/-- info: 'IntervalArith.cubicLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubicLinear

noncomputable def oddPolynomial (x : ℝ) : ℝ :=
  x ^ 5 + 3 * x ^ 3 - 2 * x + 1
/-- info: 'IntervalArith.oddPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oddPolynomial

noncomputable def expCos (x : ℝ) : ℝ :=
  Real.exp (Real.cos x)
/-- info: 'IntervalArith.expCos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expCos

noncomputable def decayingCubic (x : ℝ) : ℝ :=
  Real.exp (-x) * x ^ 3
/-- info: 'IntervalArith.decayingCubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decayingCubic

noncomputable def gaussianQuartic (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2)) * x ^ 4
/-- info: 'IntervalArith.gaussianQuartic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gaussianQuartic

noncomputable def endpointWeight (x : ℝ) : ℝ :=
  x ^ 4 / Real.sqrt (1 - x ^ 2)
/-- info: 'IntervalArith.endpointWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms endpointWeight

noncomputable def logIntegrand (x : ℝ) : ℝ :=
  Real.log x
/-- info: 'IntervalArith.logIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms logIntegrand

noncomputable def narrowGaussian (x : ℝ) : ℝ :=
  Real.exp (-1000 * (x - 1 / 2) ^ 2)
/-- info: 'IntervalArith.narrowGaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms narrowGaussian

noncomputable def cubeSum (x : Fin 10 → ℝ) : ℝ :=
  ∑ i : Fin 10, x i
/-- info: 'IntervalArith.cubeSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubeSum

noncomputable def reciprocalX (x : ℝ) : ℝ :=
  1 / x
/-- info: 'IntervalArith.reciprocalX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reciprocalX

noncomputable def reciprocalXSquared (x : ℝ) : ℝ :=
  1 / x ^ 2
/-- info: 'IntervalArith.reciprocalXSquared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reciprocalXSquared

noncomputable def reciprocalOneMinusX (x : ℝ) : ℝ :=
  1 / (1 - x)
/-- info: 'IntervalArith.reciprocalOneMinusX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reciprocalOneMinusX

noncomputable def tangent (x : ℝ) : ℝ :=
  Real.tan x
/-- info: 'IntervalArith.tangent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tangent

noncomputable def one (x : ℝ) : ℝ :=
  1
/-- info: 'IntervalArith.one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one

noncomputable def identity (x : ℝ) : ℝ :=
  x
/-- info: 'IntervalArith.identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms identity

noncomputable def sine (x : ℝ) : ℝ :=
  Real.sin x
/-- info: 'IntervalArith.sine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sine

noncomputable def exponential (x : ℝ) : ℝ :=
  Real.exp x
/-- info: 'IntervalArith.exponential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exponential

set_option maxHeartbeats 2844 in -- measured: 2708; +5%
/-- **IC01** — `∫₀¹ (x³ + 2x) dx`; expected value `1.25`. -/
def cubicLinearSubtype :
    { x : Rat //
      IntegralConverges cubicLinear (Set.Icc (0 : ℝ) 1) ∧
      abs ((∫ y in Set.Icc (0 : ℝ) 1, cubicLinear y) - x) < integralTolerance } := by
  lynth
/-- info: 'IntervalArith.cubicLinearSubtype' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubicLinearSubtype

set_option maxHeartbeats 4948 in -- measured: 4712; +5%
/-- **IC02** — `∫₋₁¹ (x⁵ + 3x³ - 2x + 1) dx`; expected value `2`. -/
def oddPolynomialSubtype :
    { x : Rat //
      IntegralConverges oddPolynomial (Set.Icc (-1 : ℝ) 1) ∧
      abs ((∫ y in Set.Icc (-1 : ℝ) 1, oddPolynomial y) - x) < integralTolerance } := by
  lynth
/-- info: 'IntervalArith.oddPolynomialSubtype' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oddPolynomialSubtype

set_option maxHeartbeats 1294 in -- measured: 1232; +5%
/-- **IC03** — `∫₀²π exp (cos θ) dθ`; expected value `7.95492652101284`. -/
def expCosResult :
    IntegralConvergenceResult expCos (Set.Icc (0 : ℝ) (2 * Real.pi)) integralTolerance := by
  lynth
/-- info: 'IntervalArith.expCosResult' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, expCosResult._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms expCosResult

set_option maxHeartbeats 18557 in -- measured: 17673; +5%
/-- **IC04** — `∫₀^∞ exp (-x) x³ dx`; expected value `6`. -/
def decayingCubicResult :
    IntegralConvergenceResult decayingCubic (Set.Ioi 0) integralTolerance := by
  lynth
/-- info: 'IntervalArith.decayingCubicResult' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decayingCubicResult

set_option maxHeartbeats 3384 in -- measured: 3222; +5%
/-- **IC05** — `∫₋∞^∞ exp (-x²) x⁴ dx`; expected value `1.32934038817914`. -/
def gaussianQuarticResult :
    IntegralConvergenceResult gaussianQuartic Set.univ integralTolerance := by
  lynth
/-- info: 'IntervalArith.gaussianQuarticResult' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, gaussianQuarticResult._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms gaussianQuarticResult

set_option maxHeartbeats 11770 in -- measured: 11209; +5%
/-- **IC06** — `∫₋₁¹ x⁴ / sqrt (1 - x²) dx`; expected value `1.17809724509617`. -/
def endpointWeightSubtype :
    { x : Rat //
      IntegralConverges endpointWeight (Set.Icc (-1 : ℝ) 1) ∧
      abs ((∫ y in Set.Icc (-1 : ℝ) 1, endpointWeight y) - x) < integralTolerance } := by
  lynth
/-- info: 'IntervalArith.endpointWeightSubtype' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms endpointWeightSubtype

set_option maxHeartbeats 3113 in -- measured: 2964; +5%
/-- **IC07** — `∫₀¹ log x dx`; expected value `-1`. -/
def logIntegrandResult :
    IntegralConvergenceResult logIntegrand (Set.Ioc (0 : ℝ) 1) integralTolerance := by
  lynth
/-- info: 'IntervalArith.logIntegrandResult' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, logIntegrandResult._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms logIntegrandResult

set_option maxHeartbeats 2722 in -- measured: 2592; +5%
/-- **IC08** — `∫₋₁¹ exp (-1000 (x - 1/2)²) dx`; expected value
`0.0560499121640`. -/
def narrowGaussianSubtype :
    { x : Rat //
      IntegralConverges narrowGaussian (Set.Icc (-1 : ℝ) 1) ∧
      abs ((∫ y in Set.Icc (-1 : ℝ) 1, narrowGaussian y) - x) < integralTolerance } := by
  lynth
/-- info: 'IntervalArith.narrowGaussianSubtype' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, narrowGaussianSubtype._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms narrowGaussianSubtype

set_option maxHeartbeats 264 in -- measured: 251; +5%
/-- **ID01** — `∫₀¹ 1/x dx`; the improper integral diverges. -/
def reciprocalXPositiveResult :
    IntegralConvergenceResult reciprocalX (Set.Ioc (0 : ℝ) 1) integralTolerance := by
  lynth
/-- info: 'IntervalArith.reciprocalXPositiveResult' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reciprocalXPositiveResult

set_option maxHeartbeats 100 in -- measured: 95; +5%
/-- **ID02** — `∫₀¹ 1/x² dx`; the improper integral diverges. -/
theorem reciprocalXSquaredPositive_not_convergent :
    ¬ IntegralConverges reciprocalXSquared (Set.Ioc (0 : ℝ) 1) := by
  lynth
/-- info: 'IntervalArith.reciprocalXSquaredPositive_not_convergent' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reciprocalXSquaredPositive_not_convergent

set_option maxHeartbeats 133 in -- measured: 126; +5%
/-- **ID03** — `∫₋₁¹ 1/x dx`; the two one-sided improper integrals diverge. -/
theorem reciprocalXSymmetric_not_convergent :
    ¬ IntegralConverges reciprocalX (Set.Icc (-1 : ℝ) 1) := by
  lynth
/-- info: 'IntervalArith.reciprocalXSymmetric_not_convergent' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reciprocalXSymmetric_not_convergent

set_option maxHeartbeats 270 in -- measured: 257; +5%
/-- **ID04** — `∫₀¹ 1/(1-x) dx`; the improper integral diverges. -/
def reciprocalOneMinusXResult :
    IntegralConvergenceResult reciprocalOneMinusX (Set.Ioc (0 : ℝ) 1) integralTolerance := by
  lynth
/-- info: 'IntervalArith.reciprocalOneMinusXResult' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reciprocalOneMinusXResult

set_option maxHeartbeats 1701 in -- measured: 1620; +5%
/-- **ID05** — `∫₀^(π/2) tan x dx`; the improper integral diverges. -/
theorem tangent_not_convergent :
    ¬ IntegralConverges tangent (Set.Ioc (0 : ℝ) (Real.pi / 2)) := by
  lynth
/-- info: 'IntervalArith.tangent_not_convergent' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tangent_not_convergent

set_option maxHeartbeats 231 in -- measured: 220; +5%
/-- **ID06** — `∫₁^∞ 1/x dx`; the improper integral diverges. -/
def reciprocalXTailResult :
    IntegralConvergenceResult reciprocalX (Set.Ici (1 : ℝ)) integralTolerance := by
  lynth
/-- info: 'IntervalArith.reciprocalXTailResult' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reciprocalXTailResult

set_option maxHeartbeats 53 in -- measured: 50; +5%
/-- **ID07** — `∫₀^∞ 1 dx`; the improper integral diverges. -/
theorem one_not_convergent :
    ¬ IntegralConverges one (Set.Ioi (0 : ℝ)) := by
  lynth
/-- info: 'IntervalArith.one_not_convergent' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_not_convergent

set_option maxHeartbeats 23 in -- measured: 21; +5%
/-- **ID08** — `∫₋∞^∞ x dx`; the two-sided improper integral diverges. -/
theorem identity_not_convergent :
    ¬ IntegralConverges identity Set.univ := by
  lynth
/-- info: 'IntervalArith.identity_not_convergent' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms identity_not_convergent

set_option maxHeartbeats 212 in -- measured: 201; +5%
/-- **ID09** — `∫₁^∞ sin x dx`; the partial integrals oscillate and have no limit. -/
def sineTailResult :
    IntegralConvergenceResult sine (Set.Ici (1 : ℝ)) integralTolerance := by
  lynth
/-- info: 'IntervalArith.sineTailResult' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sineTailResult

set_option maxHeartbeats 30 in -- measured: 28; +5%
/-- **ID10** — `∫₀^∞ exp x dx`; the improper integral diverges. -/
theorem exponential_not_convergent :
    ¬ IntegralConverges exponential (Set.Ioi (0 : ℝ)) := by
  lynth
/-- info: 'IntervalArith.exponential_not_convergent' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exponential_not_convergent

-- Axiom footprint checks.

end IntervalArith

/-!
Improper real examples from FLINT's `examples/integrals.c`. These goals include
the complete infinite tail. FLINT 2 displays twice the integral tested here.
Every integration testcase in this file has its own finite heartbeat limit,
set to `ceil(count * 105 / 100)` using Mathlib's `#count_heartbeats in` on a
temporary copy. Keep that counting wrapper out of the tests themselves: it
disables the limit. Heartbeats do not bound native wall time.
-/

namespace IntervalArith.Flint

open MeasureTheory

set_option maxHeartbeats 2358 in -- measured: 2245; +5%
/-- FLINT 2: the arctangent derivative on the positive half-line. -/
def atanHalfLine :
    {q : ℚ //
      IntegrableOn (fun x : ℝ => 1 / (1 + x^2)) (Set.Ioi 0) ∧
      |(∫ x in Set.Ioi (0 : ℝ), 1 / (1 + x^2)) - (q : ℝ)| < 1 / 100000} := by
  lynth
/-- info: 'IntervalArith.Flint.atanHalfLine' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, atanHalfLine._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms atanHalfLine
#guard |atanHalfLine.val - (15707963267948966 / 10^16 : ℚ)| < 1 / 100000

set_option maxHeartbeats 9807 in -- measured: 9340; +5%
/-- FLINT 14: the Gaussian half-line integral at absolute tolerance `10⁻⁵`. -/
def gaussianHalfLine :
    {q : ℚ //
      IntegrableOn (fun x : ℝ => Real.exp (-(x^2))) (Set.Ioi 0) ∧
      |(∫ x in Set.Ioi (0 : ℝ), Real.exp (-(x^2))) - (q : ℝ)| < 1 / 100000} := by
  lynth
/-- info: 'IntervalArith.Flint.gaussianHalfLine' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gaussianHalfLine
#guard |gaussianHalfLine.val - (88622692545275801 / 10^17 : ℚ)| < 1 / 100000

set_option maxHeartbeats 1911 in -- measured: 1820; +5%
/-- FLINT 17: the hyperbolic secant on the positive half-line. -/
def sechHalfLine :
    {q : ℚ //
      IntegrableOn (fun x : ℝ => (Real.cosh x)⁻¹) (Set.Ioi 0) ∧
      |(∫ x in Set.Ioi (0 : ℝ), (Real.cosh x)⁻¹) - (q : ℝ)| < 1 / 100000} := by
  lynth
/-- info: 'IntervalArith.Flint.sechHalfLine' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, sechHalfLine._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms sechHalfLine
#guard |sechHalfLine.val - (15707963267948966 / 10^16 : ℚ)| < 1 / 100000

set_option maxHeartbeats 2421 in -- measured: 2305; +5%
/-- FLINT 18: the cube of the hyperbolic secant on the positive half-line. -/
def sechCubeHalfLine :
    {q : ℚ //
      IntegrableOn (fun x : ℝ => ((Real.cosh x)⁻¹)^3) (Set.Ioi 0) ∧
      |(∫ x in Set.Ioi (0 : ℝ), ((Real.cosh x)⁻¹)^3) - (q : ℝ)| < 1 / 100000} := by
  lynth
/-- info: 'IntervalArith.Flint.sechCubeHalfLine' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, sechCubeHalfLine._native.native_decide.ax_1] -/
#guard_msgs (whitespace := lax) in
#print axioms sechCubeHalfLine
#guard |sechCubeHalfLine.val - (78539816339744831 / 10^17 : ℚ)| < 1 / 100000

end IntervalArith.Flint
