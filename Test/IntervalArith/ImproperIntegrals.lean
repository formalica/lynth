import Mathlib
import Lynth

/-!
Integral interval-arithmetic tests, including finite intervals, improper
endpoints, infinite domains, and a ten-dimensional cube.

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

/-- A two-constructor result for an integral. -/
def IntegralConvergenceResult
    (f : ℝ → ℝ) (s : Set ℝ) (tol : ℝ) : Type :=
  { x : Rat //
      IntegralConverges f s ∧
      abs ((∫ y in s, f y) - x) < tol }
  ⊕' (¬ IntegralConverges f s)

/-- Common tolerance for the rational witnesses. -/
noncomputable def integralTolerance : ℝ := 1 / 100000

noncomputable def cubicLinear (x : ℝ) : ℝ :=
  x ^ 3 + 2 * x

noncomputable def oddPolynomial (x : ℝ) : ℝ :=
  x ^ 5 + 3 * x ^ 3 - 2 * x + 1

noncomputable def expCos (x : ℝ) : ℝ :=
  Real.exp (Real.cos x)

noncomputable def decayingCubic (x : ℝ) : ℝ :=
  Real.exp (-x) * x ^ 3

noncomputable def gaussianQuartic (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2)) * x ^ 4

noncomputable def endpointWeight (x : ℝ) : ℝ :=
  x ^ 4 / Real.sqrt (1 - x ^ 2)

noncomputable def logIntegrand (x : ℝ) : ℝ :=
  Real.log x

noncomputable def narrowGaussian (x : ℝ) : ℝ :=
  Real.exp (-1000 * (x - 1 / 2) ^ 2)

noncomputable def cubeSum (x : ℝ ^ 10) : ℝ :=
  ∑ i : Fin 10, x i

noncomputable def reciprocalX (x : ℝ) : ℝ :=
  1 / x

noncomputable def reciprocalXSquared (x : ℝ) : ℝ :=
  1 / x ^ 2

noncomputable def reciprocalOneMinusX (x : ℝ) : ℝ :=
  1 / (1 - x)

noncomputable def tangent (x : ℝ) : ℝ :=
  Real.tan x

noncomputable def one (x : ℝ) : ℝ :=
  1

noncomputable def identity (x : ℝ) : ℝ :=
  x

noncomputable def sine (x : ℝ) : ℝ :=
  Real.sin x

noncomputable def exponential (x : ℝ) : ℝ :=
  Real.exp x

/-- **IC01** — `∫₀¹ (x³ + 2x) dx`; expected value `1.25`. -/
def cubicLinearSubtype :
    { x : Rat //
      IntegralConverges cubicLinear (Set.Icc (0 : ℝ) 1) ∧
      abs ((∫ y in Set.Icc (0 : ℝ) 1, cubicLinear y) - x) < integralTolerance } := by
  lynth

/-- **IC02** — `∫₋₁¹ (x⁵ + 3x³ - 2x + 1) dx`; expected value `2`. -/
def oddPolynomialSubtype :
    { x : Rat //
      IntegralConverges oddPolynomial (Set.Icc (-1 : ℝ) 1) ∧
      abs ((∫ y in Set.Icc (-1 : ℝ) 1, oddPolynomial y) - x) < integralTolerance } := by
  lynth

/-- **IC03** — `∫₀²π exp (cos θ) dθ`; expected value `7.95492652101284`. -/
def expCosResult :
    IntegralConvergenceResult expCos (Set.Icc (0 : ℝ) (2 * Real.pi)) integralTolerance := by
  lynth

/-- **IC04** — `∫₀^∞ exp (-x) x³ dx`; expected value `6`. -/
def decayingCubicResult :
    IntegralConvergenceResult decayingCubic (Set.Ioi 0) integralTolerance := by
  lynth

/-- **IC05** — `∫₋∞^∞ exp (-x²) x⁴ dx`; expected value `1.32934038817914`. -/
def gaussianQuarticResult :
    IntegralConvergenceResult gaussianQuartic Set.univ integralTolerance := by
  lynth

/-- **IC06** — `∫₋₁¹ x⁴ / sqrt (1 - x²) dx`; expected value `1.17809724509617`. -/
def endpointWeightSubtype :
    { x : Rat //
      IntegralConverges endpointWeight (Set.Icc (-1 : ℝ) 1) ∧
      abs ((∫ y in Set.Icc (-1 : ℝ) 1, endpointWeight y) - x) < integralTolerance } := by
  lynth

/-- **IC07** — `∫₀¹ log x dx`; expected value `-1`. -/
def logIntegrandResult :
    IntegralConvergenceResult logIntegrand (Set.Ioc (0 : ℝ) 1) integralTolerance := by
  lynth

/-- **IC08** — `∫₋₁¹ exp (-1000 (x - 1/2)²) dx`; expected value
`0.0560499121640`. -/
def narrowGaussianSubtype :
    { x : Rat //
      IntegralConverges narrowGaussian (Set.Icc (-1 : ℝ) 1) ∧
      abs ((∫ y in Set.Icc (-1 : ℝ) 1, narrowGaussian y) - x) < integralTolerance } := by
  lynth

/-- **IC09** — `∫_[0,1]^10 (x₁ + ... + x₁₀) dx`; expected value `5`. -/
def cubeSumSubtype :
    { x : Rat //
      MeasureTheory.IntegrableOn cubeSum
          (Set.Icc (0 : ℝ ^ 10) (1 : ℝ ^ 10)) ∧
      abs ((∫ y in Set.Icc (0 : ℝ ^ 10) (1 : ℝ ^ 10), cubeSum y) - x) < integralTolerance } := by
  lynth

/-- **ID01** — `∫₀¹ 1/x dx`; the improper integral diverges. -/
def reciprocalXPositiveResult :
    IntegralConvergenceResult reciprocalX (Set.Ioc (0 : ℝ) 1) integralTolerance := by
  lynth

/-- **ID02** — `∫₀¹ 1/x² dx`; the improper integral diverges. -/
theorem reciprocalXSquaredPositive_not_convergent :
    ¬ IntegralConverges reciprocalXSquared (Set.Ioc (0 : ℝ) 1) := by
  lynth

/-- **ID03** — `∫₋₁¹ 1/x dx`; the two one-sided improper integrals diverge. -/
theorem reciprocalXSymmetric_not_convergent :
    ¬ IntegralConverges reciprocalX (Set.Icc (-1 : ℝ) 1) := by
  lynth

/-- **ID04** — `∫₀¹ 1/(1-x) dx`; the improper integral diverges. -/
def reciprocalOneMinusXResult :
    IntegralConvergenceResult reciprocalOneMinusX (Set.Ioc (0 : ℝ) 1) integralTolerance := by
  lynth

/-- **ID05** — `∫₀^(π/2) tan x dx`; the improper integral diverges. -/
theorem tangent_not_convergent :
    ¬ IntegralConverges tangent (Set.Ioc (0 : ℝ) (Real.pi / 2)) := by
  lynth

/-- **ID06** — `∫₁^∞ 1/x dx`; the improper integral diverges. -/
def reciprocalXTailResult :
    IntegralConvergenceResult reciprocalX (Set.Ici (1 : ℝ)) integralTolerance := by
  lynth

/-- **ID07** — `∫₀^∞ 1 dx`; the improper integral diverges. -/
theorem one_not_convergent :
    ¬ IntegralConverges one (Set.Ioi (0 : ℝ)) := by
  lynth

/-- **ID08** — `∫₋∞^∞ x dx`; the two-sided improper integral diverges. -/
theorem identity_not_convergent :
    ¬ IntegralConverges identity Set.univ := by
  lynth

/-- **ID09** — `∫₁^∞ sin x dx`; the partial integrals oscillate and have no limit. -/
def sineTailResult :
    IntegralConvergenceResult sine (Set.Ici (1 : ℝ)) integralTolerance := by
  lynth

/-- **ID10** — `∫₀^∞ exp x dx`; the improper integral diverges. -/
theorem exponential_not_convergent :
    ¬ IntegralConverges exponential (Set.Ioi (0 : ℝ)) := by
  lynth

-- Axiom footprint checks.
/-- info: 'IntervalArith.IntegralConverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IntegralConverges
/-- info: 'IntervalArith.IntegralConvergenceResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IntegralConvergenceResult
/-- info: 'IntervalArith.integralTolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integralTolerance
/-- info: 'IntervalArith.cubicLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicLinear
/-- info: 'IntervalArith.oddPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPolynomial
/-- info: 'IntervalArith.expCos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCos
/-- info: 'IntervalArith.decayingCubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decayingCubic
/-- info: 'IntervalArith.gaussianQuartic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussianQuartic
/-- info: 'IntervalArith.endpointWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms endpointWeight
/-- info: 'IntervalArith.logIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logIntegrand
/-- info: 'IntervalArith.narrowGaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms narrowGaussian
/-- info: 'IntervalArith.cubeSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubeSum
/-- info: 'IntervalArith.reciprocalX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalX
/-- info: 'IntervalArith.reciprocalXSquared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalXSquared
/-- info: 'IntervalArith.reciprocalOneMinusX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalOneMinusX
/-- info: 'IntervalArith.tangent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tangent
/-- info: 'IntervalArith.one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one
/-- info: 'IntervalArith.identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity
/-- info: 'IntervalArith.sine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sine
/-- info: 'IntervalArith.exponential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exponential
/-- info: 'IntervalArith.cubicLinearSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicLinearSubtype
/-- info: 'IntervalArith.oddPolynomialSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPolynomialSubtype
/-- info: 'IntervalArith.expCosResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosResult
/-- info: 'IntervalArith.decayingCubicResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decayingCubicResult
/-- info: 'IntervalArith.gaussianQuarticResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussianQuarticResult
/-- info: 'IntervalArith.endpointWeightSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms endpointWeightSubtype
/-- info: 'IntervalArith.logIntegrandResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logIntegrandResult
/-- info: 'IntervalArith.narrowGaussianSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms narrowGaussianSubtype
/-- info: 'IntervalArith.cubeSumSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubeSumSubtype
/-- info: 'IntervalArith.reciprocalXPositiveResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalXPositiveResult
/-- info: 'IntervalArith.reciprocalXSquaredPositive_not_convergent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalXSquaredPositive_not_convergent
/-- info: 'IntervalArith.reciprocalXSymmetric_not_convergent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalXSymmetric_not_convergent
/-- info: 'IntervalArith.reciprocalOneMinusXResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalOneMinusXResult
/-- info: 'IntervalArith.tangent_not_convergent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tangent_not_convergent
/-- info: 'IntervalArith.reciprocalXTailResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalXTailResult
/-- info: 'IntervalArith.one_not_convergent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_not_convergent
/-- info: 'IntervalArith.identity_not_convergent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity_not_convergent
/-- info: 'IntervalArith.sineTailResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sineTailResult
/-- info: 'IntervalArith.exponential_not_convergent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exponential_not_convergent

end IntervalArith
