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
/-- info: 'IntervalArith.IntegralConverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IntegralConverges

/-- A two-constructor result for an integral. -/
def IntegralConvergenceResult
    (f : ℝ → ℝ) (s : Set ℝ) (tol : ℝ) : Type :=
  { x : Rat //
      IntegralConverges f s ∧
      abs ((∫ y in s, f y) - x) < tol }
  ⊕' (¬ IntegralConverges f s)
/-- info: 'IntervalArith.IntegralConvergenceResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IntegralConvergenceResult

/-- Common tolerance for the rational witnesses. -/
noncomputable def integralTolerance : ℝ := 1 / 100000
/-- info: 'IntervalArith.integralTolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integralTolerance

noncomputable def cubicLinear (x : ℝ) : ℝ :=
  x ^ 3 + 2 * x
/-- info: 'IntervalArith.cubicLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicLinear

noncomputable def oddPolynomial (x : ℝ) : ℝ :=
  x ^ 5 + 3 * x ^ 3 - 2 * x + 1
/-- info: 'IntervalArith.oddPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPolynomial

noncomputable def expCos (x : ℝ) : ℝ :=
  Real.exp (Real.cos x)
/-- info: 'IntervalArith.expCos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCos

noncomputable def decayingCubic (x : ℝ) : ℝ :=
  Real.exp (-x) * x ^ 3
/-- info: 'IntervalArith.decayingCubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decayingCubic

noncomputable def gaussianQuartic (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2)) * x ^ 4
/-- info: 'IntervalArith.gaussianQuartic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussianQuartic

noncomputable def endpointWeight (x : ℝ) : ℝ :=
  x ^ 4 / Real.sqrt (1 - x ^ 2)
/-- info: 'IntervalArith.endpointWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms endpointWeight

noncomputable def logIntegrand (x : ℝ) : ℝ :=
  Real.log x
/-- info: 'IntervalArith.logIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logIntegrand

noncomputable def narrowGaussian (x : ℝ) : ℝ :=
  Real.exp (-1000 * (x - 1 / 2) ^ 2)
/-- info: 'IntervalArith.narrowGaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms narrowGaussian

noncomputable def cubeSum (x : Fin 10 → ℝ) : ℝ :=
  ∑ i : Fin 10, x i
/-- info: 'IntervalArith.cubeSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubeSum

noncomputable def reciprocalX (x : ℝ) : ℝ :=
  1 / x
/-- info: 'IntervalArith.reciprocalX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalX

noncomputable def reciprocalXSquared (x : ℝ) : ℝ :=
  1 / x ^ 2
/-- info: 'IntervalArith.reciprocalXSquared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalXSquared

noncomputable def reciprocalOneMinusX (x : ℝ) : ℝ :=
  1 / (1 - x)
/-- info: 'IntervalArith.reciprocalOneMinusX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalOneMinusX

noncomputable def tangent (x : ℝ) : ℝ :=
  Real.tan x
/-- info: 'IntervalArith.tangent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tangent

noncomputable def one (x : ℝ) : ℝ :=
  1
/-- info: 'IntervalArith.one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one

noncomputable def identity (x : ℝ) : ℝ :=
  x
/-- info: 'IntervalArith.identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity

noncomputable def sine (x : ℝ) : ℝ :=
  Real.sin x
/-- info: 'IntervalArith.sine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sine

noncomputable def exponential (x : ℝ) : ℝ :=
  Real.exp x
/-- info: 'IntervalArith.exponential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exponential

/-- **IC01** — `∫₀¹ (x³ + 2x) dx`; expected value `1.25`. -/
def cubicLinearSubtype :
    { x : Rat //
      IntegralConverges cubicLinear (Set.Icc (0 : ℝ) 1) ∧
      abs ((∫ y in Set.Icc (0 : ℝ) 1, cubicLinear y) - x) < integralTolerance } := by
  lynth
/-- info: 'IntervalArith.cubicLinearSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubicLinearSubtype

/-- **IC02** — `∫₋₁¹ (x⁵ + 3x³ - 2x + 1) dx`; expected value `2`. -/
def oddPolynomialSubtype :
    { x : Rat //
      IntegralConverges oddPolynomial (Set.Icc (-1 : ℝ) 1) ∧
      abs ((∫ y in Set.Icc (-1 : ℝ) 1, oddPolynomial y) - x) < integralTolerance } := by
  lynth
/-- info: 'IntervalArith.oddPolynomialSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPolynomialSubtype

/-- **IC03** — `∫₀²π exp (cos θ) dθ`; expected value `7.95492652101284`. -/
def expCosResult :
    IntegralConvergenceResult expCos (Set.Icc (0 : ℝ) (2 * Real.pi)) integralTolerance := by
  lynth
/-- info: 'IntervalArith.expCosResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expCosResult

/-- **IC04** — `∫₀^∞ exp (-x) x³ dx`; expected value `6`. -/
def decayingCubicResult :
    IntegralConvergenceResult decayingCubic (Set.Ioi 0) integralTolerance := by
  lynth
/-- info: 'IntervalArith.decayingCubicResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decayingCubicResult

/-- **IC05** — `∫₋∞^∞ exp (-x²) x⁴ dx`; expected value `1.32934038817914`. -/
def gaussianQuarticResult :
    IntegralConvergenceResult gaussianQuartic Set.univ integralTolerance := by
  lynth
/-- info: 'IntervalArith.gaussianQuarticResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gaussianQuarticResult

/-- **IC06** — `∫₋₁¹ x⁴ / sqrt (1 - x²) dx`; expected value `1.17809724509617`. -/
def endpointWeightSubtype :
    { x : Rat //
      IntegralConverges endpointWeight (Set.Icc (-1 : ℝ) 1) ∧
      abs ((∫ y in Set.Icc (-1 : ℝ) 1, endpointWeight y) - x) < integralTolerance } := by
  lynth
/-- info: 'IntervalArith.endpointWeightSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms endpointWeightSubtype

/-- **IC07** — `∫₀¹ log x dx`; expected value `-1`. -/
def logIntegrandResult :
    IntegralConvergenceResult logIntegrand (Set.Ioc (0 : ℝ) 1) integralTolerance := by
  lynth
/-- info: 'IntervalArith.logIntegrandResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logIntegrandResult

/-- **IC08** — `∫₋₁¹ exp (-1000 (x - 1/2)²) dx`; expected value
`0.0560499121640`. -/
def narrowGaussianSubtype :
    { x : Rat //
      IntegralConverges narrowGaussian (Set.Icc (-1 : ℝ) 1) ∧
      abs ((∫ y in Set.Icc (-1 : ℝ) 1, narrowGaussian y) - x) < integralTolerance } := by
  lynth
/-- info: 'IntervalArith.narrowGaussianSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms narrowGaussianSubtype

/-- **IC09** — `∫_[0,1]^10 (x₁ + ... + x₁₀) dx`; expected value `5`. -/
def cubeSumSubtype :
    { x : Rat //
      MeasureTheory.IntegrableOn cubeSum
          (Set.Icc (0 : Fin 10 → ℝ) (1 : Fin 10 → ℝ)) ∧
      abs ((∫ y in Set.Icc (0 : Fin 10 → ℝ) (1 : Fin 10 → ℝ), cubeSum y) - x) < integralTolerance } := by
  lynth
/-- info: 'IntervalArith.cubeSumSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cubeSumSubtype

/-- **ID01** — `∫₀¹ 1/x dx`; the improper integral diverges. -/
def reciprocalXPositiveResult :
    IntegralConvergenceResult reciprocalX (Set.Ioc (0 : ℝ) 1) integralTolerance := by
  lynth
/-- info: 'IntervalArith.reciprocalXPositiveResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalXPositiveResult

/-- **ID02** — `∫₀¹ 1/x² dx`; the improper integral diverges. -/
theorem reciprocalXSquaredPositive_not_convergent :
    ¬ IntegralConverges reciprocalXSquared (Set.Ioc (0 : ℝ) 1) := by
  lynth
/-- info: 'IntervalArith.reciprocalXSquaredPositive_not_convergent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalXSquaredPositive_not_convergent

/-- **ID03** — `∫₋₁¹ 1/x dx`; the two one-sided improper integrals diverge. -/
theorem reciprocalXSymmetric_not_convergent :
    ¬ IntegralConverges reciprocalX (Set.Icc (-1 : ℝ) 1) := by
  lynth
/-- info: 'IntervalArith.reciprocalXSymmetric_not_convergent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalXSymmetric_not_convergent

/-- **ID04** — `∫₀¹ 1/(1-x) dx`; the improper integral diverges. -/
def reciprocalOneMinusXResult :
    IntegralConvergenceResult reciprocalOneMinusX (Set.Ioc (0 : ℝ) 1) integralTolerance := by
  lynth
/-- info: 'IntervalArith.reciprocalOneMinusXResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalOneMinusXResult

/-- **ID05** — `∫₀^(π/2) tan x dx`; the improper integral diverges. -/
theorem tangent_not_convergent :
    ¬ IntegralConverges tangent (Set.Ioc (0 : ℝ) (Real.pi / 2)) := by
  lynth
/-- info: 'IntervalArith.tangent_not_convergent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tangent_not_convergent

/-- **ID06** — `∫₁^∞ 1/x dx`; the improper integral diverges. -/
def reciprocalXTailResult :
    IntegralConvergenceResult reciprocalX (Set.Ici (1 : ℝ)) integralTolerance := by
  lynth
/-- info: 'IntervalArith.reciprocalXTailResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalXTailResult

/-- **ID07** — `∫₀^∞ 1 dx`; the improper integral diverges. -/
theorem one_not_convergent :
    ¬ IntegralConverges one (Set.Ioi (0 : ℝ)) := by
  lynth
/-- info: 'IntervalArith.one_not_convergent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_not_convergent

/-- **ID08** — `∫₋∞^∞ x dx`; the two-sided improper integral diverges. -/
theorem identity_not_convergent :
    ¬ IntegralConverges identity Set.univ := by
  lynth
/-- info: 'IntervalArith.identity_not_convergent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity_not_convergent

/-- **ID09** — `∫₁^∞ sin x dx`; the partial integrals oscillate and have no limit. -/
def sineTailResult :
    IntegralConvergenceResult sine (Set.Ici (1 : ℝ)) integralTolerance := by
  lynth
/-- info: 'IntervalArith.sineTailResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sineTailResult

/-- **ID10** — `∫₀^∞ exp x dx`; the improper integral diverges. -/
theorem exponential_not_convergent :
    ¬ IntegralConverges exponential (Set.Ioi (0 : ℝ)) := by
  lynth
/-- info: 'IntervalArith.exponential_not_convergent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exponential_not_convergent

-- Axiom footprint checks.

end IntervalArith
