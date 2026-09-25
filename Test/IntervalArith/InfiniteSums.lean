import Mathlib
import Lynth

/-!
Infinite-series interval-arithmetic tests.

The `SeriesSummabilityResult` goals use a two-branch `PSum`: the left
branch contains a rational approximation together with a summability proof,
and the right branch contains a proof that the series is not summable.  The
ordinary refinement goals contain only the approximation and summability
proof.  Expected values are recorded in comments, never in the predicates.
-/

namespace IntervalArith

/-- Common tolerance for the rational witnesses. -/
noncomputable def infiniteSumTolerance : ℝ := 1 / 100000

/-- `5 * (3/5)^k`, for `k = 0, 1, ...`. -/
noncomputable def geometricFiveSixths (k : ℕ) : ℝ :=
  5 * ((3 : ℝ) / 5) ^ k

/-- `1 / ((k+1)(k+2))`, for `k = 0, 1, ...`. -/
noncomputable def telescopingReciprocals (k : ℕ) : ℝ :=
  1 / (((k + 1 : ℝ) * (k + 2 : ℝ)))

/-- `3^(-k) + 2 * 5^(-k)`, for `k = 0, 1, ...`. -/
noncomputable def twoGeometricSeries (k : ℕ) : ℝ :=
  ((1 / 3 : ℝ) ^ k) + 2 * ((1 / 5 : ℝ) ^ k)

/-- `(-1)^k / (k+1)`, for `k = 0, 1, ...`. -/
noncomputable def alternatingHarmonic (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ k) / ((k : ℝ) + 1)

/-- `(-1)^(k+1) / (2(k+1)-1)`, for `k = 0, 1, ...`. -/
noncomputable def leibnizSeries (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ (k + 1)) / (2 * (k + 1 : ℝ) - 1)

/-- `1 / (k+1)^2`, for `k = 0, 1, ...`. -/
noncomputable def baselSeries (k : ℕ) : ℝ :=
  1 / ((k + 1 : ℝ) ^ 2)

/-- `1 / (k+1)^(3/2)`, for `k = 0, 1, ...`. -/
noncomputable def pSeriesThreeHalves (k : ℕ) : ℝ :=
  1 / (((k + 1 : ℝ) ^ ((3 : ℝ) / 2)))

/-- `1 / (k+1)!`, for `k = 0, 1, ...`. -/
noncomputable def reciprocalFactorials (k : ℕ) : ℝ :=
  1 / ((Nat.factorial (k + 1) : ℕ) : ℝ)

/-- `(-1)^(k+1) / (k+1)^2`, for `k = 0, 1, ...`. -/
noncomputable def alternatingBaselSeries (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ (k + 1)) / ((k + 1 : ℝ) ^ 2)

/-- `1 / (4(k+1)^2-1)`, for `k = 0, 1, ...`. -/
noncomputable def fourSquareMinusOne (k : ℕ) : ℝ :=
  1 / (4 * ((k + 1 : ℝ) ^ 2) - 1)

/-- `1 / (k+1)^(k+1)`, for `k = 0, 1, ...`. -/
noncomputable def reciprocalSelfPowers (k : ℕ) : ℝ :=
  1 / (((k + 1 : ℝ) ^ ((k + 1 : ℝ))))

/-- `1 / (2^(k+1)-1)`, for `k = 0, 1, ...`. -/
noncomputable def reciprocalMersenneNumbers (k : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ (k + 1) - 1)

/-- `1 / F_(k+1)`, where `F_1 = F_2 = 1`, for `k = 0, 1, ...`. -/
noncomputable def reciprocalFibonacci (k : ℕ) : ℝ :=
  1 / ((Nat.fib (k + 1) : ℕ) : ℝ)

/--
A two-branch result for a series.  The left branch contains a rational
approximation and a proof of summability; the right branch contains a proof
that the series is not summable.
-/
def SeriesSummabilityResult (f : ℕ → ℝ) (tol : ℝ) : Type :=
  { x : Rat //
      Summable f ∧
      abs (tsum f - x) < tol }
  ⊕' (¬ Summable f)

/-- The alternating harmonic series is not absolutely summable. -/
theorem alternatingHarmonic_not_summable :
    ¬ Summable alternatingHarmonic := by
  lynth

/-- The Leibniz series is not absolutely summable. -/
theorem leibnizSeries_not_summable :
    ¬ Summable leibnizSeries := by
  lynth

/-- **IS01** — `∑ 5(0.6)^k`; the expected value is `12.5`. -/
def geometricFiveSixthsResult :
    SeriesSummabilityResult geometricFiveSixths infiniteSumTolerance := by
  lynth

/-- **IS03** — `∑ (3^(-k) + 2*5^(-k))`; the expected value is `4`. -/
def twoGeometricSeriesResult :
    SeriesSummabilityResult twoGeometricSeries infiniteSumTolerance := by
  lynth

/-- **IS04** — `∑ (-1)^k/(k+1)`; the expected value is `log 2`, but the
series is conditionally rather than absolutely convergent. -/
def alternatingHarmonicResult :
    SeriesSummabilityResult alternatingHarmonic infiniteSumTolerance := by
  lynth

/-- **IS05** — `∑ (-1)^(k+1)/(2k-1)`; the expected value is `π/4`, but the
series is conditionally rather than absolutely convergent. -/
def leibnizSeriesResult :
    SeriesSummabilityResult leibnizSeries infiniteSumTolerance := by
  lynth

/-- **IS06** — `∑ 1/k^2`; the expected value is `π^2/6`. -/
def baselSeriesResult :
    SeriesSummabilityResult baselSeries infiniteSumTolerance := by
  lynth

/-- **IS09** — `∑ (-1)^(k+1)/k^2`; the expected value is `π^2/12`. This
alternating series is absolutely convergent. -/
def alternatingBaselSeriesResult :
    SeriesSummabilityResult alternatingBaselSeries infiniteSumTolerance := by
  lynth

/-- **IS02** — `∑ 1/(k(k+1))`; the expected value is `1`. -/
def telescopingReciprocalsSubtype :
    { x : Rat //
      Summable telescopingReciprocals ∧
      abs (tsum telescopingReciprocals - x) < infiniteSumTolerance } := by
  lynth

/-- **IS07** — `∑ 1/k^(3/2)`; the expected value is `ζ(3/2)`. -/
def pSeriesThreeHalvesSubtype :
    { x : Rat //
      Summable pSeriesThreeHalves ∧
      abs (tsum pSeriesThreeHalves - x) < infiniteSumTolerance } := by
  lynth

/-- **IS08** — `∑ 1/k!`; the expected value is `e - 1`. -/
def reciprocalFactorialsSubtype :
    { x : Rat //
      Summable reciprocalFactorials ∧
      abs (tsum reciprocalFactorials - x) < infiniteSumTolerance } := by
  lynth

/-- **IS10** — `∑ 1/(4k^2-1)`; the expected value is `1/2`. -/
def fourSquareMinusOneSubtype :
    { x : Rat //
      Summable fourSquareMinusOne ∧
      abs (tsum fourSquareMinusOne - x) < infiniteSumTolerance } := by
  lynth

/-- **IS11** — `∑ 1/k^k`; the expected value is `1.29128599706266...`. -/
def reciprocalSelfPowersSubtype :
    { x : Rat //
      Summable reciprocalSelfPowers ∧
      abs (tsum reciprocalSelfPowers - x) < infiniteSumTolerance } := by
  lynth

/-- **IS12** — `∑ 1/(2^k-1)`; the expected value is `1.60669515241529...`. -/
def reciprocalMersenneNumbersSubtype :
    { x : Rat //
      Summable reciprocalMersenneNumbers ∧
      abs (tsum reciprocalMersenneNumbers - x) < infiniteSumTolerance } := by
  lynth

/-- **IS13** — `∑ 1/F_n`, where `F_n` is Fibonacci; the expected value is
`3.35988566624318...`. -/
def reciprocalFibonacciSubtype :
    { x : Rat //
      Summable reciprocalFibonacci ∧
      abs (tsum reciprocalFibonacci - x) < infiniteSumTolerance } := by
  lynth

-- Axiom footprint checks.
/-- info: 'IntervalArith.infiniteSumTolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infiniteSumTolerance
/-- info: 'IntervalArith.geometricFiveSixths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms geometricFiveSixths
/-- info: 'IntervalArith.telescopingReciprocals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms telescopingReciprocals
/-- info: 'IntervalArith.twoGeometricSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoGeometricSeries
/-- info: 'IntervalArith.alternatingHarmonic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alternatingHarmonic
/-- info: 'IntervalArith.leibnizSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leibnizSeries
/-- info: 'IntervalArith.baselSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms baselSeries
/-- info: 'IntervalArith.pSeriesThreeHalves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pSeriesThreeHalves
/-- info: 'IntervalArith.reciprocalFactorials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalFactorials
/-- info: 'IntervalArith.alternatingBaselSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alternatingBaselSeries
/-- info: 'IntervalArith.fourSquareMinusOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fourSquareMinusOne
/-- info: 'IntervalArith.reciprocalSelfPowers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalSelfPowers
/-- info: 'IntervalArith.reciprocalMersenneNumbers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalMersenneNumbers
/-- info: 'IntervalArith.reciprocalFibonacci' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalFibonacci
/-- info: 'IntervalArith.SeriesSummabilityResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SeriesSummabilityResult
/-- info: 'IntervalArith.alternatingHarmonic_not_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alternatingHarmonic_not_summable
/-- info: 'IntervalArith.leibnizSeries_not_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leibnizSeries_not_summable
/-- info: 'IntervalArith.geometricFiveSixthsResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms geometricFiveSixthsResult
/-- info: 'IntervalArith.twoGeometricSeriesResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoGeometricSeriesResult
/-- info: 'IntervalArith.alternatingHarmonicResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alternatingHarmonicResult
/-- info: 'IntervalArith.leibnizSeriesResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leibnizSeriesResult
/-- info: 'IntervalArith.baselSeriesResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms baselSeriesResult
/-- info: 'IntervalArith.alternatingBaselSeriesResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alternatingBaselSeriesResult
/-- info: 'IntervalArith.telescopingReciprocalsSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms telescopingReciprocalsSubtype
/-- info: 'IntervalArith.pSeriesThreeHalvesSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pSeriesThreeHalvesSubtype
/-- info: 'IntervalArith.reciprocalFactorialsSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalFactorialsSubtype
/-- info: 'IntervalArith.fourSquareMinusOneSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fourSquareMinusOneSubtype
/-- info: 'IntervalArith.reciprocalSelfPowersSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalSelfPowersSubtype
/-- info: 'IntervalArith.reciprocalMersenneNumbersSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalMersenneNumbersSubtype
/-- info: 'IntervalArith.reciprocalFibonacciSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalFibonacciSubtype

end IntervalArith
