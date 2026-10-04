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
/-- info: 'IntervalArith.infiniteSumTolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infiniteSumTolerance

/-- `5 * (3/5)^k`, for `k = 0, 1, ...`. -/
noncomputable def geometricFiveSixths (k : ℕ) : ℝ :=
  5 * ((3 : ℝ) / 5) ^ k
/-- info: 'IntervalArith.geometricFiveSixths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms geometricFiveSixths

/-- `3^(-k) + 2 * 5^(-k)`, for `k = 0, 1, ...`. -/
noncomputable def twoGeometricSeries (k : ℕ) : ℝ :=
  ((1 / 3 : ℝ) ^ k) + 2 * ((1 / 5 : ℝ) ^ k)
/-- info: 'IntervalArith.twoGeometricSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoGeometricSeries

/-- `(-1)^k / (k+1)`, for `k = 0, 1, ...`. -/
noncomputable def alternatingHarmonic (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ k) / ((k : ℝ) + 1)
/-- info: 'IntervalArith.alternatingHarmonic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alternatingHarmonic

/-- `(-1)^(k+1) / (2(k+1)-1)`, for `k = 0, 1, ...`. -/
noncomputable def leibnizSeries (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ (k + 1)) / (2 * (k + 1 : ℝ) - 1)
/-- info: 'IntervalArith.leibnizSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leibnizSeries

/-- `1 / (k+1)^2`, for `k = 0, 1, ...`. -/
noncomputable def baselSeries (k : ℕ) : ℝ :=
  1 / ((k + 1 : ℝ) ^ 2)
/-- info: 'IntervalArith.baselSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms baselSeries

/-- `1 / (k+1)^(3/2)`, for `k = 0, 1, ...`. -/
noncomputable def pSeriesThreeHalves (k : ℕ) : ℝ :=
  1 / (((k + 1 : ℝ) ^ ((3 : ℝ) / 2)))
/-- info: 'IntervalArith.pSeriesThreeHalves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pSeriesThreeHalves

/-- `(-1)^(k+1) / (k+1)^2`, for `k = 0, 1, ...`. -/
noncomputable def alternatingBaselSeries (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ (k + 1)) / ((k + 1 : ℝ) ^ 2)
/-- info: 'IntervalArith.alternatingBaselSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alternatingBaselSeries

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
/-- info: 'IntervalArith.SeriesSummabilityResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SeriesSummabilityResult

/-- The alternating harmonic series is not absolutely summable. -/
theorem alternatingHarmonic_not_summable :
    ¬ Summable alternatingHarmonic := by
  lynth
/-- info: 'IntervalArith.alternatingHarmonic_not_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alternatingHarmonic_not_summable

/-- The Leibniz series is not absolutely summable. -/
theorem leibnizSeries_not_summable :
    ¬ Summable leibnizSeries := by
  lynth
/-- info: 'IntervalArith.leibnizSeries_not_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leibnizSeries_not_summable

/-- **IS01** — `∑ 5(0.6)^k`; the expected value is `12.5`. -/
def geometricFiveSixthsResult :
    SeriesSummabilityResult geometricFiveSixths infiniteSumTolerance := by
  lynth
/-- info: 'IntervalArith.geometricFiveSixthsResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms geometricFiveSixthsResult

/-- **IS03** — `∑ (3^(-k) + 2*5^(-k))`; the expected value is `4`. -/
def twoGeometricSeriesResult :
    SeriesSummabilityResult twoGeometricSeries infiniteSumTolerance := by
  lynth
/-- info: 'IntervalArith.twoGeometricSeriesResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoGeometricSeriesResult

/-- **IS04** — `∑ (-1)^k/(k+1)`; the expected value is `log 2`, but the
series is conditionally rather than absolutely convergent. -/
def alternatingHarmonicResult :
    SeriesSummabilityResult alternatingHarmonic infiniteSumTolerance := by
  lynth
/-- info: 'IntervalArith.alternatingHarmonicResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alternatingHarmonicResult

/-- **IS05** — `∑ (-1)^(k+1)/(2k-1)`; the expected value is `π/4`, but the
series is conditionally rather than absolutely convergent. -/
def leibnizSeriesResult :
    SeriesSummabilityResult leibnizSeries infiniteSumTolerance := by
  lynth
/-- info: 'IntervalArith.leibnizSeriesResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leibnizSeriesResult

/-- **IS06** — `∑ 1/k^2`; the expected value is `π^2/6`. -/
def baselSeriesResult :
    SeriesSummabilityResult baselSeries infiniteSumTolerance := by
  lynth
/-- info: 'IntervalArith.baselSeriesResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms baselSeriesResult

/-- **IS09** — `∑ (-1)^(k+1)/k^2`; the expected value is `π^2/12`. This
alternating series is absolutely convergent. -/
def alternatingBaselSeriesResult :
    SeriesSummabilityResult alternatingBaselSeries infiniteSumTolerance := by
  lynth
/-- info: 'IntervalArith.alternatingBaselSeriesResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alternatingBaselSeriesResult

/-- **IS07** — `∑ 1/k^(3/2)`; the expected value is `ζ(3/2)`. -/
def pSeriesThreeHalvesSubtype :
    { x : Rat //
      Summable pSeriesThreeHalves ∧
      abs (tsum pSeriesThreeHalves - x) < infiniteSumTolerance } := by
  lynth
/-- info: 'IntervalArith.pSeriesThreeHalvesSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pSeriesThreeHalvesSubtype
