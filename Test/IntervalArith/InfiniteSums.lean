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

set_option maxHeartbeats 28 in
/-- Common tolerance for the rational witnesses. -/
noncomputable def infiniteSums_infiniteSumTolerance : ℝ := 1 / 100000
/-- info: 'IntervalArith.infiniteSums_infiniteSumTolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infiniteSums_infiniteSumTolerance

set_option maxHeartbeats 46 in
/-- `5 * (3/5)^k`, for `k = 0, 1, ...`. -/
noncomputable def geometricFiveSixths (k : ℕ) : ℝ :=
  5 * ((3 : ℝ) / 5) ^ k
/-- info: 'IntervalArith.geometricFiveSixths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms geometricFiveSixths

set_option maxHeartbeats 68 in
/-- `1 / ((k+1)(k+2))`, for `k = 0, 1, ...`. -/
noncomputable def telescopingReciprocals (k : ℕ) : ℝ :=
  1 / (((k + 1 : ℝ) * (k + 2 : ℝ)))
/-- info: 'IntervalArith.telescopingReciprocals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms telescopingReciprocals

set_option maxHeartbeats 76 in
/-- `3^(-k) + 2 * 5^(-k)`, for `k = 0, 1, ...`. -/
noncomputable def twoGeometricSeries (k : ℕ) : ℝ :=
  ((1 / 3 : ℝ) ^ k) + 2 * ((1 / 5 : ℝ) ^ k)
/-- info: 'IntervalArith.twoGeometricSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoGeometricSeries

set_option maxHeartbeats 45 in
/-- `(-1)^k / (k+1)`, for `k = 0, 1, ...`. -/
noncomputable def infiniteSums_alternatingHarmonic (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ k) / ((k : ℝ) + 1)
/-- info: 'IntervalArith.infiniteSums_alternatingHarmonic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infiniteSums_alternatingHarmonic

set_option maxHeartbeats 88 in
/-- `(-1)^(k+1) / (2(k+1)-1)`, for `k = 0, 1, ...`. -/
noncomputable def leibnizSeries (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ (k + 1)) / (2 * (k + 1 : ℝ) - 1)
/-- info: 'IntervalArith.leibnizSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leibnizSeries

set_option maxHeartbeats 63 in
/-- `1 / (k+1)^2`, for `k = 0, 1, ...`. -/
noncomputable def baselSeries (k : ℕ) : ℝ :=
  1 / ((k + 1 : ℝ) ^ 2)
/-- info: 'IntervalArith.baselSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms baselSeries

set_option maxHeartbeats 63 in
/-- `1 / (k+1)^(3/2)`, for `k = 0, 1, ...`. -/
noncomputable def pSeriesThreeHalves (k : ℕ) : ℝ :=
  1 / (((k + 1 : ℝ) ^ ((3 : ℝ) / 2)))
/-- info: 'IntervalArith.pSeriesThreeHalves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pSeriesThreeHalves

set_option maxHeartbeats 41 in
/-- `1 / (k+1)!`, for `k = 0, 1, ...`. -/
noncomputable def reciprocalFactorials (k : ℕ) : ℝ :=
  1 / ((Nat.factorial (k + 1) : ℕ) : ℝ)
/-- info: 'IntervalArith.reciprocalFactorials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalFactorials

set_option maxHeartbeats 78 in
/-- `(-1)^(k+1) / (k+1)^2`, for `k = 0, 1, ...`. -/
noncomputable def alternatingBaselSeries (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ (k + 1)) / ((k + 1 : ℝ) ^ 2)
/-- info: 'IntervalArith.alternatingBaselSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alternatingBaselSeries

set_option maxHeartbeats 99 in
/-- `1 / (4(k+1)^2-1)`, for `k = 0, 1, ...`. -/
noncomputable def fourSquareMinusOne (k : ℕ) : ℝ :=
  1 / (4 * ((k + 1 : ℝ) ^ 2) - 1)
/-- info: 'IntervalArith.fourSquareMinusOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fourSquareMinusOne

set_option maxHeartbeats 60 in
/-- `1 / (k+1)^(k+1)`, for `k = 0, 1, ...`. -/
noncomputable def reciprocalSelfPowers (k : ℕ) : ℝ :=
  1 / (((k + 1 : ℝ) ^ ((k + 1 : ℝ))))
/-- info: 'IntervalArith.reciprocalSelfPowers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalSelfPowers

set_option maxHeartbeats 55 in
/-- `1 / (2^(k+1)-1)`, for `k = 0, 1, ...`. -/
noncomputable def reciprocalMersenneNumbers (k : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ (k + 1) - 1)
/-- info: 'IntervalArith.reciprocalMersenneNumbers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalMersenneNumbers

set_option maxHeartbeats 41 in
/-- `1 / F_(k+1)`, where `F_1 = F_2 = 1`, for `k = 0, 1, ...`. -/
noncomputable def reciprocalFibonacci (k : ℕ) : ℝ :=
  1 / ((Nat.fib (k + 1) : ℕ) : ℝ)
/-- info: 'IntervalArith.reciprocalFibonacci' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalFibonacci

set_option maxHeartbeats 51 in
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

set_option maxHeartbeats 46987 in
/-- **IS02** — `∑ 1/(k(k+1))`; the expected value is `1`. -/
def telescopingReciprocalsSubtype :
    { x : Rat //
      Summable telescopingReciprocals ∧
      abs (tsum telescopingReciprocals - x) < infiniteSums_infiniteSumTolerance } := by
  lynth
/-- info: 'IntervalArith.telescopingReciprocalsSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms telescopingReciprocalsSubtype

set_option maxHeartbeats 947 in
/-- **IS08** — `∑ 1/k!`; the expected value is `e - 1`. -/
def reciprocalFactorialsSubtype :
    { x : Rat //
      Summable reciprocalFactorials ∧
      abs (tsum reciprocalFactorials - x) < infiniteSums_infiniteSumTolerance } := by
  lynth
/-- info: 'IntervalArith.reciprocalFactorialsSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalFactorialsSubtype

set_option maxHeartbeats 30416 in
/-- **IS10** — `∑ 1/(4k^2-1)`; the expected value is `1/2`. -/
def fourSquareMinusOneSubtype :
    { x : Rat //
      Summable fourSquareMinusOne ∧
      abs (tsum fourSquareMinusOne - x) < infiniteSums_infiniteSumTolerance } := by
  lynth
/-- info: 'IntervalArith.fourSquareMinusOneSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fourSquareMinusOneSubtype

set_option maxHeartbeats 21405 in
/-- **IS11** — `∑ 1/k^k`; the expected value is `1.29128599706266...`. -/
def reciprocalSelfPowersSubtype :
    { x : Rat //
      Summable reciprocalSelfPowers ∧
      abs (tsum reciprocalSelfPowers - x) < infiniteSums_infiniteSumTolerance } := by
  lynth
/-- info: 'IntervalArith.reciprocalSelfPowersSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalSelfPowersSubtype

set_option maxHeartbeats 3010 in
/-- **IS12** — `∑ 1/(2^k-1)`; the expected value is `1.60669515241529...`. -/
def reciprocalMersenneNumbersSubtype :
    { x : Rat //
      Summable reciprocalMersenneNumbers ∧
      abs (tsum reciprocalMersenneNumbers - x) < infiniteSums_infiniteSumTolerance } := by
  lynth
/-- info: 'IntervalArith.reciprocalMersenneNumbersSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalMersenneNumbersSubtype

set_option maxHeartbeats 2076 in
/-- **IS13** — `∑ 1/F_n`, where `F_n` is Fibonacci; the expected value is
`3.35988566624318...`. -/
def reciprocalFibonacciSubtype :
    { x : Rat //
      Summable reciprocalFibonacci ∧
      abs (tsum reciprocalFibonacci - x) < infiniteSums_infiniteSumTolerance } := by
  lynth
/-- info: 'IntervalArith.reciprocalFibonacciSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reciprocalFibonacciSubtype

-- Axiom footprint checks.

end IntervalArith
