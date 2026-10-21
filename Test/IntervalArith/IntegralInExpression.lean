import Mathlib
import Lynth


/-! Integrals and finite/infinite sums as subexpressions. The mixed-binder
cases check both nesting orders and uniform tails depending on an integration
variable. Witness values are checked independently below each specification.
-/



open MeasureTheory
open Lean Elab Command in
elab "#check_expression_axioms " decl:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
  let axioms ← Lean.collectAxioms name
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := axioms.filter fun ax =>
    !standard.contains ax && !(ax.toString.contains "native_decide.ax")
  unless unexpected.isEmpty do
    throwError "unexpected axiom dependencies for {name}: {axioms}"

namespace IntervalArith.IntegralInExpression

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option lynth.interval.maxPrec 256

noncomputable def gaussian (x : ℝ) : ℝ := Real.exp (-(x ^ 2))

set_option maxHeartbeats 3816 in -- measured: 3634; +5%
def integralInsideProduct :
    {q : ℚ //
      IntervalIntegrable gaussian volume 0 1 ∧
      |2 * ((∫ x in (0 : ℝ)..1, gaussian x) - (q : ℝ)) * Real.exp 1| < 1 / 100000} := by
  lynth
#check_expression_axioms integralInsideProduct
#guard |integralInsideProduct.val - (746824 : ℚ) / 1000000| < 1 / 100000

set_option maxHeartbeats 13704 in -- measured: 13051; +5%
def sumInsideProduct :
    {q : ℚ //
      |2 * ((∑ k ∈ Finset.range 5, Real.exp (-(k : ℝ))) - (q : ℝ)) *
        Real.cos (1 / 3)| < 1 / 100000} := by
  lynth
#check_expression_axioms sumInsideProduct
#guard |sumInsideProduct.val - (15713174 : ℚ) / 10000000| < 1 / 100000

set_option maxHeartbeats 4896 in -- measured: 4662; +5%
def sumInsideIntegral :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => ∑ k ∈ Finset.range 3, (x + (k : ℝ))) volume 0 1 ∧
      |(∫ x in (0 : ℝ)..1, (∑ k ∈ Finset.range 3, (x + (k : ℝ)))) -
        (q : ℝ)| < 1 / 100000} := by
  lynth
#check_expression_axioms sumInsideIntegral
#guard |sumInsideIntegral.val - (9 / 2 : ℚ)| < 1 / 100000

set_option maxHeartbeats 16100 in -- measured: 15333; +5%
def integralInsideSum :
    {q : ℚ //
      |(∑ k ∈ Finset.range 3, (∫ x in (0 : ℝ)..1, (x + (k : ℝ)))) -
        (q : ℝ)| < 1 / 100000} := by
  lynth
#check_expression_axioms integralInsideSum
#guard |integralInsideSum.val - (9 / 2 : ℚ)| < 1 / 100000

set_option maxHeartbeats 2986 in -- measured: 2843; +5%
def seriesInsideProduct :
    {q : ℚ //
      Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) ∧
      |3 * (∑' k : ℕ, (1 / 2 : ℝ) ^ k) - (q : ℝ)| < 1 / 100000} := by
  lynth
#check_expression_axioms seriesInsideProduct
#guard |seriesInsideProduct.val - 6| < 1 / 100000

set_option maxHeartbeats 4317 in -- measured: 4111; +5%
/-- The ratio depends on the integration variable. The tail must hold for
its entire parameter interval, including points other than quadrature nodes. -/
def seriesInsideIntegral :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => ∑' k : ℕ, (x / 4) ^ k) volume 0 1 ∧
      |(∫ x in (0 : ℝ)..1, (∑' k : ℕ, (x / 4) ^ k)) - (q : ℝ)| < 1 / 100000} := by
  lynth
#check_expression_axioms seriesInsideIntegral
#guard |seriesInsideIntegral.val - (1150728289807 : ℚ) / 1000000000000| < 1 / 100000

set_option maxHeartbeats 56325 in -- measured: 53642; +5%
def integralInsideSeries :
    {q : ℚ //
      Summable (fun k : ℕ => ∫ x in (0 : ℝ)..1, (x / 4) ^ k) ∧
      |(∑' k : ℕ, (∫ x in (0 : ℝ)..1, (x / 4) ^ k)) - (q : ℝ)| < 1 / 10000} := by
  lynth
#check_expression_axioms integralInsideSeries
#guard |integralInsideSeries.val - (1150728289807 : ℚ) / 1000000000000| < 1 / 10000

set_option maxHeartbeats 20930 in -- measured: 19933; +5%
/-- An integral is a subexpression of the summand, rather than its head. -/
def arithmeticInsideSeries :
    {q : ℚ //
      |(∑' k : ℕ, (2 * (∫ x in (0 : ℝ)..1, (x / 4) ^ k) + (1 / 8 : ℝ) ^ k)) -
        (q : ℝ)| < 1 / 10000} := by
  lynth
#check_expression_axioms arithmeticInsideSeries
#guard |arithmeticInsideSeries.val - (3444313722471 : ℚ) / 1000000000000| < 1 / 10000

set_option maxHeartbeats 4844 in -- measured: 4613; +5%
/-- The integral's real binder shadows the sum's natural binder. -/
def shadowedBinders :
    {q : ℚ //
      |(∑ x ∈ Finset.range 3,
          (∫ x in (0 : ℝ)..1, (∑ k ∈ Finset.range 2, (x + (k : ℝ))))) -
        (q : ℝ)| < 1 / 100000} := by
  lynth
#check_expression_axioms shadowedBinders
#guard |shadowedBinders.val - 6| < 1 / 100000

set_option maxHeartbeats 5558 in -- measured: 5293; +5%
def variableIntegralEndpoints :
    {q : ℚ //
      |(∑ k ∈ Finset.range 3, (∫ x in (0 : ℝ)..((k + 1 : ℕ) : ℝ), Real.exp (-x))) -
        (q : ℝ)| < 1 / 10000} := by
  lynth
#check_expression_axioms variableIntegralEndpoints
#guard |variableIntegralEndpoints.val - (2446998207224 : ℚ) / 1000000000000| < 1 / 10000

set_option lynth.interval.trust "kernel" in
set_option maxHeartbeats 1790 in -- measured: 1704; +5%
def kernelComposition :
    {q : ℚ // |2 * ((∫ x in (0 : ℝ)..1, x) - (q : ℝ)) * 3| < 1 / 100} := by
  lynth
#check_expression_axioms kernelComposition
#guard |kernelComposition.val - (1 / 2 : ℚ)| < 1 / 100

set_option maxHeartbeats 5615 in -- measured: 5347; +5%
/-- Composition follows the requested precision, including irrational values. -/
def highPrecisionComposition :
    {q : ℚ //
      |2 * ((∫ x in (0 : ℝ)..1, gaussian x) - (q : ℝ)) * Real.exp 1| <
        1 / (10 : ℝ) ^ 25} := by
  lynth
#check_expression_axioms highPrecisionComposition
#guard |highPrecisionComposition.val - (746824 : ℚ) / 1000000| < 1 / 100000

set_option maxHeartbeats 1048 in -- measured: 998; +5%
theorem gaussianIntegralBoundedByTwo (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    |(∫ x in (0 : ℝ)..1, gaussian x) - z| < 2 := by
  lynth
#check_expression_axioms gaussianIntegralBoundedByTwo

set_option maxHeartbeats 1546 in -- measured: 1472; +5%
theorem expIntegralVariableEndpointBound : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
    (∫ x in (0 : ℝ)..z, Real.exp (-x)) < 2 := by
  lynth
#check_expression_axioms expIntegralVariableEndpointBound

set_option maxHeartbeats 1035 in -- measured: 985; +5%
theorem geometricSeriesBound (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun k : ℕ => (z / 4) ^ k) ∧ (∑' k : ℕ, (z / 4) ^ k) < 2 := by
  lynth
#check_expression_axioms geometricSeriesBound

noncomputable def aliasedIntegral : ℝ := ∫ x in (0 : ℝ)..1, gaussian x

set_option maxHeartbeats 2272 in -- measured: 2163; +5%
def aliasedIntegralProduct :
    {q : ℚ // |2 * (aliasedIntegral - (q : ℝ)) * 3| < 1 / 100000} := by
  lynth
#check_expression_axioms aliasedIntegralProduct
#guard |aliasedIntegralProduct.val - (746824 : ℚ) / 1000000| < 1 / 100000

set_option maxHeartbeats 40933 in -- measured: 38983; +5%
/-- The upper endpoint varies with the infinite summation index. -/
def seriesWithVariableEndpoints :
    {q : ℚ //
      |(∑' k : ℕ, (∫ _x in (0 : ℝ)..(1 / ((k : ℝ) + 1)), (1 / 2 : ℝ) ^ k)) -
        (q : ℝ)| < 1 / 10000} := by
  lynth
#check_expression_axioms seriesWithVariableEndpoints
#guard |seriesWithVariableEndpoints.val - (138629436112 : ℚ) / 100000000000| < 1 / 10000

set_option maxHeartbeats 6384 in -- measured: 6080; +5%
def linearSeriesInsideIntegral :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => 2 * (∑' k : ℕ, (x / 4) ^ k) + x) volume 0 1 ∧
      |(∫ x in (0 : ℝ)..1, (2 * (∑' k : ℕ, (x / 4) ^ k) + x)) -
        (q : ℝ)| < 1 / 100000} := by
  lynth
#check_expression_axioms linearSeriesInsideIntegral
#guard |linearSeriesInsideIntegral.val - (2801456579614 : ℚ) / 1000000000000| < 1 / 100000

set_option maxHeartbeats 7446 in -- measured: 7091; +5%
def functionsOfAggregates :
    {q : ℚ //
      |Real.exp (∫ x in (0 : ℝ)..1, x) + Real.sin (∑' k : ℕ, (1 / 2 : ℝ) ^ k) -
        (q : ℝ)| < 1 / 100000} := by
  lynth
#check_expression_axioms functionsOfAggregates
#guard |functionsOfAggregates.val - (2558018697526 : ℚ) / 1000000000000| < 1 / 100000

set_option maxHeartbeats 111128 in -- measured: 105836; +5%
/-- A tighter tolerance needs a prefix longer than the expression recursion budget. -/
def longSeriesPrefix :
    {q : ℚ //
      |(∑' k : ℕ, (∫ _x in (0 : ℝ)..1, (3 / 4 : ℝ) ^ k)) - (q : ℝ)| <
        1 / (10 : ℝ) ^ 12} := by
  lynth
#check_expression_axioms longSeriesPrefix
#guard |longSeriesPrefix.val - 4| < 1 / (10 : ℚ) ^ 12

set_option maxHeartbeats 14312 in -- measured: 13630; +5%
def squaredIntegralSeries :
    {q : ℚ //
      Summable (fun k : ℕ => (∫ _x in (0 : ℝ)..1, (1 / 2 : ℝ) ^ k) ^ 2) ∧
      |(∑' k : ℕ, (∫ _x in (0 : ℝ)..1, (1 / 2 : ℝ) ^ k) ^ 2) -
        (q : ℝ)| < 1 / 100000} := by
  lynth
#check_expression_axioms squaredIntegralSeries
#guard |squaredIntegralSeries.val - (4 / 3 : ℚ)| < 1 / 100000

set_option maxHeartbeats 170379 in -- measured: 162265; +5%
theorem expGeometricSeriesIntegralBound :
    IntervalIntegrable (fun x : ℝ => Real.exp (∑' k : ℕ, (x / 4) ^ k)) volume 0 1 ∧
      (∫ x in (0 : ℝ)..1, Real.exp (∑' k : ℕ, (x / 4) ^ k)) < 4 := by
  lynth
#check_expression_axioms expGeometricSeriesIntegralBound

/-- A finite prefix cannot certify a divergent infinite series. -/
example : True := by
  run_tac
    let target ← Lean.Elab.Term.elabTerm (← `(term|
      {q : ℚ // |2 * (∑' _k : ℕ, (1 : ℝ)) - (q : ℝ)| < 1 / 10})) none
    if (← Lynth.Interval.Goals.Composition.run? target).isSome then
      throwError "composition accepted a divergent series"
  trivial

end IntervalArith.IntegralInExpression
