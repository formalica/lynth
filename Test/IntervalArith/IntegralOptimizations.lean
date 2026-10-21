import Mathlib
import Lynth


/-! Focused regressions for large trigonometric phases and half-integer
powers. Each cap is ceil(105 * measured / 100), measured with Mathlib's
`#count_heartbeats in` on a temporary copy. -/

open Lean Elab Command in
elab "#check_integral_axioms " decl:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
  let axioms ← Lean.collectAxioms name
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := axioms.filter fun ax =>
    !standard.contains ax && !(ax.toString.contains "native_decide.ax")
  unless unexpected.isEmpty do
    throwError "unexpected axiom dependencies for {name}: {axioms}"

namespace IntervalArith.IntegralOptimizations

open MeasureTheory

set_option maxRecDepth 10000

set_option maxHeartbeats 4589 in -- measured: 4370; +5%
def largeTrigPhase :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => Real.sin (30000+x)) volume 0 1 ∧
      |(∫ x in (0 : ℝ)..1, Real.sin (30000+x)) - (q : ℝ)| < 1/100000} := by
  lynth
#check_integral_axioms largeTrigPhase
#guard |largeTrigPhase.val - (-949596961102/10^12 : ℚ)| < 1/100000

set_option maxHeartbeats 10345 in -- measured: 9852; +5%
def positiveHalfPower :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => x^(3/2 : ℝ)) volume 1 4 ∧
      |(∫ x in (1 : ℝ)..4, x^(3/2 : ℝ)) - (q : ℝ)| < 1/100000} := by
  lynth
#check_integral_axioms positiveHalfPower
#guard |positiveHalfPower.val - (62/5 : ℚ)| < 1/100000

set_option maxHeartbeats 11031 in -- measured: 10505; +5%
def negativeHalfPower :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => (1+x)^(-3/2 : ℝ)) volume 0 1 ∧
      |(∫ x in (0 : ℝ)..1, (1+x)^(-3/2 : ℝ)) - (q : ℝ)| < 1/100000} := by
  lynth
#check_integral_axioms negativeHalfPower
#guard |negativeHalfPower.val - (585786437627/10^12 : ℚ)| < 1/100000

set_option maxHeartbeats 1469 in -- measured: 1399; +5%
/-- Exercise logarithmic jump isolation on a short interval. The original
FLINT 16 problem on [0,8] remains a performance regression in
TestFailures/IntervalArith/Integrals.lean. -/
def fractionalExpJumps :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => (Real.exp x - (⌊Real.exp x⌋ : ℤ)) *
        Real.sin (x+Real.exp x)) volume 0 2 ∧
      |(∫ x in (0 : ℝ)..2, (Real.exp x - (⌊Real.exp x⌋ : ℤ)) *
        Real.sin (x+Real.exp x)) - (q : ℝ)| < 1/100000} := by
  lynth
#check_integral_axioms fractionalExpJumps
#guard |fractionalExpJumps.val - (157425052409/10^12 : ℚ)| < 1/100000

set_option maxHeartbeats 9978 in -- measured: 9502; +5%
/-- The cancellation rule also handles polynomial amplitudes and negative
reciprocal frequencies. -/
def weightedReciprocalSin :
    {q : ℚ //
      IntervalIntegrable (fun x : ℝ => x^2 * Real.sin (-3/x)) volume 0 1 ∧
      |(∫ x in (0 : ℝ)..1, x^2 * Real.sin (-3/x)) - (q : ℝ)| < 1/100000} := by
  lynth
#check_integral_axioms weightedReciprocalSin
#guard |weightedReciprocalSin.val - (121302220667/10^12 : ℚ)| < 1/100000

set_option maxHeartbeats 1558 in -- measured: 1483; +5%
/-- Endpoint uncertainty must survive when both rounded midpoints coincide. -/
def closeEndpoints :
    {q : ℚ //
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume
        (1+1/(10:ℝ)^100) (1+2/(10:ℝ)^100) ∧
      |(∫ _ in (1+1/(10:ℝ)^100)..(1+2/(10:ℝ)^100), (1 : ℝ)) - (q : ℝ)| <
        1/(10:ℝ)^110} := by
  lynth
#check_integral_axioms closeEndpoints
#guard |closeEndpoints.val - (1/(10:ℚ)^100)| < 1/(10:ℚ)^110

end IntervalArith.IntegralOptimizations
