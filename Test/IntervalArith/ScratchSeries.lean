module
public import Lynth
import Mathlib

local syntax (name := lynthSeries) "lynth_series" : tactic

open Lean Elab Tactic in
@[local tactic lynthSeries]
private meta def lynthSeriesImpl : Tactic := fun _ => do
  let g ← getMainGoal
  let some pf ← Lynth.Interval.Goals.proveSeries? (← Lean.instantiateMVars (← g.getType))
    | throwError "series: no proof"
  g.assign pf
  replaceMainGoal []

namespace IntervalArith

set_option maxHeartbeats 27 in
public noncomputable def scratchSeries_infiniteSumTolerance : ℝ := 1 / 100000

set_option maxHeartbeats 46 in
public noncomputable def scratchSeries_alternatingHarmonic (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ k) / ((k : ℝ) + 1)

set_option maxHeartbeats 567 in
set_option profiler true in
public theorem alternatingHarmonic_not_summable :
    ¬ Summable scratchSeries_alternatingHarmonic := by
  lynth_series
/-- info: 'IntervalArith.alternatingHarmonic_not_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alternatingHarmonic_not_summable


/-- info: 'IntervalArith.scratchSeries_infiniteSumTolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scratchSeries_infiniteSumTolerance
/-- info: 'IntervalArith.scratchSeries_alternatingHarmonic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scratchSeries_alternatingHarmonic

end IntervalArith
