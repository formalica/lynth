import Mathlib
import Lynth.Interval.Goals.Series

open Lean Elab Tactic in
elab "lynth_series" : tactic => do
  let g ← getMainGoal
  let some pf ← Lynth.Interval.Goals.proveSeries? (← Lean.instantiateMVars (← g.getType))
    | throwError "series: no proof"
  g.assign pf
  replaceMainGoal []

namespace IntervalArith

set_option maxHeartbeats 28 in
noncomputable def scratchSeries_infiniteSumTolerance : ℝ := 1 / 100000

set_option maxHeartbeats 45 in
noncomputable def scratchSeries_alternatingHarmonic (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ k) / ((k : ℝ) + 1)

set_option maxHeartbeats 212 in
set_option profiler true in
theorem alternatingHarmonic_not_summable :
    ¬ Summable scratchSeries_alternatingHarmonic := by
  lynth_series
#print axioms alternatingHarmonic_not_summable


end IntervalArith
