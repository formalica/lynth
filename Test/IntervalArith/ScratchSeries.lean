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

noncomputable def infiniteSumTolerance : ℝ := 1 / 100000

noncomputable def alternatingHarmonic (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ k) / ((k : ℝ) + 1)

set_option profiler true in
theorem alternatingHarmonic_not_summable :
    ¬ Summable alternatingHarmonic := by
  lynth_series

#print axioms alternatingHarmonic_not_summable

end IntervalArith
