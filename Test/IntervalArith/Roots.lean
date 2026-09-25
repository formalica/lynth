import Mathlib
import Lynth

namespace IntervalArith

/-- R01 — root of `r^5 - r - 1 = 0` on `[1, 3/2]`.
Etalon: `1.1673039782614187`. -/
def rootQuintic :
    { x : Rat //
      1 ≤ (x : ℝ) ∧
      (x : ℝ) ≤ 3 / 2 ∧
      abs ((x : ℝ) ^ 5 - (x : ℝ) - 1) <
        1 / 100000000 } := by
  lynth

/-- R02 — positive root of `exp r = r + 2` on `[1, 3/2]`.
Etalon: `1.14619322062058`. -/
def rootExpLinear :
    { x : Rat //
      1 ≤ (x : ℝ) ∧
      (x : ℝ) ≤ 3 / 2 ∧
      abs (Real.exp (x : ℝ) - (x : ℝ) - 2) <
        1 / 100000000 } := by
  lynth

/-- info: 'IntervalArith.rootQuintic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootQuintic

/-- info: 'IntervalArith.rootExpLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootExpLinear

end IntervalArith
