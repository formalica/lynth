import Mathlib
import Lynth

set_option maxHeartbeats 319 in
theorem closed_c1 : (1 : ℝ) / 3 + 1 / 7 < 1 / 2 := by lynth
/-- info: 'closed_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms closed_c1
set_option maxHeartbeats 478 in
theorem closed_c2 : Real.sqrt 2 < 1415 / 1000 ∧ 1414 / 1000 < Real.sqrt 2 := by lynth
/-- info: 'closed_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms closed_c2
set_option maxHeartbeats 1068 in
theorem closed_c3 : |Real.sqrt 2 * Real.sqrt 3 - Real.sqrt 6| < 1 / 10 ^ 12 := by lynth
/-- info: 'closed_c3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms closed_c3
set_option maxHeartbeats 373 in
theorem closed_c4 : (∑ k ∈ Finset.range 10, ((k : ℝ) + 1)⁻¹) < 3 := by lynth
/-- info: 'closed_c4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms closed_c4
set_option maxHeartbeats 1423 in
theorem closed_c5 : ‖(1 + 2 * Complex.I) * (3 - Complex.I)‖ < 71 / 10 := by lynth
/-- info: 'closed_c5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms closed_c5

