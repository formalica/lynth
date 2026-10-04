import Mathlib
import Lynth

set_option maxHeartbeats 336 in
theorem closed_c1 : (1 : ℝ) / 3 + 1 / 7 < 1 / 2 := by lynth
#print axioms closed_c1
set_option maxHeartbeats 403 in
theorem closed_c2 : Real.sqrt 2 < 1415 / 1000 ∧ 1414 / 1000 < Real.sqrt 2 := by lynth
#print axioms closed_c2
set_option maxHeartbeats 582 in
theorem closed_c3 : |Real.sqrt 2 * Real.sqrt 3 - Real.sqrt 6| < 1 / 10 ^ 12 := by lynth
#print axioms closed_c3
set_option maxHeartbeats 386 in
theorem closed_c4 : (∑ k ∈ Finset.range 10, ((k : ℝ) + 1)⁻¹) < 3 := by lynth
#print axioms closed_c4
set_option maxHeartbeats 639 in
theorem closed_c5 : ‖(1 + 2 * Complex.I) * (3 - Complex.I)‖ < 71 / 10 := by lynth
#print axioms closed_c5

