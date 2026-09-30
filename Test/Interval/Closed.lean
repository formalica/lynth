import Mathlib
import Lynth

theorem c1 : (1 : ℝ) / 3 + 1 / 7 < 1 / 2 := by lynth
theorem c2 : Real.sqrt 2 < 1415 / 1000 ∧ 1414 / 1000 < Real.sqrt 2 := by lynth
theorem c3 : |Real.sqrt 2 * Real.sqrt 3 - Real.sqrt 6| < 1 / 10 ^ 12 := by lynth
theorem c4 : (∑ k ∈ Finset.range 10, ((k : ℝ) + 1)⁻¹) < 3 := by lynth
theorem c5 : ‖(1 + 2 * Complex.I) * (3 - Complex.I)‖ < 71 / 10 := by lynth

#print axioms c1
#print axioms c3
#print axioms c4
#print axioms c5
