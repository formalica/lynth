import Mathlib
import Lynth

def a1 : { x : ℚ // |Real.sqrt 2 - x| < 1 / 10 ^ 10 } := by lynth
def a2 : { x : ℚ // abs ((1 : ℝ) / 3 - x) < 1 / 1000 } := by lynth
def a3 : { x : ℚ // |(x : ℝ) - Real.sqrt 3 * 2| < 1 / 100 } := by lynth
#eval a1.1
#eval a2.1
#eval a3.1
#print axioms a1
