import Mathlib
import Lynth

set_option maxHeartbeats 685 in
def a1 : { x : ℚ // |Real.sqrt 2 - x| < 1 / 10 ^ 10 } := by lynth
#print axioms a1
set_option maxHeartbeats 643 in
def a2 : { x : ℚ // abs ((1 : ℝ) / 3 - x) < 1 / 1000 } := by lynth
#print axioms a2
set_option maxHeartbeats 735 in
def a3 : { x : ℚ // |(x : ℝ) - Real.sqrt 3 * 2| < 1 / 100 } := by lynth
#print axioms a3
#eval a1.1
#eval a2.1
#eval a3.1
