-- Nonlinear procedure checks: squares, products, AM-GM-shaped goals.
import Lynth

theorem nlin_sq (a b : Int) : 0 ≤ (a - b) * (a - b) := by lynth

theorem nlin_sq_nat (n : Nat) : 0 ≤ n * n := by lynth

theorem nlin_sq_sum (a b : Int) : 0 ≤ a * a + b * b := by lynth

/-- info: 'nlin_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nlin_sq
/-- info: 'nlin_sq_nat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms nlin_sq_nat
/-- info: 'nlin_sq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nlin_sq_sum
