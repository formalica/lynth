-- Nonlinear procedure checks: squares, products, AM-GM-shaped goals.
import Lynth

theorem nlin_sq (a b : Int) : 0 ≤ (a - b) * (a - b) := by lynth

theorem nlin_sq_nat (n : Nat) : 0 ≤ n * n := by lynth

theorem nlin_sq_sum (a b : Int) : 0 ≤ a * a + b * b := by lynth

#print axioms nlin_sq
#print axioms nlin_sq_nat
#print axioms nlin_sq_sum
