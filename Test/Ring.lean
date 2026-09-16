-- Ring procedure checks: nonlinear identities.
import Lynth

theorem ring_sq (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by lynth

theorem ring_mul_comm (x y : Int) : x * y = y * x := by lynth

theorem ring_distrib (a b c : Int) : a * (b + c) = a * b + a * c := by lynth

#print axioms ring_sq
#print axioms ring_mul_comm
#print axioms ring_distrib
