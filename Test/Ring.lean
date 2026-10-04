-- Ring procedure checks: nonlinear identities.
import Lynth

set_option maxHeartbeats 269 in
theorem ring_sq (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by lynth
/-- info: 'ring_sq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ring_sq

set_option maxHeartbeats 57 in
theorem ring_mul_comm (x y : Int) : x * y = y * x := by lynth
/-- info: 'ring_mul_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ring_mul_comm

set_option maxHeartbeats 81 in
theorem ring_distrib (a b c : Int) : a * (b + c) = a * b + a * c := by lynth
/-- info: 'ring_distrib' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ring_distrib

