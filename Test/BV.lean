-- BV procedure: bitvector identities via blast oracle + `bv_decide`.
import Lynth

set_option maxHeartbeats 66 in
theorem bv_add_zero (x : BitVec 8) : x + 0 = x := by lynth
/-- info: 'bv_add_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bv_add_zero

set_option maxHeartbeats 1034 in
theorem bv_add_comm (x y : BitVec 8) : x + y = y + x := by lynth
/-- info: 'bv_add_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bv_add_comm

set_option maxHeartbeats 71 in
theorem bv_demorgan (x y : BitVec 8) :
    ~~~(x &&& y) = ~~~x ||| ~~~y := by lynth
/-- info: 'bv_demorgan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bv_demorgan

set_option maxHeartbeats 46 in
theorem bv_xor_self (x : BitVec 8) : x ^^^ x = 0 := by lynth
/-- info: 'bv_xor_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bv_xor_self
