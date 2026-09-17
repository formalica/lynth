-- BV procedure: bitvector identities via blast oracle + `bv_decide`.
import Lynth

theorem bv_add_zero (x : BitVec 8) : x + 0 = x := by lynth

theorem bv_add_comm (x y : BitVec 8) : x + y = y + x := by lynth

theorem bv_demorgan (x y : BitVec 8) :
    ~~~(x &&& y) = ~~~x ||| ~~~y := by lynth

theorem bv_xor_self (x : BitVec 8) : x ^^^ x = 0 := by lynth

theorem bv_add_succ_ne (x : BitVec 8) : (x + 1) ≠ x := by lynth

#print axioms bv_add_zero
#print axioms bv_add_comm
#print axioms bv_demorgan
#print axioms bv_xor_self
#print axioms bv_add_succ_ne
