-- BV procedure: bitvector identities via blast oracle + `bv_decide`.
import Lynth

theorem bv_add_succ_ne (x : BitVec 8) : (x + 1) ≠ x := by lynth
/-- info: 'bv_add_succ_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bv_add_succ_ne
