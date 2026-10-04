-- Tests mirroring `SPEC.md` examples literally.
import Lynth

section SpecMirror

variable (a b : Nat)

set_option maxHeartbeats 78 in
-- `theorem spec_thm : a + b = b + a := by lynth`
theorem spec_thm : a + b = b + a := by lynth
/-- info: 'spec_thm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms spec_thm

end SpecMirror

set_option maxHeartbeats 41 in
-- `def spec_f : { n : Nat // P n } := by lynth` (computable witness + proof)
def spec_f : { n : Nat // 0 < n } := by lynth
/-- info: 'spec_f' does not depend on any axioms -/
#guard_msgs in
#print axioms spec_f

#eval (spec_f : Nat) -- expect 1

