-- Tests mirroring `SPEC.md` examples literally.
import Lynth

section SpecMirror

variable (a b : Nat)

-- `theorem thm : a + b = b + a := by lynth`
theorem thm : a + b = b + a := by lynth

end SpecMirror

-- `def f : { n : Nat // P n } := by lynth` (computable witness + proof)
def f : { n : Nat // 0 < n } := by lynth

#eval (f : Nat) -- expect 1

/-- info: 'thm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms thm
/-- info: 'f' does not depend on any axioms -/
#guard_msgs in
#print axioms f
