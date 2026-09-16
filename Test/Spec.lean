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

#print axioms thm
#print axioms f
