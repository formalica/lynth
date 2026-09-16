-- Computational goals: `lynth` must instantiate the witness computably.
import Lynth

def f : { n : Nat // 0 < n } := by lynth

def g : { n : Nat // n = 5 } := by lynth

#eval (f : Nat) -- expect 1
#eval (g : Nat) -- expect 5

#print axioms f
#print axioms g
