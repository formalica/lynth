-- Computational goals: `lynth` must instantiate the witness computably.
import Lynth

def f : { n : Nat // 0 < n } := by lynth

def g : { n : Nat // n = 5 } := by lynth

-- Int witnesses: search interleaves 0, 1, -1, …
def hneg : { n : Int // n < 0 } := by lynth

def hpos : { n : Int // n = 42 } := by lynth

#eval (f : Nat) -- expect 1
#eval (g : Nat) -- expect 5
#eval (hneg : Int) -- expect -1
#eval (hpos : Int) -- expect 42

#print axioms f
#print axioms g
#print axioms hneg
#print axioms hpos
