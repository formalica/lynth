-- Computational goals: `lynth` must instantiate the witness computably.
import Lynth

def f : { n : Nat // 0 < n } := by lynth

def g : { n : Nat // n = 5 } := by lynth

-- Int witnesses: search interleaves 0, 1, -1, …
def hneg : { n : Int // n < 0 } := by lynth

def hpos : { n : Int // n = 42 } := by lynth

-- Bool witnesses
def btrue : { b : Bool // b = true } := by lynth

#eval (f : Nat) -- expect 1
#eval (g : Nat) -- expect 5
#eval (hneg : Int) -- expect -1
#eval (hpos : Int) -- expect 42
#eval btrue -- expect true

#print axioms f
#print axioms g
#print axioms hneg
#print axioms hpos
#print axioms btrue

-- existential goals use the same enumeration machinery
theorem ex_nat : ∃ n : Nat, n > 5 := by lynth

theorem ex_int : ∃ n : Int, n < 0 := by lynth

theorem ex_conj : ∃ n : Nat, n > 3 ∧ n < 6 := by lynth

-- larger witnesses within the raised bound
theorem ex_big : ∃ n : Nat, n = 100 := by lynth

-- product domains enumerate diagonally
def pp : { p : Nat × Nat // p.1 + p.2 = 3 } := by lynth

#eval (pp : Nat × Nat) -- expect (0, 3)

#print axioms ex_nat
#print axioms ex_int
#print axioms ex_conj
#print axioms ex_big
#print axioms pp

-- finite domains enumerate completely
def ff : { i : Fin 5 // i.val > 2 } := by lynth

#eval (ff : Fin 5) -- expect 3
#eval (ff : Nat) -- expect 3

#print axioms ff
