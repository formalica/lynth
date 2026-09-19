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

/-- info: 'f' does not depend on any axioms -/
#guard_msgs in
#print axioms f
/-- info: 'g' does not depend on any axioms -/
#guard_msgs in
#print axioms g
/-- info: 'hneg' does not depend on any axioms -/
#guard_msgs in
#print axioms hneg
/-- info: 'hpos' does not depend on any axioms -/
#guard_msgs in
#print axioms hpos
/-- info: 'btrue' does not depend on any axioms -/
#guard_msgs in
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

/-- info: 'ex_nat' does not depend on any axioms -/
#guard_msgs in
#print axioms ex_nat
/-- info: 'ex_int' does not depend on any axioms -/
#guard_msgs in
#print axioms ex_int
/-- info: 'ex_conj' does not depend on any axioms -/
#guard_msgs in
#print axioms ex_conj
/-- info: 'ex_big' does not depend on any axioms -/
#guard_msgs in
#print axioms ex_big
/-- info: 'pp' does not depend on any axioms -/
#guard_msgs in
#print axioms pp

-- finite domains enumerate completely
def ff : { i : Fin 5 // i.val > 2 } := by lynth

#eval (ff : Fin 5) -- expect 3
#eval (ff : Nat) -- expect 3

/-- info: 'ff' does not depend on any axioms -/
#guard_msgs in
#print axioms ff

-- inductive predicates as side conditions go through the same probes
theorem even_ex : ∃ n : Nat, Even n ∧ n > 10 := by lynth

-- nested existentials: outer witness + tactic side-close compose
theorem nest1 : ∃ a : Nat, ∃ b : Nat, a + b = 3 := by lynth

theorem sq_ex : ∃ x : Int, x > 0 ∧ x < 5 ∧ x * x = 16 := by lynth

theorem mix1 (p : Nat → Prop) (h : ∀ n, p n) : ∃ n, p (n + 1) := by lynth

-- bound-directed synthesis: thresholds beyond enumeration range
theorem thr1 : ∃ n : Nat, n > 100 := by lynth

def thr2 : { n : Nat // 100 ≤ n ∧ n ≤ 105 } := by lynth

theorem thr3 : ∃ n : Int, n < -100 := by lynth

-- beyond enumeration range: needs bound direction, not luck
theorem far1 : ∃ n : Nat, n > 1000 := by lynth

/-- info: 'even_ex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms even_ex
/-- info: 'nest1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nest1
/-- info: 'sq_ex' does not depend on any axioms -/
#guard_msgs in
#print axioms sq_ex
/-- info: 'mix1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mix1
/-- info: 'thr1' does not depend on any axioms -/
#guard_msgs in
#print axioms thr1
/-- info: 'thr2' does not depend on any axioms -/
#guard_msgs in
#print axioms thr2
/-- info: 'thr3' does not depend on any axioms -/
#guard_msgs in
#print axioms thr3
/-- info: 'far1' does not depend on any axioms -/
#guard_msgs in
#print axioms far1
