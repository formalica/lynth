-- Computational goals: `lynth` must instantiate the witness computably.
import Lynth

set_option maxHeartbeats 44 in
def witness_f : { n : Nat // 0 < n } := by lynth
/-- info: 'witness_f' does not depend on any axioms -/
#guard_msgs in
#print axioms witness_f

set_option maxHeartbeats 28 in
def g : { n : Nat // n = 5 } := by lynth
/-- info: 'g' does not depend on any axioms -/
#guard_msgs in
#print axioms g

set_option maxHeartbeats 54 in
-- Int witnesses: search interleaves 0, 1, -1, …
def hneg : { n : Int // n < 0 } := by lynth
/-- info: 'hneg' does not depend on any axioms -/
#guard_msgs in
#print axioms hneg

set_option maxHeartbeats 32 in
def hpos : { n : Int // n = 42 } := by lynth
/-- info: 'hpos' does not depend on any axioms -/
#guard_msgs in
#print axioms hpos

set_option maxHeartbeats 24 in
-- Bool witnesses
def btrue : { b : Bool // b = true } := by lynth
/-- info: 'btrue' does not depend on any axioms -/
#guard_msgs in
#print axioms btrue

#eval (witness_f : Nat) -- expect 1
#eval (g : Nat) -- expect 5
#eval (hneg : Int) -- expect -1
#eval (hpos : Int) -- expect 42
#eval btrue -- expect true


set_option maxHeartbeats 35 in
-- existential goals use the same enumeration machinery
theorem ex_nat : ∃ n : Nat, n > 5 := by lynth
/-- info: 'ex_nat' does not depend on any axioms -/
#guard_msgs in
#print axioms ex_nat

set_option maxHeartbeats 46 in
theorem ex_int : ∃ n : Int, n < 0 := by lynth
/-- info: 'ex_int' does not depend on any axioms -/
#guard_msgs in
#print axioms ex_int

set_option maxHeartbeats 50 in
theorem ex_conj : ∃ n : Nat, n > 3 ∧ n < 6 := by lynth
/-- info: 'ex_conj' does not depend on any axioms -/
#guard_msgs in
#print axioms ex_conj

set_option maxHeartbeats 23 in
-- larger witnesses within the raised bound
theorem ex_big : ∃ n : Nat, n = 100 := by lynth
/-- info: 'ex_big' does not depend on any axioms -/
#guard_msgs in
#print axioms ex_big

set_option maxHeartbeats 114 in
-- product domains enumerate diagonally
def witness_pp : { p : Nat × Nat // p.1 + p.2 = 3 } := by lynth
/-- info: 'witness_pp' does not depend on any axioms -/
#guard_msgs in
#print axioms witness_pp

#eval (witness_pp : Nat × Nat) -- expect (0, 3)


set_option maxHeartbeats 65 in
-- finite domains enumerate completely
def ff : { i : Fin 5 // i.val > 2 } := by lynth
/-- info: 'ff' does not depend on any axioms -/
#guard_msgs in
#print axioms ff

#eval (ff : Fin 5) -- expect 3
#eval (ff : Nat) -- expect 3


set_option maxHeartbeats 47 in
-- inductive predicates as side conditions go through the same probes
theorem even_ex : ∃ n : Nat, Even n ∧ n > 10 := by lynth
/-- info: 'even_ex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms even_ex

set_option maxHeartbeats 200 in
-- nested existentials: outer witness + tactic side-close compose
theorem nest1 : ∃ a : Nat, ∃ b : Nat, a + b = 3 := by lynth
/-- info: 'nest1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nest1

set_option maxHeartbeats 116 in
theorem sq_ex : ∃ x : Int, x > 0 ∧ x < 5 ∧ x * x = 16 := by lynth
/-- info: 'sq_ex' does not depend on any axioms -/
#guard_msgs in
#print axioms sq_ex

set_option maxHeartbeats 73 in
theorem mix1 (p : Nat → Prop) (h : ∀ n, p n) : ∃ n, p (n + 1) := by lynth
/-- info: 'mix1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mix1

set_option maxHeartbeats 34 in
-- bound-directed synthesis: thresholds beyond enumeration range
theorem thr1 : ∃ n : Nat, n > 100 := by lynth
/-- info: 'thr1' does not depend on any axioms -/
#guard_msgs in
#print axioms thr1

set_option maxHeartbeats 55 in
def thr2 : { n : Nat // 100 ≤ n ∧ n ≤ 105 } := by lynth
/-- info: 'thr2' does not depend on any axioms -/
#guard_msgs in
#print axioms thr2

set_option maxHeartbeats 588 in
theorem thr3 : ∃ n : Int, n < -100 := by lynth
/-- info: 'thr3' does not depend on any axioms -/
#guard_msgs in
#print axioms thr3

set_option maxHeartbeats 34 in
-- beyond enumeration range: needs bound direction, not luck
theorem far1 : ∃ n : Nat, n > 1000 := by lynth
/-- info: 'far1' does not depend on any axioms -/
#guard_msgs in
#print axioms far1

