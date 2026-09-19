-- README claims, executed (guards documentation).
import Lynth

theorem thm (a b : Nat) : a + b = b + a := by lynth

def f : { n : Nat // 0 < n } := by lynth

#eval (f : Nat) -- 1

theorem ex : ∃ n : Int, n < 0 := by lynth

def pp : { p : Nat × Nat // p.1 + p.2 = 3 } := by lynth

/-- info: 'thm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms thm
/-- info: 'f' does not depend on any axioms -/
#guard_msgs in
#print axioms f
/-- info: 'ex' does not depend on any axioms -/
#guard_msgs in
#print axioms ex
/-- info: 'pp' does not depend on any axioms -/
#guard_msgs in
#print axioms pp
