-- README claims, executed (guards documentation).
import Lynth

set_option maxHeartbeats 77 in
theorem readme_thm (a b : Nat) : a + b = b + a := by lynth
/-- info: 'readme_thm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms readme_thm

set_option maxHeartbeats 41 in
def readme_f : { n : Nat // 0 < n } := by lynth
/-- info: 'readme_f' does not depend on any axioms -/
#guard_msgs in
#print axioms readme_f

#eval (readme_f : Nat) -- 1

set_option maxHeartbeats 47 in
theorem ex : ∃ n : Int, n < 0 := by lynth
/-- info: 'ex' does not depend on any axioms -/
#guard_msgs in
#print axioms ex

set_option maxHeartbeats 114 in
def readme_pp : { p : Nat × Nat // p.1 + p.2 = 3 } := by lynth
/-- info: 'readme_pp' does not depend on any axioms -/
#guard_msgs in
#print axioms readme_pp

