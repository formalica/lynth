-- End-to-end `lynth` checks: propositions + linear arithmetic.
-- Each theorem must depend only on Lean native axioms
-- (`propext`, `Classical.choice`, `Quot.sound`).
import Lynth

set_option maxHeartbeats 77 in
theorem thm_add_comm (a b : Nat) : a + b = b + a := by lynth
/-- info: 'thm_add_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms thm_add_comm

set_option maxHeartbeats 19 in
theorem thm_triv (p : Prop) (h : p) : p := by lynth
/-- info: 'thm_triv' does not depend on any axioms -/
#guard_msgs in
#print axioms thm_triv

set_option maxHeartbeats 48 in
theorem thm_and (p q : Prop) (hp : p) (hq : q) : p ∧ q := by lynth
/-- info: 'thm_and' depends on axioms: [propext] -/
#guard_msgs in
#print axioms thm_and

set_option maxHeartbeats 1014 in
theorem thm_arith (x y : Int) (h : x + 2 * y = 10) : 2 * x + 4 * y = 20 := by lynth
/-- info: 'thm_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thm_arith

set_option maxHeartbeats 57 in
-- genuine propositional tautologies (oracle reports `true` for these)
theorem thm_mp (p q : Prop) : (p → q) → p → q := by lynth
/-- info: 'thm_mp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms thm_mp

set_option maxHeartbeats 39 in
theorem thm_conj_elim (p q : Prop) : p ∧ q → p := by lynth
/-- info: 'thm_conj_elim' depends on axioms: [propext] -/
#guard_msgs in
#print axioms thm_conj_elim

set_option maxHeartbeats 78 in
theorem thm_disj_comm (p q : Prop) : p ∨ q → q ∨ p := by lynth
/-- info: 'thm_disj_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thm_disj_comm

set_option maxHeartbeats 47 in
-- hypothesis-driven: oracle must see the context, not just the goal
theorem thm_hyp_mp (p q : Prop) (h1 : p → q) (h2 : p) : q := by lynth
/-- info: 'thm_hyp_mp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms thm_hyp_mp

set_option maxHeartbeats 60 in
theorem thm_hyp_conj (p q r : Prop) (h : p ∧ q) : q ∧ p ∧ (p ∨ r) := by lynth
/-- info: 'thm_hyp_conj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms thm_hyp_conj

