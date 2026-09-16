-- End-to-end `lynth` checks: propositions + linear arithmetic.
-- Each theorem must depend only on Lean native axioms
-- (`propext`, `Classical.choice`, `Quot.sound`).
import Lynth

theorem thm_add_comm (a b : Nat) : a + b = b + a := by lynth

theorem thm_triv (p : Prop) (h : p) : p := by lynth

theorem thm_and (p q : Prop) (hp : p) (hq : q) : p ∧ q := by lynth

theorem thm_arith (x y : Int) (h : x + 2 * y = 10) : 2 * x + 4 * y = 20 := by lynth

-- genuine propositional tautologies (oracle reports `true` for these)
theorem thm_mp (p q : Prop) : (p → q) → p → q := by lynth

theorem thm_conj_elim (p q : Prop) : p ∧ q → p := by lynth

theorem thm_disj_comm (p q : Prop) : p ∨ q → q ∨ p := by lynth

#print axioms thm_add_comm
#print axioms thm_triv
#print axioms thm_and
#print axioms thm_arith
#print axioms thm_mp
#print axioms thm_conj_elim
#print axioms thm_disj_comm
