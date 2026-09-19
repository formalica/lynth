-- Robustness: contradictory contexts, trivial goals, decidables, Nat order.
import Lynth

theorem false_of_contra (p : Prop) (h1 : p) (h2 : ¬p) : False := by lynth

theorem true_goal : True := by lynth

theorem iff_refl (p : Prop) : p ↔ p := by lynth

theorem ne_decide : 1 ≠ 2 := by lynth

theorem nat_le_trans (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by lynth

/-- info: 'false_of_contra' depends on axioms: [propext] -/
#guard_msgs in
#print axioms false_of_contra
/-- info: 'true_goal' does not depend on any axioms -/
#guard_msgs in
#print axioms true_goal
/-- info: 'iff_refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms iff_refl
/-- info: 'ne_decide' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ne_decide
/-- info: 'nat_le_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nat_le_trans
