-- Robustness: contradictory contexts, trivial goals, decidables, Nat order.
import Lynth

theorem false_of_contra (p : Prop) (h1 : p) (h2 : ¬p) : False := by lynth

theorem true_goal : True := by lynth

theorem iff_refl (p : Prop) : p ↔ p := by lynth

theorem ne_decide : 1 ≠ 2 := by lynth

theorem nat_le_trans (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by lynth

#print axioms false_of_contra
#print axioms true_goal
#print axioms iff_refl
#print axioms ne_decide
#print axioms nat_le_trans
