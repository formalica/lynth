-- Robustness: contradictory contexts, trivial goals, decidables, Nat order.
import Lynth

set_option maxHeartbeats 17 in
theorem false_of_contra (p : Prop) (h1 : p) (h2 : ¬p) : False := by lynth
/-- info: 'false_of_contra' depends on axioms: [propext] -/
#guard_msgs in
#print axioms false_of_contra

set_option maxHeartbeats 21 in
theorem true_goal : True := by lynth
/-- info: 'true_goal' does not depend on any axioms -/
#guard_msgs in
#print axioms true_goal

set_option maxHeartbeats 28 in
theorem iff_refl (p : Prop) : p ↔ p := by lynth
/-- info: 'iff_refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms iff_refl

set_option maxHeartbeats 71 in
theorem ne_decide : 1 ≠ 2 := by lynth
/-- info: 'ne_decide' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ne_decide

set_option maxHeartbeats 376 in
theorem nat_le_trans (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by lynth
/-- info: 'nat_le_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nat_le_trans

