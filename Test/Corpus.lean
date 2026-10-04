-- Cross-fragment corpus: every procedure must route correctly.
import Lynth

set_option maxHeartbeats 16 in
theorem corpus_c1 (a b : Nat) (h : a = b) : b = a := by lynth
/-- info: 'corpus_c1' does not depend on any axioms -/
#guard_msgs in
#print axioms corpus_c1

set_option maxHeartbeats 17 in
theorem corpus_c2 (p q : Prop) (h : p ∧ ¬p) : q := by lynth
/-- info: 'corpus_c2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms corpus_c2

set_option maxHeartbeats 61 in
theorem corpus_c3 (x : Int) : x + 0 = x := by lynth
/-- info: 'corpus_c3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms corpus_c3

set_option maxHeartbeats 72 in
theorem corpus_c4 (n : Nat) : n * 1 = n := by lynth
/-- info: 'corpus_c4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms corpus_c4

set_option maxHeartbeats 1276 in
theorem corpus_c5 (a b c : Int) (h : a < b) (k : b < c) : a < c := by lynth
/-- info: 'corpus_c5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms corpus_c5

set_option maxHeartbeats 39 in
theorem c6 (p : Prop) : ¬¬p → p := by lynth
/-- info: 'c6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms c6

set_option maxHeartbeats 58 in
def c7 : { n : Nat // n > 3 ∧ n < 6 } := by lynth
/-- info: 'c7' does not depend on any axioms -/
#guard_msgs in
#print axioms c7

set_option maxHeartbeats 28 in
theorem c8 (f : Nat → Nat) (a b : Nat) (h : a = b) : f (f a) = f (f b) := by lynth
/-- info: 'c8' does not depend on any axioms -/
#guard_msgs in
#print axioms c8

set_option maxHeartbeats 266 in
theorem c9 (x y : Int) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by lynth
/-- info: 'c9' depends on axioms: [propext] -/
#guard_msgs in
#print axioms c9

set_option maxHeartbeats 76 in
theorem c10 : (2 + 2 : Nat) = 4 := by lynth
/-- info: 'c10' depends on axioms: [propext] -/
#guard_msgs in
#print axioms c10

set_option maxHeartbeats 287 in
-- combinations: rewriting + arithmetic + propositions together
theorem k1 (a b : Nat) (h : a = b) : a + 1 ≤ b + 1 := by lynth
/-- info: 'k1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms k1

set_option maxHeartbeats 497 in
theorem k3 (a b : Nat) (h : 2 * a = 2 * b) : a = b := by lynth
/-- info: 'k3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms k3

set_option maxHeartbeats 165 in
theorem k4 (p : Prop) (h : p) (n : Nat) : n + 0 = n ∧ p := by lynth
/-- info: 'k4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms k4

set_option maxHeartbeats 219 in
theorem k5 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : b = c) :
    f a + 0 ≤ f c := by lynth
/-- info: 'k5' depends on axioms: [propext] -/
#guard_msgs in
#print axioms k5

set_option maxHeartbeats 41 in
theorem k6 (p : Prop) : p ∨ ¬p := by lynth
/-- info: 'k6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms k6

set_option maxHeartbeats 259 in
theorem k7 (a : Nat) : (0 : Int) ≤ (a : Int) := by lynth
/-- info: 'k7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms k7

set_option maxHeartbeats 117 in
theorem k8 : ∀ i : Fin 3, i.val < 3 := by lynth
/-- info: 'k8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms k8

set_option maxHeartbeats 3792 in
-- division/parity, abs, min/max, branching, powers
theorem k9 (n : Nat) (h : n % 2 = 0) : Even n := by lynth
/-- info: 'k9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms k9

set_option maxHeartbeats 279 in
theorem k10 (a : Int) : |a| ≥ 0 := by lynth
/-- info: 'k10' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms k10

set_option maxHeartbeats 234 in
theorem k11 (a b : Nat) : min a b ≤ a := by lynth
/-- info: 'k11' depends on axioms: [propext] -/
#guard_msgs in
#print axioms k11

set_option maxHeartbeats 499 in
theorem k12 (p : Prop) [Decidable p] (a b : Nat) :
    (if p then a else b) ≤ max a b := by lynth
/-- info: 'k12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms k12

set_option maxHeartbeats 517 in
theorem k13 (n : Nat) : 2 ^ n ≥ 1 := by lynth
/-- info: 'k13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms k13

#eval (c7 : Nat) -- expect 4
