-- Cross-fragment corpus: every procedure must route correctly.
import Lynth

theorem c1 (a b : Nat) (h : a = b) : b = a := by lynth

theorem c2 (p q : Prop) (h : p ∧ ¬p) : q := by lynth

theorem c3 (x : Int) : x + 0 = x := by lynth

theorem c4 (n : Nat) : n * 1 = n := by lynth

theorem c5 (a b c : Int) (h : a < b) (k : b < c) : a < c := by lynth

theorem c6 (p : Prop) : ¬¬p → p := by lynth

def c7 : { n : Nat // n > 3 ∧ n < 6 } := by lynth

theorem c8 (f : Nat → Nat) (a b : Nat) (h : a = b) : f (f a) = f (f b) := by lynth

theorem c9 (x y : Int) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by lynth

theorem c10 : (2 + 2 : Nat) = 4 := by lynth

-- combinations: rewriting + arithmetic + propositions together
theorem k1 (a b : Nat) (h : a = b) : a + 1 ≤ b + 1 := by lynth

theorem k2 (x y : Int) (h1 : x = y) (h2 : x + 1 ≤ 0) : y + 1 ≤ 0 := by lynth

theorem k3 (a b : Nat) (h : 2 * a = 2 * b) : a = b := by lynth

theorem k4 (p : Prop) (h : p) (n : Nat) : n + 0 = n ∧ p := by lynth

#eval (c7 : Nat) -- expect 4

#print axioms c1
#print axioms c2
#print axioms c3
#print axioms c4
#print axioms c5
#print axioms c6
#print axioms c7
#print axioms c8
#print axioms c9
#print axioms c10
#print axioms k1
#print axioms k2
#print axioms k3
#print axioms k4
