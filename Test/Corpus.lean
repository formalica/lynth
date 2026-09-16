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

theorem k5 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : b = c) :
    f a + 0 ≤ f c := by lynth

theorem k6 (p : Prop) : p ∨ ¬p := by lynth

theorem k7 (a : Nat) : (0 : Int) ≤ (a : Int) := by lynth

theorem k8 : ∀ i : Fin 3, i.val < 3 := by lynth

-- division/parity, abs, min/max, branching, powers
theorem k9 (n : Nat) (h : n % 2 = 0) : Even n := by lynth

theorem k10 (a : Int) : |a| ≥ 0 := by lynth

theorem k11 (a b : Nat) : min a b ≤ a := by lynth

theorem k12 (p : Prop) [Decidable p] (a b : Nat) :
    (if p then a else b) ≤ max a b := by lynth

theorem k13 (n : Nat) : 2 ^ n ≥ 1 := by lynth

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
#print axioms k5
#print axioms k6
#print axioms k7
#print axioms k8
#print axioms k9
#print axioms k10
#print axioms k11
#print axioms k12
#print axioms k13
