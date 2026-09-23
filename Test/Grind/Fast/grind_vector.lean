import Lynth.Grind.Tactic

/-!
Tests for `grind` support for vectors, including componentwise algebraic operations.
-/

example [BEq α] (xs ys : Vector α n) : (xs.toList == ys.toList) = (xs == ys) := by lynth_grind

example [LT α] {xs ys : Vector α n} : xs.toList < ys.toList ↔ xs < ys := by lynth_grind

example (xs ys zs : Vector Nat n) : (xs + ys) + zs = xs + (ys + zs) := by lynth_grind

example (xs : Vector Int n) : -xs + xs = 0 := by lynth_grind

section

attribute [local instance] Vector.instMul

example (xs ys zs : Vector Nat n) : xs * (ys + zs) = xs * ys + xs * zs := by lynth_grind

end

example (c d : Nat) (xs : Vector Nat n) : (c + d) • xs = c • xs + d • xs := by lynth_grind

example (c : Nat) (xs ys : Vector Nat n) : c * (xs + ys) = c * xs + c * ys := by lynth_grind
