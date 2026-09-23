import Lynth.Grind.Tactic
example (x : Nat) : x ≥ (0 : Int) := by lynth_grind
example (x : Nat) : Int.ofNat x ≥ (0 : Int) := by lynth_grind
example (x : Nat) : NatCast.natCast x ≥ 0 := by lynth_grind
example (x : Nat) : x ≥ (-1 : Int) := by lynth_grind
example (x : Nat) : Int.ofNat x ≥ (-1 : Int) := by lynth_grind
example (x : Nat) : NatCast.natCast x ≥ -1 := by lynth_grind

example (n : Nat) : Nat.cast n = n := by
  lynth_grind

example (n m a : Nat) : n = m → Nat.cast n - a = m - a := by
  lynth_grind
