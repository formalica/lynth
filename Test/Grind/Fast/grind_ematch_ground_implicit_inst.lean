import Lynth.Grind.Tactic
example (a : Nat) : max a a = a := by
  lynth_grind

instance : Max Nat where
  max := Nat.max

example (a : Nat) : max a a = a := by
  lynth_grind
