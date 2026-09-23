import Lynth.Grind.Tactic
example (x : Nat) (h : x < 0) : Nat → Nat := by
  lynth_grind

example : False → Nat := by
  lynth_grind

example : (x : Nat) → x < 0 → Nat := by
  lynth_grind

example : (x : Nat) → x < 3 → x > 4 → Nat := by
  lynth_grind
