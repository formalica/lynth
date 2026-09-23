import Lynth.Grind.Tactic
example (x y : Nat) : (x : Int) - (y : Int) = 0 → x = y := by
  lynth_grind

example (x y : Nat) : (x : Int) - (y : Int) ≤ 0 → (x : Int) - (y : Int) ≥ 0 → x = y := by
  lynth_grind

example (x y : Nat) : (x : Int) = (y : Int) → x = y := by
  lynth_grind
