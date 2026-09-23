import Lynth.Grind.Tactic

set_option grind.debug true in
theorem mwe2 (n : Nat) : [d][n]?.getD d = d := by
  lynth_grind
