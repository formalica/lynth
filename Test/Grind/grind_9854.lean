import Lynth.Grind.Tactic
example (x: Nat) : UInt32.size - x < UInt64.size := by
  lynth_grind only
