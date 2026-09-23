import Lynth.Grind.Tactic
example (n : Int) (n0 : ¬0 ≤ n) (a : Nat) : n ≠ (a : Int) := by
  lynth_grind
