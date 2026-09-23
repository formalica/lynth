import Lynth.Grind.Tactic
example {a b : Nat} (ha : 1 ≤ a) : (a - 1 + 1) * b = a * b := by lynth_grind

example {a b : Nat} (ha : 1 ≤ a) : (a - 1 + 1) * b = a * b := by
  lynth_grind => done
