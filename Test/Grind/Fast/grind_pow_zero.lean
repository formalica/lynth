import Lynth.Grind.Tactic
open Lean Grind

example [CommRing α] (a : α) : a^0 = 1 := by lynth_grind

example [CommSemiring α] [AddRightCancel α] (a : α) : a^0 = 1 := by lynth_grind
example [CommRing α] (a : α) : a^1 = a := by lynth_grind
example [CommRing α] (a : α) : a^2 = a*a := by lynth_grind

example [Field α] (a : α) : b ≠ 0 → a ≠ 0 → a * (b / a) / b = 1 := by lynth_grind
