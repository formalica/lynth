import Lynth.Grind.Tactic
example [LT α] [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] {b : α} (h : b < b) : False := by lynth_grind
