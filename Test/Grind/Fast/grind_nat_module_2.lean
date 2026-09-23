import Lynth.Grind.Tactic
open Std Lean.Grind

section NatModule

variable (M : Type) [NatModule M] [AddRightCancel M]

example (x y : M) : 2 • x + 3 • y + x = 3 • (x + y) := by lynth_grind

variable [LE M] [IsLinearOrder M] [OrderedAdd M]

example {x y : M} (h : x ≤ y) : 2 • x + y ≤ 3 • y := by lynth_grind

end NatModule
