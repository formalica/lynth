import Lynth.Grind.Tactic
open Lean Grind

attribute [local instance] Semiring.natCast Ring.intCast

example [CommRing α] (a : α) : Int.cast (R := α) (-2) = a → a + 2 = 0 := by
  lynth_grind

example [CommRing α] (a : α) : Nat.cast (R := α) 2 = a → a - 2 = 0 := by
  lynth_grind

example [CommRing α] [IsCharP α 4] (a : α) : Int.cast (R := α) (-2) = a → a + 2 = 0 := by
  lynth_grind

example [CommRing α] [IsCharP α 4] (a : α) : Nat.cast (R := α) 2 = a → a - 2 = 0 := by
  lynth_grind
