import Lynth.Grind.Tactic
inductive C where
  | a | b | c

def f : C → Nat
  | .a => 2
  | .b => 3
  | .c => 4

example : f .a > 1 := by
  lynth_grind [f]

example : f x > 1 := by
  lynth_grind [f, C]
