import Lynth.Grind.Tactic
example (x y z : Nat) : x &&& (y ||| z) = (x &&& y) ||| (x &&& z) := by lynth_grind
example (w x y z : Nat) : (w ||| x) &&& (y ||| z) = (w &&& y) ||| (w &&& z) ||| (x &&& y) ||| (x &&& z) := by lynth_grind

example (x y z : Nat) : x &&& (y ^^^ z) = (x &&& y) ^^^ (x &&& z) := by lynth_grind
example (w x y z : Nat) : (w ^^^ x) &&& (y ^^^ z) = (w &&& y) ^^^ (w &&& z) ^^^ (x &&& y) ^^^ (x &&& z) := by lynth_grind
