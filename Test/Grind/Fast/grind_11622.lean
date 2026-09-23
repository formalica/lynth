import Lynth.Grind.Tactic
example {x y : Int} : y = 0 → (x.fdiv y) = 0 := by lynth_grind
example {x y : Int} : y = 0 → (x.tdiv y) = 0 := by lynth_grind
example {x y : Int} : y = 0 → (x.fmod y) = x := by lynth_grind
example {x y : Int} : y = 1 → (x.fdiv (2 - y)) = x := by lynth_grind
example {x : Int} : x > 0 → x.sign = 1 := by lynth_grind
example {x : Int} : x < 0 → x.sign = -1 := by lynth_grind
example {x y : Int} : x.sign = 0 → x*y = 0 := by lynth_grind
