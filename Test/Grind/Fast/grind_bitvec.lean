import Lynth.Grind.Tactic
open BitVec

example (x : BitVec (w+1)) : (cons x.msb (x.setWidth w)) = x := by
  lynth_grind

example {x : BitVec v} (h : w ≤ v) : BitVec.setWidth w (-x) = -BitVec.setWidth w x := by
  lynth_grind
