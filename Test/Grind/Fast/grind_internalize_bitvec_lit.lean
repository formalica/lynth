import Lynth.Grind.Tactic
attribute [grind? =] BitVec.sdiv_zero

example {x : BitVec 32} : x.sdiv 0#32 = 0#32 := by
  lynth_grind

example {x : BitVec 32} : x.sdiv 0#32 = 0#32 := by
  lynth_grind -ext
