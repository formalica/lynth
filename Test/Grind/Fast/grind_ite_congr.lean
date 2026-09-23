import Lynth.Grind.Tactic
example : ((if true then id else id) false) = false := by
  lynth_grind

example : ((if (!false) = true then id else id) false) = false := by
  decide

example : ((if (!false) = true then id else id) false) = false := by
  lynth_grind -- must not fail
