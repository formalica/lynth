import Lynth.Grind.Tactic
example : (List.range' 1 n).drop (List.range' 1 n).length = [] := by lynth_grind -- solves
example : [].sum = 0 := by lynth_grind -- solves
example : ((List.range' 1 n).drop (List.range' 1 n).length).sum = 0 := by lynth_grind -- solves
example : ((List.range' 1 n).take (List.range' 1 n).length).sum = (List.range' 1 n).sum := by lynth_grind -- solves
example (as bs : List Nat) : ((as ++ bs).take (as ++ bs).length).sum = (as ++ bs).sum := by lynth_grind -- solves
example (as bs : List Nat) : ((as ++ bs).take (as ++ bs).length).sum = bs.sum + as.sum := by lynth_grind -- solves
