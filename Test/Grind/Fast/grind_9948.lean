import Lynth.Grind.Tactic
theorem sum_of_n (n : Nat) :
  (List.range (n + 1)).sum = n * (n + 1) / 2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    lynth_grind [List.range_succ]
