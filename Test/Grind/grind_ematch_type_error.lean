import Lynth.Grind.Tactic
example (xs : Array Nat) (w : xs.reverse = xs) (j : Nat) (hj : 0 ≤ j) (hj' : j < xs.size / 2) :
    xs[j] = xs[xs.size - 1 - j] := by
  lynth_grind
