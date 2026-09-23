import Lynth.Grind.Tactic
@[grind =] def f : Nat → Nat
  | 0 => 0
  | n + 1 => f n

theorem foo (n : Nat) : f n = 0 := by
  match n with
  | 0 => lynth_grind
  | n + 1 => lynth_grind [foo n]
