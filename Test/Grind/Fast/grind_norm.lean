import Lynth.Grind.Tactic
opaque f : Nat → Nat
opaque g : Nat → Nat

@[grind norm] axiom fax : f x = x + 2
@[grind norm ←] axiom fg : f x = g x

example : f x ≥ 2 := by lynth_grind
example : f x ≥ g x := by lynth_grind
example : f x + g x ≥ 4 := by lynth_grind

@[grind unfold] def h (x : Nat) := 2 * x

example : 2 ∣ h x := by lynth_grind
