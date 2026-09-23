import Lynth.Grind.Tactic
namespace Nat

@[grind =]
theorem testBit_shiftRight_shiftLeft_add {n j k : Nat} (x : Nat) : (x >>> n <<< (n + k)).testBit j =
    (decide (n + k ≤ j) && x.testBit (j - k)) := by
  lynth_grind

theorem myTheorem {x : Nat} : x = x := by lynth_grind

end Nat
