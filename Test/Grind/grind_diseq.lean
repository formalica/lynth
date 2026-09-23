import Lynth.Grind.Tactic
set_option grind.debug true

example (p q : Prop) (a b c d : Nat) :
     a = b → c = d → a ≠ c → (d ≠ b → p) → (d ≠ b → q) → p ∧ q := by
  lynth_grind (splits:=0)
