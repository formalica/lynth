import Lynth.Grind.Tactic
reset_grind_attrs%
attribute [grind] List.not_mem_nil

/-!
Note: the following definition used to fail because the goal mentions the
declaration `incList` being defined.
-/

def incList (as : List Nat) : { as : List Nat // ∀ a, a ∈ as → a > 0 } :=
  match as with
  | [] => ⟨[], by lynth_grind⟩
  | a::as => ⟨(incList as).1, by lynth_grind⟩
