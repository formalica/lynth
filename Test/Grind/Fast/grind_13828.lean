import Lynth.Grind.Tactic

/-!
Regression test for #13828: `grind?` suggestions used to omit `cases` parameters
(e.g., `cases Bool`), producing suggestions that failed during replay. The parameters
marking types for case-splitting must be preserved in the suggestions.
-/

/--
info: Try these:
  [apply] lynth_grind only [#bd83, cases Bool]
  [apply] lynth_grind only [cases Bool]
  [apply] lynth_grind [cases Bool] => cases #bd83
-/
#guard_msgs (info) in
example (f : Bool → Bool) (x : Bool) (h₁ : f true = true) (h₂ : f false = true) :
    f (f (f x)) = f x := by
  lynth_grind? only [cases Bool]

/--
info: Try these:
  [apply] lynth_grind only [#bd83, #0173, cases Option]
  [apply] lynth_grind only [cases Option]
  [apply] lynth_grind [cases Option] => cases #bd83 <;> instantiate only [#0173]
-/
#guard_msgs (info) in
example (x : Option Nat) : x = none ∨ ∃ n, x = some n := by
  lynth_grind? [cases Option]

/-! Check that the suggestions above actually work. -/

example (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases h₁ : f true <;> cases h₂ : f false <;> lynth_grind only [#bd83, cases Bool]

example (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases h₁ : f true <;> cases h₂ : f false <;> lynth_grind only [cases Bool]

example (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases h₁ : f true <;> cases h₂ : f false <;> lynth_grind [cases Bool] => cases #bd83

example (x : Option Nat) : x = none ∨ ∃ n, x = some n := by
  lynth_grind only [#bd83, #0173, cases Option]

example (x : Option Nat) : x = none ∨ ∃ n, x = some n := by
  lynth_grind only [cases Option]

example (x : Option Nat) : x = none ∨ ∃ n, x = some n := by
  lynth_grind [cases Option] => cases #bd83 <;> instantiate only [#0173]
