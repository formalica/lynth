import Lynth.Grind.Tactic
import Lean

set_library_suggestions Lean.LibrarySuggestions.sineQuaNonSelector

-- Test that grind? +suggestions does NOT include +suggestions in its output
/--
info: Try this:
  [apply] lynth_grind only
-/
#guard_msgs in
example {x y : Nat} (h : x = y) : y = x := by
  lynth_grind? +suggestions

def f (x : α) := x

/--
info: Try these:
  [apply] lynth_grind only [f]
  [apply] lynth_grind => instantiate only [f]
-/
#guard_msgs in
example {x y : Nat} (h : x = y) : x = f y := by
  lynth_grind? +suggestions [f]
