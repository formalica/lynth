-- Datatypes theory: injectivity edges + discrimination closes.
import Lynth

/-- Injectivity: `some a = some b` splinters, `assumption` finishes. -/
theorem dt_inj_option (a b : Nat) (h : some a = some b) : a = b := by lynth

/-- Injectivity over lists: head equality splinters off. -/
theorem dt_inj_list (a b : Nat) (as bs : List Nat)
    (h : a :: as = b :: bs) : a = b := by lynth

/-- Nested constructors splinter through bounded rounds. -/
theorem dt_inj_nested (a b : Nat)
    (h : some (some a) = some (some b)) : a = b := by lynth

/-- Discrimination goal closes via intro + injection. -/
theorem dt_discr_goal (a : Nat) : some a ≠ none := by lynth

/-- Contradictory equation closes any goal. -/
theorem dt_discr_false (a : Nat) (h : some a = none) : False := by lynth

/-- No-op: plain variable equality is EUF's job, untouched. -/
theorem dt_noop (a b : Nat) (h : a = b) : b = a := by lynth

#print axioms dt_inj_option
#print axioms dt_inj_list
#print axioms dt_inj_nested
#print axioms dt_discr_goal
#print axioms dt_discr_false
#print axioms dt_noop
