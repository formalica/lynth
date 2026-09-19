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

-- user-defined inductives: nothing is hardcoded (recognition via
-- `isConstructorApp?`, proofs via core `injections`)
inductive DtColor where
  | red | green | blue

inductive DtTree (α : Type) where
  | leaf : DtTree α
  | node : α → DtTree α → DtTree α → DtTree α

theorem dt_custom_inj (a b : Nat) (l1 l2 r1 r2 : DtTree Nat)
    (h : DtTree.node a l1 r1 = DtTree.node b l2 r2) : a = b := by lynth

theorem dt_custom_discr : DtColor.red ≠ DtColor.green := by lynth

theorem dt_custom_discr2 (t : DtTree Nat) :
    DtTree.leaf ≠ DtTree.node 1 t t := by lynth

/-- info: 'dt_inj_option' does not depend on any axioms -/
#guard_msgs in
#print axioms dt_inj_option
/-- info: 'dt_inj_list' does not depend on any axioms -/
#guard_msgs in
#print axioms dt_inj_list
/-- info: 'dt_inj_nested' does not depend on any axioms -/
#guard_msgs in
#print axioms dt_inj_nested
/-- info: 'dt_discr_goal' does not depend on any axioms -/
#guard_msgs in
#print axioms dt_discr_goal
/-- info: 'dt_discr_false' does not depend on any axioms -/
#guard_msgs in
#print axioms dt_discr_false
/-- info: 'dt_noop' does not depend on any axioms -/
#guard_msgs in
#print axioms dt_noop
/-- info: 'dt_custom_inj' does not depend on any axioms -/
#guard_msgs in
#print axioms dt_custom_inj
/-- info: 'dt_custom_discr' does not depend on any axioms -/
#guard_msgs in
#print axioms dt_custom_discr
/-- info: 'dt_custom_discr2' does not depend on any axioms -/
#guard_msgs in
#print axioms dt_custom_discr2
