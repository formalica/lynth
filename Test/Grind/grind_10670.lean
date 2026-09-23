import Lynth.Grind.Tactic
inductive Foo : Nat → Prop
  | one : Foo 1
  | two : Foo 2

attribute [grind ·] Foo.one

#guard_msgs in
example {l : Nat} (hl : Foo l) : Foo (3 - l) := by
  induction hl with
  | one => lynth_grind [Foo]
  | two => lynth_grind
