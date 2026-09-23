import Lynth.Grind.Tactic
variable {α β : Type}

axiom foo (f : α → β) : β

axiom fooProp : β → Prop

axiom fooProp_foo {f : α → β} : fooProp (foo (fun x ↦ f x))
axiom fooProp_foo' {f : α → β} : fooProp (foo f)

attribute [grind ←] fooProp_foo -- should work

example {f : α → β} : fooProp (foo f) := by lynth_grind -- succeeds, using `fooProp_foo`

/--
info: Try these:
  [apply] lynth_grind only [← fooProp_foo]
  [apply] lynth_grind => instantiate only [← fooProp_foo]
-/
#guard_msgs in
example {f : α → β} : fooProp (foo f) := by lynth_grind? -- succeeds, using `fooProp_foo`

attribute [grind ←] fooProp_foo' -- succeeds

example {f : α → β} : fooProp (foo f) := by lynth_grind
