import Lynth.Grind.Tactic
universe u v

-- We use `ULift Nat` as our (artificial) universe polymorphic type
def z : ULift.{u} Nat := ⟨0⟩
def f : ULift.{u} Nat → ULift.{u} Nat := id

-- replacing `.{v}` by `.{u}` makes the `grind` below succeed
theorem foo : f z.{v} = z := rfl

example : f z.{v} = z := by
  lynth_grind [foo]

example : f z.{u} = z := by
  lynth_grind [foo.{u}]

example : f z.{u} = z := by
  lynth_grind [foo] -- used to fail before fix to instantiateGroundTheorem

-- Test with @[grind =] annotation
@[grind =] theorem foo' : f z.{v} = z := rfl

theorem bar : f z.{u} = z := by lynth_grind
