import Lynth.Grind.Tactic
example (f : α → β) (h : Function.Injective f)
    : f a = f b → a = b := by
  lynth_grind
