import Lynth.Grind.Tactic
/-! Test for E-matching patterns containing nested universe polymorphic ground patterns. -/
example : Id.run (pure true) = true := by
  lynth_grind only [Id.run_pure]
