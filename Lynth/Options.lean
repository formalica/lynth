module

public import Lean.Data.Options

/-! User options for the `lynth` tactic. -/

public section

namespace Lynth.Interval

register_option lynth.interval.trust : String := {
  defValue := "auto"
  descr := "lynth interval certificates: kernel | native | auto"
}

register_option lynth.interval.kernelBudget : Nat := {
  defValue := 400000
  descr := "cost units allowed for kernel checking in `auto` mode"
}

register_option lynth.interval.maxPrec : Nat := {
  defValue := 4096
  descr := "maximal working precision (bits) tried by the interval procedure"
}

end Lynth.Interval

namespace Lynth.Interval.Goals

register_option lynth.interval.complexIntegralSteps : Nat := {
  defValue := 16384
  descr := "subdivision and recursive-integral search budget for a complex component"
}

end Lynth.Interval.Goals
