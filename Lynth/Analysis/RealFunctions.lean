module

public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! Real special functions, with aliases outside the interval implementation namespace. -/

namespace Lynth.Interval.Fns

namespace Real'

/-- real zeta as a real-valued function (graph for the registry entry). -/
public noncomputable def zeta (s : ℝ) : ℝ := (riemannZeta (s : ℂ)).re

end Real'

namespace Real'

/-- real digamma as a real-valued function (graph for the registry entry). -/
public noncomputable def digamma (s : ℝ) : ℝ := (Complex.digamma (s : ℂ)).re

end Real'

end Lynth.Interval.Fns

namespace Real

export Lynth.Interval.Fns.Real' (digamma zeta)

end Real
