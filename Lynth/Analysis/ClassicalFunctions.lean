module

public import Mathlib.Basic.Complex.Basic
import Mathlib
import Mathlib.Analysis.Complex.Basic

/-! Classical complex functions provided by Lynth. -/

open scoped Nat
open MeasureTheory

namespace Complex

/-- The modified Bessel function of the first kind, defined by its classical series. -/
public noncomputable def besselI (ν w : ℂ) : ℂ :=
  (w / 2) ^ ν * ∑' k : ℕ, (w ^ 2 / 4) ^ k / ((k ! : ℂ) * Gamma (ν + k + 1))

/-- The complete elliptic integral of the first kind, in the parameter convention `m = k²`. -/
public noncomputable def ellipticK (m : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), (1 - m * (Real.sin t : ℂ) ^ 2) ^ (-(1 / 2) : ℂ)

/-- The complete elliptic integral of the second kind, in the parameter convention `m = k²`. -/
public noncomputable def ellipticE (m : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), (1 - m * (Real.sin t : ℂ) ^ 2) ^ ((1 / 2) : ℂ)

end Complex
