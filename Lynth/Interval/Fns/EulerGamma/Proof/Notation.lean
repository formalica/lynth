import Lynth.Interval.Fns.EulerGamma.SeriesBounds

/-!
# Basic objects for the proof of the Brent–McMillan error bound

We use the following notation (with `x = m`, `n = 4m`):
* `I(x) = bmB (x^2) = Σ x^{2k}/(k!)²` (Bessel `I₀(2x)`),
* `S(x) = bmA (x^2) = Σ H_k x^{2k}/(k!)²`,
* `K0 x = ∫_0^∞ exp(-2x cosh v) dv` (Bessel `K₀(2x)`),
* `cc j = C(2j,j)/4^j`, the Taylor coefficients of `(1-u)^{-1/2}`,
* `pp n j = cc j * Γ(j+1/2) / n^j`,
* `PP n = ∫_0^n e^{-t} t^{-1/2} (1-t/n)^{-1/2} dt` (so `I(x) = e^{2x} PP(4x)/(2π√x)`),
* `QQ n = ∫_0^∞ e^{-s} s^{-1/2} (1+s/n)^{-1/2} ds` (so `K0 x = e^{-2x} QQ(4x)/(2√x)`).
-/

open Real MeasureTheory Set

namespace BM

/-- `c_j = binom(2j, j) / 4^j`. -/
noncomputable def cc (j : ℕ) : ℝ := ((2 * j).choose j : ℝ) / 4 ^ j

/-- `p_j = c_j Γ(j + 1/2) / n^j`, the terms of the asymptotic expansion of `PP n`. -/
noncomputable def pp (n : ℕ) (j : ℕ) : ℝ := cc j * Real.Gamma (j + 1 / 2) / (n : ℝ) ^ j

/-- `PP n = ∫_0^n e^{-t} t^{-1/2} (1 - t/n)^{-1/2} dt`. -/
noncomputable def PP (n : ℕ) : ℝ :=
  ∫ t in Ioo 0 (n : ℝ), exp (-t) * t ^ (-(1 / 2 : ℝ)) * (1 - t / n) ^ (-(1 / 2 : ℝ))

/-- `QQ n = ∫_0^∞ e^{-s} s^{-1/2} (1 + s/n)^{-1/2} ds`. -/
noncomputable def QQ (n : ℕ) : ℝ :=
  ∫ s in Ioi 0, exp (-s) * s ^ (-(1 / 2 : ℝ)) * (1 + s / n) ^ (-(1 / 2 : ℝ))

/-- The Bessel function `K0 x = ∫_0^∞ exp(-2x cosh v) dv` (classically `K₀(2x)`). -/
noncomputable def K0 (x : ℝ) : ℝ := ∫ v in Ioi 0, exp (-(2 * x * cosh v))

end BM
