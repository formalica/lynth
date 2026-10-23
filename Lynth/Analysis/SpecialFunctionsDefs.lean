module

public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib
import Mathlib.Analysis.Complex.Basic

/-! Real and complex special functions provided by Lynth. -/

namespace SpecialFunctions

public inductive SeriesKind where
  | erf | si | airy0 | airy1
deriving @[expose] BEq, @[expose] DecidableEq, Repr, Inhabited

@[expose] public def SeriesKind.num : SeriesKind → ℕ → ℕ
  | .erf, k | .si, k => 2*k+1
  | .airy0, _ | .airy1, _ => 1

@[expose] public def SeriesKind.den : SeriesKind → ℕ → ℕ
  | .erf, k => (k+1)*(2*k+3)
  | .si, k => (2*k+2)*(2*k+3)^2
  | .airy0, k => (3*k+3)*(3*k+2)
  | .airy1, k => (3*k+3)*(3*k+4)

def coefficient (kind : SeriesKind) : ℕ → ℚ
  | 0 => 1
  | k+1 => coefficient kind k * kind.num k / kind.den k

noncomputable def seriesR (kind : SeriesKind) (x : ℝ) : ℝ :=
  ∑' k, (coefficient kind k : ℝ) * x^k

noncomputable def seriesC (kind : SeriesKind) (z : ℂ) : ℂ :=
  ∑' k, (coefficient kind k : ℂ) * z^k

noncomputable def airyA : ℝ := 1 / ((3 : ℝ)^(2/3 : ℝ) * Real.Gamma (2/3))
noncomputable def airyB : ℝ := -1 / ((3 : ℝ)^(1/3 : ℝ) * Real.Gamma (1/3))

end SpecialFunctions

namespace Real

public noncomputable def erf (x : ℝ) : ℝ :=
  2 / Real.sqrt Real.pi * x * SpecialFunctions.seriesR .erf (-x^2)

/-- Sine integral, with its removable singularity at zero filled in. -/
public noncomputable def Si (x : ℝ) : ℝ := x * SpecialFunctions.seriesR .si (-x^2)

/-- Entire continuation of the alternating zeta function; eta(1) = log 2. -/
public noncomputable def dirichletEta (s : ℝ) : ℝ :=
  if s = 1 then Real.log 2 else (1 - (2 : ℝ)^(1-s)) * (riemannZeta (s : ℂ)).re

public noncomputable def airyAi (x : ℝ) : ℝ :=
  SpecialFunctions.airyA * SpecialFunctions.seriesR .airy0 (x^3) +
    SpecialFunctions.airyB * x * SpecialFunctions.seriesR .airy1 (x^3)

end Real

namespace Complex

public noncomputable def erf (z : ℂ) : ℂ :=
  (2 / Real.sqrt Real.pi : ℝ) * z * SpecialFunctions.seriesC .erf (-z^2)

public noncomputable def Si (z : ℂ) : ℂ := z * SpecialFunctions.seriesC .si (-z^2)

public noncomputable def dirichletEta (s : ℂ) : ℂ :=
  if s = 1 then (Real.log 2 : ℂ) else (1 - (2 : ℂ)^(1-s)) * riemannZeta s

public noncomputable def airyAi (z : ℂ) : ℂ :=
  (SpecialFunctions.airyA : ℂ) * SpecialFunctions.seriesC .airy0 (z^3) +
    (SpecialFunctions.airyB : ℂ) * z * SpecialFunctions.seriesC .airy1 (z^3)

end Complex

