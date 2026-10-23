module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Multiset.Defs
import Mathlib
import Mathlib.Analysis.Complex.Basic

/-! The generalized complex hypergeometric function provided by Lynth. -/

open scoped Nat

namespace Complex

variable {a b : Multiset ℂ} {z : ℂ} {n : ℕ}

/-- The coefficients of the (non-regularized) generalized hypergeometric series; they are the
coefficients of the regularized series multiplied by `∏ⱼ Γ(bⱼ)`. -/
noncomputable def HGFunCoeff (a b : Multiset ℂ) (n : ℕ) : ℂ :=
  (b.map Gamma).prod * regularizedHGFunCoeff a b n

/-- Lexicographic order on `ℂ` used to canonically order the top pair in `IsPfaffRegime`. -/
def cplxLe (u v : ℂ) : Prop :=
  u.re < v.re ∨ (u.re = v.re ∧ u.im ≤ v.im)

theorem cplxLe_refl (u : ℂ) : cplxLe u u :=
  Or.inr ⟨rfl, le_rfl⟩

theorem cplxLe_antisymm {u v : ℂ} (h1 : cplxLe u v) (h2 : cplxLe v u) : u = v := by
  rcases h1 with h1 | ⟨h1r, h1i⟩ <;> rcases h2 with h2 | ⟨h2r, h2i⟩
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · exact Complex.ext h1r (le_antisymm h1i h2i)

/-- Regime in which the `₂F₁` series is analytically continued left of `Re z = -1`
via the Pfaff transformation `₂F₁(a₀, a₁; c; z) = (1 - z)^{-a₀} ₂F₁(a₀, c - a₁; c; z / (z - 1))`. -/
def IsPfaffRegime (a b : Multiset ℂ) (z : ℂ) : Prop :=
  z.re < -1 ∧ (∀ x ∈ a, 0 < x.re) ∧
    (∃ p : ℂ × ℂ, a = {p.1, p.2} ∧ cplxLe p.1 p.2) ∧ (∃ c : ℂ, b = {c})

/-- Raw power-series definition `(∏ⱼ Γ(bⱼ)) · pF̃q(a; b; z)`. -/
noncomputable def HGFunBase (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  (b.map Gamma).prod * regularizedHGFun a b z

open Classical in
/-- The (non-regularized) generalized hypergeometric function `pFq`, defined through the
regularized one by `pFq(a; b; z) = (∏ⱼ Γ(bⱼ)) · pF̃q(a; b; z)` and extended to `IsPfaffRegime`
by Pfaff's transformation. -/
public noncomputable def HGFun (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  if h : IsPfaffRegime a b z then
    let p := Classical.choose h.2.2.1
    let c := Classical.choose h.2.2.2
    (1 - z) ^ (-p.1) * HGFunBase {p.1, c - p.2} {c} (z / (z - 1))
  else
    HGFunBase a b z

end Complex
