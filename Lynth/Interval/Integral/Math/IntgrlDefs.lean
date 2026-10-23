module

import Mathlib

/-!
Portable mathematical vocabulary for certified Gauss-Legendre integration.
This file has no Lynth dependencies and contains no proof placeholders.
The recurrence is a mathematical specification, not the runtime evaluator.
-/

noncomputable section

open scoped BigOperators

namespace Intgrl

/-- Legendre polynomials, normalized by P_n(1) = 1. -/
def legendre : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X
  | n + 2 =>
      Polynomial.C ((2 * (n : ℝ) + 3) / ((n : ℝ) + 2)) *
        Polynomial.X * legendre (n + 1) -
      Polynomial.C (((n : ℝ) + 1) / ((n : ℝ) + 2)) * legendre n

/-- No particular ordering of the n distinct roots is required. -/
def IsGaussNodes {n : ℕ} (x : Fin n → ℝ) : Prop :=
  Function.Injective x ∧
    ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1 ∧ (legendre n).eval (x i) = 0

def gaussWeight (n : ℕ) (x : ℝ) : ℝ :=
  2 / ((1 - x ^ 2) * ((legendre n).derivative.eval x) ^ 2)

def gaussSum {n : ℕ} (x : Fin n → ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i, gaussWeight n (x i) * f (x i)

def gaussSumC {n : ℕ} (x : Fin n → ℝ) (f : ℂ → ℂ) : ℂ :=
  ∑ i, (gaussWeight n (x i) : ℂ) * f (x i)

def ellipseX (ρ : ℝ) : ℝ := (ρ + ρ⁻¹) / 2

def ellipseY (ρ : ℝ) : ℝ := (ρ - ρ⁻¹) / 2

/-- Closed filled Bernstein ellipse. All uses require 1 < rho. -/
def ellipse (ρ : ℝ) : Set ℂ :=
  {z | (z.re / ellipseX ρ) ^ 2 + (z.im / ellipseY ρ) ^ 2 ≤ 1}

def affine (a b : ℝ) (z : ℂ) : ℂ :=
  (((a + b) / 2 : ℝ) : ℂ) + (((b - a) / 2 : ℝ) : ℂ) * z

/-- The deliberately slightly relaxed bound used by FLINT. -/
def glError (n : ℕ) (ρ M : ℝ) : ℝ :=
  64 * M / (15 * (ρ - 1) * ρ ^ (2 * n - 1))

end Intgrl
