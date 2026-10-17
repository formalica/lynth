import Lynth.Interval.Integral.Math.IntgrlDefs

/-!
P0: roots, weights and exactness. Send with IntgrlDefs.lean.
Every sorry is an unproved obligation, not a claimed completed proof.
Mathlib's Polynomial.shiftedLegendre can be used to prove these results;
its convention must be transformed to the normalization in IntgrlDefs.
-/

noncomputable section

open scoped BigOperators

namespace Intgrl

theorem legendre_natDegree (n : ℕ) :
    (legendre n).natDegree = n := by
  sorry

theorem legendre_orthogonal (n : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree < n) :
    (∫ t in (-1 : ℝ)..1, (legendre n).eval t * p.eval t) = 0 := by
  sorry

theorem legendre_roots (n : ℕ) :
    ∃ x : Fin n → ℝ, IsGaussNodes x ∧
      ∀ i, (legendre n).derivative.eval (x i) ≠ 0 := by
  sorry

theorem gaussWeight_pos {n : ℕ} {x : Fin n → ℝ}
    (hx : IsGaussNodes x) (i : Fin n) :
    0 < gaussWeight n (x i) := by
  sorry

theorem gauss_exact {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ}
    (hx : IsGaussNodes x) (p : Polynomial ℝ)
    (hp : p.natDegree < 2 * n) :
    (∫ t in (-1 : ℝ)..1, p.eval t) = gaussSum x p.eval := by
  sorry

theorem gaussWeight_sum {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ}
    (hx : IsGaussNodes x) :
    (∑ i, gaussWeight n (x i)) = 2 := by
  sorry

end Intgrl
