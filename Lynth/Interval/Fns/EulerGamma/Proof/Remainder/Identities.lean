import Lynth.Interval.Fns.EulerGamma.Proof.Remainder.Substitution

/-!
# The exponentially small difference `PP n - Σ_{j<n} pp n j`: pointwise identities
-/

open Real MeasureTheory Set Filter Topology Finset

namespace BM

noncomputable def Em (n : ℕ) (y : ℝ) : ℝ := exp (-((n : ℝ) * (exp (-y) - 1 + y)))
noncomputable def Ep (n : ℕ) (y : ℝ) : ℝ := exp (-((n : ℝ) * (exp y - 1 - y)))
noncomputable def VV (n : ℕ) (y : ℝ) : ℝ := ∑ i ∈ range n, cc (n + i) * exp (-((i + 1 / 2) * y))
noncomputable def WW (n : ℕ) (y : ℝ) : ℝ :=
  ∑ i ∈ range n, cc (n - 1 - i) * exp (-((i + 1 / 2) * y))
/-- the tail `(1-e^{-y})^{-1/2} - Σ_{j<2n} c_j e^{-jy}`, rescaled -/
noncomputable def TL (n : ℕ) (y : ℝ) : ℝ :=
  exp (((n : ℝ) - 1 / 2) * y) *
    ((1 - exp (-y)) ^ (-(1 / 2 : ℝ)) - ∑ j ∈ range (2 * n), cc j * exp (-y) ^ j)

lemma exp_pow_eq (y : ℝ) (j : ℕ) : exp (-y) ^ j = exp (-(j * y)) := by
  rw [← Real.exp_nat_mul]; ring_nf

lemma lower_identity (n : ℕ) (y : ℝ) :
    exp (-(n * exp (-y))) * exp (-(1 / 2 * y)) * (1 - exp (-y)) ^ (-(1 / 2 : ℝ))
      = ∑ j ∈ range n, cc j * (exp (-(n * exp (-y))) * exp (-((j + 1 / 2) * y)))
        + exp (-(n : ℝ)) * (Em n y * (VV n y + TL n y)) := by
  set X := exp (-(n * exp (-y)))
  set T := (1 - exp (-y)) ^ (-(1 / 2 : ℝ)) - ∑ j ∈ range (2 * n), cc j * exp (-y) ^ j
  have hsplit : (1 - exp (-y)) ^ (-(1 / 2 : ℝ)) = ∑ j ∈ range n, cc j * exp (-y) ^ j
      + ∑ i ∈ range n, cc (n + i) * exp (-y) ^ (n + i) + T := by
    simp only [T]; rw [two_mul, Finset.sum_range_add]; ring
  have e1 : ∀ j : ℕ, X * exp (-(1 / 2 * y)) * (cc j * exp (-y) ^ j)
      = cc j * (X * exp (-((j + 1 / 2) * y))) := by
    intro j
    rw [exp_pow_eq, show X * exp (-(1 / 2 * y)) * (cc j * exp (-(j * y)))
      = cc j * (X * (exp (-(1 / 2 * y)) * exp (-(j * y)))) by ring, ← Real.exp_add]
    congr 3; ring
  have e2 : ∀ i : ℕ, X * exp (-(1 / 2 * y)) * (cc (n + i) * exp (-y) ^ (n + i))
      = exp (-(n : ℝ)) * (Em n y * (cc (n + i) * exp (-((i + 1 / 2) * y)))) := by
    intro i
    rw [exp_pow_eq, Em]
    simp only [X]
    rw [show exp (-(n * exp (-y))) * exp (-(1 / 2 * y)) * (cc (n + i) * exp (-(((n + i : ℕ) : ℝ) * y)))
      = cc (n + i) * (exp (-(n * exp (-y))) * exp (-(1 / 2 * y)) * exp (-(((n + i : ℕ) : ℝ) * y)))
      by ring,
      show exp (-(n : ℝ)) * (exp (-((n : ℝ) * (exp (-y) - 1 + y))) * (cc (n + i) * exp (-((i + 1 / 2) * y))))
      = cc (n + i) * (exp (-(n : ℝ)) * exp (-((n : ℝ) * (exp (-y) - 1 + y))) * exp (-((i + 1 / 2) * y)))
      by ring]
    simp only [← Real.exp_add]
    congr 2; push_cast; ring
  have e3 : X * exp (-(1 / 2 * y)) * T = exp (-(n : ℝ)) * (Em n y * (exp (((n : ℝ) - 1 / 2) * y) * T)) := by
    rw [Em]
    simp only [X]
    rw [show exp (-(n : ℝ)) * (exp (-((n : ℝ) * (exp (-y) - 1 + y))) * (exp (((n : ℝ) - 1 / 2) * y) * T))
      = (exp (-(n : ℝ)) * exp (-((n : ℝ) * (exp (-y) - 1 + y))) * exp (((n : ℝ) - 1 / 2) * y)) * T
      by ring]
    simp only [← Real.exp_add]
    congr 2; ring
  rw [hsplit, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, e3, VV, TL]
  rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_congr rfl (fun i _ => e2 i),
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

lemma upper_identity (n : ℕ) (y : ℝ) :
    ∑ j ∈ range n, cc j * (exp (-(n * exp y)) * exp ((j + 1 / 2) * y))
      = exp (-(n : ℝ)) * (Ep n y * WW n y) := by
  rw [WW, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < n := Finset.mem_range.mp hi
  rw [Ep, show exp (-(n : ℝ)) * (exp (-((n : ℝ) * (exp y - 1 - y))) * (cc (n - 1 - i) * exp (-((i + 1 / 2) * y))))
      = cc (n - 1 - i) * (exp (-(n : ℝ)) * exp (-((n : ℝ) * (exp y - 1 - y))) * exp (-((i + 1 / 2) * y)))
      by ring]
  simp only [← Real.exp_add]
  congr 2
  have : ((n - 1 - i : ℕ) : ℝ) = n - 1 - i := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  rw [this]; ring

end BM
