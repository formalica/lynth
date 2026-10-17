import Lynth.Interval.Integral.Math.LegendreEval

/-! Integer-only Bonnet recurrence with delayed scalar divisions (FLINT).
This definition and its error contract are mirrored in /tmp/intgrl/FixedPoint.lean.
-/

namespace Intgrl

/-- State after the first k recurrence updates, storing a common denominator. -/
def fixedState (p : ℕ) (x : ℤ) : ℕ → ℤ × ℤ × ℤ
  | 0 => ((2 : ℤ) ^ p, x, 1)
  | k + 1 =>
    let (a, b, den) := fixedState p x k
    let j : ℤ := k + 1
    let t := (b * x).tdiv ((2 : ℤ) ^ p)
    let v := (2 * j + 1) * t - j * j * a
    if den * (j + 1) ≥ (2 : ℤ) ^ 62 then
      (b.tdiv den, v.tdiv den, j + 1)
    else (b, v, den * (j + 1))

/-- Simultaneous P_(n-1),P_n, in units of 2^(-p). -/
def fixedPair (p : ℕ) (x : ℤ) (n : ℕ) : ℤ × ℤ :=
  if n = 0 then (0, (2 : ℤ) ^ p) else
    let (a, b, den) := fixedState p x (n - 1)
    (a.tdiv (den.tdiv (n : ℤ)), b.tdiv den)

theorem fixedPair_correct (p n : ℕ) (x : ℤ)
    (hx : |(x : ℝ) / (2 : ℝ) ^ p| ≤ 1) :
    |((fixedPair p x n).2 : ℝ) / (2 : ℝ) ^ p -
      (legendre n).eval ((x : ℝ) / (2 : ℝ) ^ p)| ≤
        (((n : ℝ) + 1) * ((n : ℝ) + 2)) / (2 : ℝ) ^ p ∧
    (0 < n →
      |((fixedPair p x n).1 : ℝ) / (2 : ℝ) ^ p -
        (legendre (n - 1)).eval ((x : ℝ) / (2 : ℝ) ^ p)| ≤
          (((n : ℝ) + 1) * ((n : ℝ) + 2)) / (2 : ℝ) ^ p) := by
  sorry

end Intgrl
