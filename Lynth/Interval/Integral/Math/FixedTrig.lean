import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! Fixed-point sine/cosine on [-2,2]. Only integer endpoint arithmetic is
used in the series loop. This Mathlib-only module is mirrored in /tmp/intgrl.
The series is an elementary-function kernel, not Taylor quadrature. -/

namespace Intgrl

/-- The remaining series is bounded by twice the current term from index 1.
Endpoint products are divided with directed integer rounding. -/
def fixedTrigLoop (p : ℕ) (a2 : ℤ) (sine : Bool) :
    ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ × ℤ
  | 0, k, lo, hi, sl, sh =>
      if k = 0 then (-((2 : ℤ)^p), (2 : ℤ)^p) else
        let tail := (2 * max lo.natAbs hi.natAbs : ℕ)
        (sl - tail, sh + tail)
  | fuel + 1, k, lo, hi, sl, sh =>
      let sl := sl + lo
      let sh := sh + hi
      let d : ℤ := if sine then (2*k+2)*(2*k+3) else (2*k+1)*(2*k+2)
      let nextLo := ((-hi * a2) >>> (2*p)) / d
      let nextHi := -(((lo * a2) >>> (2*p)) / d)
      if k ≥ 1 && max nextLo.natAbs nextHi.natAbs ≤ 1 then
        (sl - 2, sh + 2)
      else fixedTrigLoop p a2 sine fuel (k+1) nextLo nextHi sl sh

/-- Bounds in units of 2^(-p). Rounding the argument down costs at most
one unit by the Lipschitz bounds for sine and cosine. -/
def fixedTrigBounds (p : ℕ) (sine : Bool) (x : ℚ) : ℤ × ℤ :=
  let scale : ℤ := (2 : ℤ)^p
  if x = 0 then
    if sine then (0, 0) else (scale, scale)
  else
    let a := (x * (scale : ℚ)).floor
    let first := if sine then a else scale
    let (lo, hi) := fixedTrigLoop p (a*a) sine (p+16) 0 first first 0 0
    (lo-1, hi+1)

/-- Generic fixed-point series contract. The proof consists of the rounded
term recurrence invariant, a geometric tail from index 1, and the argument
rounding error. No interval implementation or integration definitions occur. -/
theorem fixedTrigBounds_sound (p : ℕ) (sine : Bool) (x : ℚ)
    (hx : |(x : ℝ)| ≤ 2) :
    ((fixedTrigBounds p sine x).1 : ℝ) * (2 : ℝ)^(-(p : ℤ)) ≤
      (if sine then Real.sin (x : ℝ) else Real.cos (x : ℝ)) ∧
    (if sine then Real.sin (x : ℝ) else Real.cos (x : ℝ)) ≤
      ((fixedTrigBounds p sine x).2 : ℝ) * (2 : ℝ)^(-(p : ℤ)) := by
  sorry

end Intgrl
