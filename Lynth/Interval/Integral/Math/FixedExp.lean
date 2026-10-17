import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Integer endpoint arithmetic for exp on [-1/2,1/2]. Mathlib-only proof
handoff; ordinary scaling and squaring reconstructs the full exponential. -/

namespace Intgrl

def fixedExpLoop (p : ℕ) (a : ℤ) :
    ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ × ℤ
  | 0, _, lo, hi, sl, sh =>
      let tail := (2 * max lo.natAbs hi.natAbs : ℕ)
      (sl-tail, sh+tail)
  | fuel+1, k, lo, hi, sl, sh =>
      let sl := sl+lo
      let sh := sh+hi
      let (l,h) := if 0 ≤ a then (lo*a,hi*a) else (hi*a,lo*a)
      let nextLo := (l >>> p) / (k+1 : ℤ)
      let nextHi := -(((-h) >>> p) / (k+1 : ℤ))
      if max nextLo.natAbs nextHi.natAbs ≤ 1 then (sl-2, sh+2)
      else fixedExpLoop p a fuel (k+1) nextLo nextHi sl sh

def fixedExpBounds (p : ℕ) (x : ℚ) : ℤ × ℤ :=
  let scale : ℤ := (2 : ℤ)^p
  if x = 0 then (scale,scale) else
    let a := (x * (scale : ℚ)).floor
    let (lo,hi) := fixedExpLoop p a (p+16) 0 scale scale 0 0
    (lo-2,hi+2)

/-- Rounded series invariant, geometric tail, and a two-unit bound for
rounding the reduced argument. -/
theorem fixedExpBounds_sound (p : ℕ) (hp : 0 < p) (x : ℚ)
    (hx : |(x : ℝ)| ≤ 1/2) :
    ((fixedExpBounds p x).1 : ℝ) * (2 : ℝ)^(-(p : ℤ)) ≤ Real.exp (x : ℝ) ∧
    Real.exp (x : ℝ) ≤ ((fixedExpBounds p x).2 : ℝ) * (2 : ℝ)^(-(p : ℤ)) := by
  sorry

end Intgrl
