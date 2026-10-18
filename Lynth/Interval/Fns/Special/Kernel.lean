import Lynth.Analysis.SpecialFunctions

/-! Small portable fixed-point kernels. Real series use two integer endpoints;
complex series use four, in a distinct loop. No CBox, Ival or tactic dependencies.
Mirrored in /tmp/intgrl/SpecialKernel.lean (with its sole local import renamed).
-/

namespace SpecialFunctions

abbrev Fixed := ℤ × ℤ
abbrev FixedC := Fixed × Fixed

def fixedAdd (a b : Fixed) : Fixed := (a.1+b.1, a.2+b.2)
def fixedNeg (a : Fixed) : Fixed := (-a.2,-a.1)
def fixedMul (p : ℕ) (a b : Fixed) : Fixed :=
  let aa := a.1*b.1
  let ab := a.1*b.2
  let ba := a.2*b.1
  let bb := a.2*b.2
  (min (min aa ab) (min ba bb) >>> p,
    -((-max (max aa ab) (max ba bb)) >>> p))
def fixedScale (a : Fixed) (n d : ℕ) : Fixed :=
  (a.1 * (n : ℤ) / (d : ℤ), -((-a.2 * (n : ℤ)) / (d : ℤ)))
def fixedAbs (a : Fixed) : ℕ := max a.1.natAbs a.2.natAbs

def fixedCAdd (a b : FixedC) : FixedC := (fixedAdd a.1 b.1, fixedAdd a.2 b.2)
def fixedCMul (p : ℕ) (a b : FixedC) : FixedC :=
  (fixedAdd (fixedMul p a.1 b.1) (fixedNeg (fixedMul p a.2 b.2)),
    fixedAdd (fixedMul p a.1 b.2) (fixedMul p a.2 b.1))
def fixedCScale (a : FixedC) (n d : ℕ) : FixedC :=
  (fixedScale a.1 n d, fixedScale a.2 n d)
def fixedCAbs (a : FixedC) : ℕ := fixedAbs a.1 + fixedAbs a.2

def fixedInput (p : ℕ) (q : ℚ) : Fixed :=
  let q := q * ((2 : ℕ)^p : ℚ)
  (q.floor, q.ceil)

def realSeriesLoop (kind : SeriesKind) (p : ℕ) (x : Fixed) :
    ℕ → ℕ → Fixed → Fixed → Option Fixed
  | 0, _, _, _ => none
  | fuel+1, k, term, sum =>
    let sum := fixedAdd sum term
    let next := fixedScale (fixedMul p term x) (kind.num k) (kind.den k)
    if 2 * fixedAbs x * kind.num (k+1) ≤ 2^p * kind.den (k+1) &&
        fixedAbs next ≤ 4 then
      let err : ℤ := 2 * fixedAbs next
      some (sum.1-err, sum.2+err)
    else realSeriesLoop kind p x fuel (k+1) next sum

def complexSeriesLoop (kind : SeriesKind) (p : ℕ) (z : FixedC) :
    ℕ → ℕ → FixedC → FixedC → Option FixedC
  | 0, _, _, _ => none
  | fuel+1, k, term, sum =>
    let sum := fixedCAdd sum term
    let next := fixedCScale (fixedCMul p term z) (kind.num k) (kind.den k)
    if 2 * fixedCAbs z * kind.num (k+1) ≤ 2^p * kind.den (k+1) &&
        fixedCAbs next ≤ 8 then
      let err : ℤ := 2 * fixedCAbs next
      some ((sum.1.1-err, sum.1.2+err), (sum.2.1-err, sum.2.2+err))
    else complexSeriesLoop kind p z fuel (k+1) next sum

def realSeriesBounds (kind : SeriesKind) (p : ℕ) (x : ℚ) : Option Fixed :=
  realSeriesLoop kind p (fixedInput p x) (4*p+128) 0 (2^p,2^p) (0,0)

def complexSeriesBounds (kind : SeriesKind) (p : ℕ) (re im : ℚ) : Option FixedC :=
  complexSeriesLoop kind p (fixedInput p re, fixedInput p im) (4*p+128) 0
    ((2^p,2^p),(0,0)) ((0,0),(0,0))

theorem realSeriesBounds_sound (kind : SeriesKind) (p : ℕ) (x : ℚ) (b : Fixed)
    (h : realSeriesBounds kind p x = some b) :
    (b.1 : ℝ) * (2 : ℝ)^(-(p : ℤ)) ≤ seriesR kind x ∧
    seriesR kind x ≤ (b.2 : ℝ) * (2 : ℝ)^(-(p : ℤ)) := by
  sorry

theorem complexSeriesBounds_sound (kind : SeriesKind) (p : ℕ) (re im : ℚ) (b : FixedC)
    (h : complexSeriesBounds kind p re im = some b) :
    (b.1.1 : ℝ) * (2 : ℝ)^(-(p : ℤ)) ≤ (seriesC kind ((re : ℂ)+(im : ℂ)*Complex.I)).re ∧
    (seriesC kind ((re : ℂ)+(im : ℂ)*Complex.I)).re ≤ (b.1.2 : ℝ) * (2 : ℝ)^(-(p : ℤ)) ∧
    (b.2.1 : ℝ) * (2 : ℝ)^(-(p : ℤ)) ≤ (seriesC kind ((re : ℂ)+(im : ℂ)*Complex.I)).im ∧
    (seriesC kind ((re : ℂ)+(im : ℂ)*Complex.I)).im ≤ (b.2.2 : ℝ) * (2 : ℝ)^(-(p : ℤ)) := by
  sorry

/-- Coarse derivative bounds on convex rectangles for transporting complex midpoints.
The l1 radius r bounds |Re z|+|Im z| on the full rectangle. -/
theorem complex_lipschitz (z w : ℂ) (r : ℝ) (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖Complex.erf z - Complex.erf w‖ ≤ 2*Real.exp (r^2)*‖z-w‖ ∧
    ‖Complex.Si z - Complex.Si w‖ ≤ Real.exp r*‖z-w‖ ∧
    ‖Complex.airyAi z - Complex.airyAi w‖ ≤
      (2+r)^2*Real.exp (r^2+1)*‖z-w‖ := by
  sorry

theorem complex_lipschitz_pair (z w : ℂ) :
    ‖Complex.erf z - Complex.erf w‖ ≤ 2*Real.exp ((‖z‖+‖w‖)^2)*‖z-w‖ ∧
    ‖Complex.Si z - Complex.Si w‖ ≤ Real.exp (‖z‖+‖w‖)*‖z-w‖ ∧
    ‖Complex.airyAi z - Complex.airyAi w‖ ≤
      (2+‖z‖+‖w‖)^2*Real.exp ((‖z‖+‖w‖)^2+1)*‖z-w‖ := by
  simpa [add_assoc] using complex_lipschitz z w (‖z‖+‖w‖)
    (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

end SpecialFunctions
