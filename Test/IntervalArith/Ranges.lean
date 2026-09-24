import Mathlib
import Lynth

/-!
T07-T11 + MR01-MR03: range tests -- the shape
  `def name : { p : Rat × Rat // |sup f - p.1| < tol ∧ |inf f - p.2| < tol } := by lynth`
where `sup`/`inf` are the supremum and infimum of `f` over a closed box
(`rangeSup`/`rangeInf` below, via `sSup`/`sInf`).  T07-T11 use elementary
functions; MR01-MR03 use *compositions* (`exp (sin r + cos r)`,
`arctan (sin r + cos r)`, `exp (cos r) * sin r`) whose extrema are interior
points, so plain interval evaluation is not enough.
Ground truth: `arb/CERTIFICATES.md` (subdivision + refinement of the
extremal boxes).
-/

namespace IntervalArith


/-- Supremum of `f` over the closed interval `[a, b]` (`sSup` of the image;
junk value for an empty set, which cannot occur for `a <= b`). -/
noncomputable def rangeSup (f : ℝ → ℝ) (a b : ℝ) : ℝ := sSup (f '' Set.Icc a b)

/-- Infimum of `f` over the closed interval `[a, b]`. -/
noncomputable def rangeInf (f : ℝ → ℝ) (a b : ℝ) : ℝ := sInf (f '' Set.Icc a b)


/-- **T07** — Range of `sin` on `[0, 1/10]`: `p.1 ~ sup`, `p.2 ~ inf` (the shape from the request,
with the `x.2` typo fixed).

enclosure `sup in [0.09983339286452264094151587, 0.09983341670638423703820763]; inf in
[-6.661342382915675514043485e-17, 2.384185797676958912586203e-08]`, witness
`(0.09983341664682815475018174, 0)`, worst error `sup 2.378230551135848409814101e-08, inf
2.384185797676958912586203e-08` < `0.001000000000000000020816682 /
0.001000000000000000020816682`.

96 boxes, argmax in 0.100000, argmin in 0.000000.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def range_sin_zero_one_tenth : { p : Rat × Rat // abs (rangeSup Real.sin 0 (1 / 10) - p.1) < 1 / 1000 ∧ abs (rangeInf Real.sin 0 (1 / 10) - p.2) < 1 / 1000 } := by lynth

/-- **T08** — Range of `cos` on `[0, 3/2]`: the supremum `1` is attained at the left endpoint, the
infimum at the right one.

enclosure `sup in [0.9999999999999946709294818, 1.000000000930998833581498]; inf in
[0.07073720166770290640467778, 0.0707372016677029480380412]`, witness `(1,
0.07073720166770290640467778)`, worst error `sup 9.309988353162212959546196e-10, inf
4.158941066936810378335285e-17` < `0.001000000000000000020816682 /
0.001000000000000000020816682`.

224 boxes, argmax in 0.000001, argmin in 1.500000.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def range_cos_zero_three_halves : { p : Rat × Rat // abs (rangeSup Real.cos 0 (3 / 2) - p.1) < 1 / 1000 ∧ abs (rangeInf Real.cos 0 (3 / 2) - p.2) < 1 / 1000 } := by lynth

/-- **T09** — Range of `exp` on `[-1, 1]`: `e` and `1/e`.

enclosure `sup in [2.718281828459045090795598, 2.718281828459045090795598]; inf in
[0.3678794411714423340242774, 0.3678794411714423340242774]`, witness
`(2.718281828459045090795598, 0.3678794411714423340242774)`, worst error `sup
1.508946672777013341832253e-16, inf 2.042693518565577336189155e-17` <
`0.001000000000000000020816682 / 0.001000000000000000020816682`.

224 boxes, argmax in 1.000000, argmin in -1.000000.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def range_exp_neg_one_one : { p : Rat × Rat // abs (rangeSup Real.exp (-1) 1 - p.1) < 1 / 1000 ∧ abs (rangeInf Real.exp (-1) 1 - p.2) < 1 / 1000 } := by lynth

/-- **T10** — Range of `tan` on `[0, 1]` (no pole): `tan 1` and `0`.

enclosure `sup in [1.557407724642336566134304, 1.557407724655005987202117]; inf in
[-1.355252715606880542509316e-20, 3.63797884097303084183217e-12]`, witness
`(1.557407724654902292371617, 0)`, worst error `sup 1.25657410933283735178346e-11, inf
3.63797884097303084183217e-12` < `0.001000000000000000020816682 /
0.001000000000000000020816682`.

128 boxes, argmax in 1.000000, argmin in 0.000000.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def range_tan_zero_one : { p : Rat × Rat // abs (rangeSup Real.tan 0 1 - p.1) < 1 / 1000 ∧ abs (rangeInf Real.tan 0 1 - p.2) < 1 / 1000 } := by lynth

/-- **T11** — Range of `exp (sin x) * cos (x^2)` on `[-1, 1]`: the maximum is an **interior**
extremum (`x ~ 0.704247`), the minimum sits at `x = -1`. Plain interval evaluation is not enough
— subdivision/refinement is required (the tolerances are correspondingly wider).

enclosure `sup in [1.680464546848401408141171, 1.684699663112938727849155]; inf in
[0.2329113301381139367052242, 0.2329113301381139644607998]`, witness
`(1.680464623973582760640966, 0.2329113301381139367052242)`, worst error `sup
0.004235039139355995831126567, inf 4.76342847399021399434423e-17` <
`0.01000000000000000020816682 / 0.001000000000000000020816682`.

224 boxes, argmax in 0.746094, argmin in -1.000000.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def range_exp_sin_cos_sq : { p : Rat × Rat // abs (rangeSup (fun r => Real.exp (Real.sin r) * Real.cos (r ^ 2)) (-1) 1 - p.1) < 1 / 100 ∧ abs (rangeInf (fun r => Real.exp (Real.sin r) * Real.cos (r ^ 2)) (-1) 1 - p.2) < 1 / 1000 } := by lynth

/-- **MR01** — `range_exp_sin_add_cos`: the range of `exp, sin, cos` on the closed box, as a `Rat ×
Rat` of `(sup, inf)`.

sup enclosure [4.11325037373946323, 4.11342338472604752], reference 4.11325037878 at r ~
0.784119, witness error 0.00017

inf enclosure [2.71828182845904509, 2.71828182845904509], reference 2.71828182846 at r ~
0.000000, witness error 9.5e-13

functions composed: exp, sin, cos

maximum at the interior point r = pi/4, minimum at the left endpoint.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def range_exp_sin_add_cos : { p : Rat × Rat // abs (rangeSup (fun r => Real.exp (Real.sin r + Real.cos r)) (0 : ℝ) (1 : ℝ) - p.1) < 1 / 1000 ∧
        abs (rangeInf (fun r => Real.exp (Real.sin r + Real.cos r)) (0 : ℝ) (1 : ℝ) - p.2) < 1 / 1000 } := by lynth

/-- **MR02** — `range_arctan_sin_add_cos`: the range of `arctan, sin, cos` on the closed box, as a
`Rat × Rat` of `(sup, inf)`.

sup enclosure [0.955316617677493429, 0.955343916080892086], reference 0.955316618125 at r ~
0.782837, witness error 2.7e-05

inf enclosure [0.458153082660882782, 0.458153082660882782], reference 0.458153082661 at r ~
2.000000, witness error 1.2e-13

functions composed: arctan, sin, cos

arctan is monotone, so the extrema come from sin + cos.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def range_arctan_sin_add_cos : { p : Rat × Rat // abs (rangeSup (fun r => Real.arctan (Real.sin r + Real.cos r)) (0 : ℝ) (2 : ℝ) - p.1) < Real.pi / 1000 ∧
        abs (rangeInf (fun r => Real.arctan (Real.sin r + Real.cos r)) (0 : ℝ) (2 : ℝ) - p.2) < Real.pi / 1000 } := by lynth

/-- **MR03** — `range_exp_cos_mul_sin`: the range of `exp, cos, sin` on the closed box, as a `Rat ×
Rat` of `(sup, inf)`.

sup enclosure [1.45852853672508598, 1.45865838162187922], reference 1.45852853714 at r ~
0.901978, witness error 0.00013

inf enclosure [-1.47474369329154012e-36, 2.74476323246779491e-28], reference 0 at r ~ 0.000000,
witness error 2.7e-28

functions composed: exp, cos, sin

interior maximum at r = pi/4, minimum 0 at the left endpoint.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def range_exp_cos_mul_sin : { p : Rat × Rat // abs (rangeSup (fun r => Real.exp (Real.cos r) * Real.sin r) (0 : ℝ) (2 : ℝ) - p.1) < 1 / 1000 ∧
        abs (rangeInf (fun r => Real.exp (Real.cos r) * Real.sin r) (0 : ℝ) (2 : ℝ) - p.2) < 1 / 1000 } := by lynth

end IntervalArith

-- The repository convention (`Test/*.lean`, `Test/Grind/README.md`) pins the
-- axiom footprint of every declaration once the goals go through.  Uncomment
-- (and keep the `info` docstring in sync) when a goal starts closing:
--
-- /-- info: 'range_exp_cos_mul_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- #guard_msgs in
-- #print axioms range_exp_cos_mul_sin
