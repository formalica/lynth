import Mathlib
import Lynth

/-!
T18-T20 + B06: special functions (`Gamma`, `zeta`, `pi`) and a
certified algebraic root.  Ground truth: `arb/CERTIFICATES.md`; the Arb
surface behind these is `arb.gamma`, `arb.zeta`, `arb.const_pi` and
interval Newton (`arb/tools.py: interval_newton`).
-/

namespace IntervalArith


/-- **T18** — `Gamma (1/4)` — Arb's rigorous Gamma (reflection/AGM based).

enclosure `3.625609908221908206371609; 3.625609908221908206371609`, witness
`3.62560990822190831193`, worst error `6.851558676720030328965983e-22` <
`1.000000000000000081803054e-05`.

arb.gamma at 1/4 (reflection/AGM-based, rigorous).

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def gamma_quarter : { x : Rat // abs (Real.Gamma (1 / 4) - x) < (10 : ℝ) ^ (-5 : ℤ) } := by lynth

/-- **T19** — `(riemannZeta 3).re` — Apéry's constant; `riemannZeta` is `ℂ → ℂ`, so the goal reads
off the real part.

enclosure `1.202056903159594236640828; 1.202056903159594236640828`, witness
`1.20205690315959428539`, worst error `9.738161511449990531354987e-21` <
`1.000000000000000081803054e-05`.

arb.zeta(3) (Apéry's constant).

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def zeta_three : { x : Rat // abs ((riemannZeta 3).re - x) < (10 : ℝ) ^ (-5 : ℤ) } := by lynth

/-- **T20** — `pi` to within `1/1000`: the classical rational witness is `355/113` (continued
fractions / interval bisection).

enclosure `3.141592653589793115997963; 3.141592653589793115997963`, witness `355 / 113`, worst
error `2.66764189062422294610122e-07` < `0.001000000000000000020816682`.

classic continued-fraction convergent 355/113; |355/113 - pi| = 2.667642e-07.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def pi_rational : { x : Rat // abs (Real.pi - x) < 1 / 1000 } := by lynth

/-- **B06** — **Bonus.** A certified root: `|x^3 - 2| < 1e-7` (interval Newton on `[5/4, 13/10]`,
existence certified by bisection).

enclosure `1.259921049894873190666544; 1.259921049894873190666544`, witness
`1.25992104989487316476`, worst error `3.43383767363677162471094e-20` <
`9.999999999999999547481118e-08`.

interval Newton on [5/4, 13/10]: converged, box empty, existence certified = True; residual |x^3
- 2| of the 20-digit witness 3.43383767363677162471094e-20.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def root_cube_two : { x : Rat // abs ((x : ℝ) ^ 3 - 2) < (10 : ℝ) ^ (-7 : ℤ) } := by lynth

end IntervalArith

-- The repository convention (`Test/*.lean`, `Test/Grind/README.md`) pins the
-- axiom footprint of every declaration once the goals go through.  Uncomment
-- (and keep the `info` docstring in sync) when a goal starts closing:
--
-- /-- info: 'root_cube_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- #guard_msgs in
-- #print axioms root_cube_two
