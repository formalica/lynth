import Mathlib
import Lynth

/-!
T18-T20 + B06: special functions (`Gamma`, `zeta`, `pi`) and a
certified algebraic root.  Ground truth: `arb/CERTIFICATES.md`; the Arb
surface behind these is `arb.gamma`, `arb.zeta`, `arb.const_pi` and
interval Newton (`arb/tools.py: interval_newton`).
-/

namespace IntervalArith


set_option maxHeartbeats 27470 in
/-- **T18** — `Gamma (1/4)` — Arb's rigorous Gamma (reflection/AGM based).

enclosure `3.625609908221908206371609; 3.625609908221908206371609`, witness
`3.62560990822190831193`, worst error `6.851558676720030328965983e-22` <
`1.000000000000000081803054e-05`.

arb.gamma at 1/4 (reflection/AGM-based, rigorous).

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def gamma_quarter : { x : Rat // abs (Real.Gamma (1 / 4) - x) < (10 : ℝ) ^ (-5 : ℤ) } := by lynth
/-- info: 'IntervalArith.gamma_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gamma_quarter

set_option maxHeartbeats 2233 in
/-- **T20** — `pi` to within `1/1000`: the classical rational witness is `355/113` (continued
fractions / interval bisection).

enclosure `3.141592653589793115997963; 3.141592653589793115997963`, witness `355 / 113`, worst
error `2.66764189062422294610122e-07` < `0.001000000000000000020816682`.

classic continued-fraction convergent 355/113; |355/113 - pi| = 2.667642e-07.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def pi_rational : { x : Rat // abs (Real.pi - x) < 1 / 1000 } := by lynth
/-- info: 'IntervalArith.pi_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pi_rational
