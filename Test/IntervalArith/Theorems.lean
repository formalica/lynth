import Mathlib
import Lynth

/-!
P21-P30: plain theorems (no witness returned), the second half of the
20/10 split requested.  They cover: range bounds by subdivision, an
unbounded-domain derivative certificate (P25), a stationary-point case
(P26), a 2-D box (P27), special-function bounds (P28, P29) and an exact
rational closed form (P30).
Ground truth: `arb/CERTIFICATES.md` / `arb/tests_arb.py` A21-A30.
-/

namespace IntervalArith


set_option maxHeartbeats 499 in
/-- **P26** — `x <= sqrt x` on `[0, 1]` — equality at both endpoints and a stationary point at
`1/4`: derivative signs + exact endpoint values.

g(r) = sqrt r - r; g' = 1/(2 sqrt r) - 1 >= 0 on [1/100, 1/4] (min box lower bound
-3.725290298e-09 on [797/3200, 1/4]); and <= 0 on [1/4, 1] (max box upper bound 1.11758709e-08
on [1/4, 259/1024]), so the minimum is at an endpoint; g(0) = 0 (0 (exact to 8 dp)), g(1/4) =
0.25 (0.25 (exact to 8 dp)), g(1) = 0 (0 (exact to 8 dp)).

derivative signs + exact endpoint values (raw interval evaluation cannot prove an equality-tight
bound).

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem le_sqrt_on_unit : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≤ Real.sqrt x := by lynth
/-- info: 'IntervalArith.le_sqrt_on_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms le_sqrt_on_unit

set_option maxHeartbeats 31351 in
/-- **P28** — `13/5 <= Gamma (1/3) ∧ Gamma (1/4) <= 37/10` — direct rigorous special-function
enclosures.

arb Gamma(1/3) = [2.6789385347077476336556, 2.6789385347077476336557] >= 2.6; arb Gamma(1/4) =
[3.6256099082219083119306, 3.6256099082219083119307] <= 3.7; direct rigorous special-function
evaluation (no subdivision needed).

special-function bounds.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem gamma_bounds : 13 / 5 ≤ Real.Gamma (1 / 3) ∧ Real.Gamma (1 / 4) ≤ 37 / 10 := by lynth
/-- info: 'IntervalArith.gamma_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gamma_bounds
