import Mathlib
import Lynth

/-!
B04-B05: interval linear algebra -- a determinant value and a 2x2
linear system posed as a refinement goal (Arb's `arb_mat.det` /
`arb_mat.solve`; see `arb/tests_arb.py` C05).
-/

namespace IntervalArith


/-- **B04** — **Bonus.** `det !![1, 2; 3, 4] = -2` — a matrix entry point (Arb's `arb_mat.det`).

enclosure `-2; -2`, witness `-2`, worst error `0` < `0.001000000000000000020816682`.

arb_mat det = -2 (exact to 20 dp) (exact: 1*4 - 2*3 = -2).

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def det_two_by_two : { d : Rat // abs (Matrix.det (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) - d) < 1 / 1000 } := by lynth

/-- **B05** — **Bonus.** A 2x2 linear system as a refinement goal: the residual form `|2 v.1 + v.2 -
1| < 1/1000 ∧ |v.1 + 3 v.2 - 2| < 1/1000` pins down `(1/5, 3/5)` (Arb's `arb_mat.solve`).

enclosure `0.2000000000000000111022302; 0.2000000000000000111022302`, witness `1 / 5 (v.1), 3 /
5 (v.2)`, worst error `9.931593851227505292864377e-77` < `0.001000000000000000020816682`.

arb_mat.solve gives v = ([0.19999999999999999999, 0.20000000000000000001],
[0.59999999999999999999, 0.60000000000000000001]); worst residual of the interval solution
9.93e-77; exact solution (1/5, 3/5).

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def linear_system_witness : { v : Rat × Rat // abs ((2 * v.1 + v.2) - 1) < 1 / 1000 ∧ abs ((v.1 + 3 * v.2) - 2) < 1 / 1000 } := by lynth

end IntervalArith

-- The repository convention (`Test/*.lean`, `Test/Grind/README.md`) pins the
-- axiom footprint of every declaration once the goals go through.  Uncomment
-- (and keep the `info` docstring in sync) when a goal starts closing:
--
-- /-- info: 'linear_system_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- #guard_msgs in
-- #print axioms linear_system_witness
