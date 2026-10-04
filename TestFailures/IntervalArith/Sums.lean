import Mathlib
import Lynth

/-!
T12-T14 + B01-B03: finite sums and (via tail bounds) infinite series.
T12-T14 are refinement goals; B01-B03 are plain theorems about series.
Ground truth: `arb/CERTIFICATES.md` / `arb/RESULTS.md` (A13-A16, B03, B04).
-/

namespace IntervalArith


noncomputable def prod_inv_sq (k : ℕ) : ℝ := (1 : ℝ) + 1 / ((k + 1 : ℝ) ^ 2)
/-- info: 'IntervalArith.prod_inv_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_inv_sq

/-- **T15** — `∏_{k=1}^∞ (1 + 1/k²) = sinh(π)/π` — infinite product via `tprod`.

enclosure `3.6760779103749777; 3.6760779103749777`, witness `3.6760779103749777`.

The infinite product converges absolutely since ∑ 1/k² converges. -/
def infinite_product_one_plus_inv_sq : { x : Rat // Multipliable prod_inv_sq ∧ abs (∏' k : ℕ, prod_inv_sq k) - x < 1 / 200 } := by lynth
/-- info: 'IntervalArith.infinite_product_one_plus_inv_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infinite_product_one_plus_inv_sq

/-- **B02** — **Bonus / theorem form.** `sum_{k<n} 1/((k+1)(k+2)) = 1 - 1/(n+1)` for every `n` — the
exact telescoping closed form.

exact rational identity verified for n = 0..39, 100, 1000, 4000; difference = 0 in every case
(telescoping is exact).

exact rational identity -- the closed form the goal states.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem sum_telescoping : ∀ n : ℕ, (∑ k ∈ Finset.range n, 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) = 1 - 1 / ((n : ℝ) + 1) := by lynth
/-- info: 'IntervalArith.sum_telescoping' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_telescoping
