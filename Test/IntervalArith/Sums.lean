import Mathlib
import Lynth

/-!
T12-T14 + B01-B03: finite sums and (via tail bounds) infinite series.
T12-T14 are refinement goals; B01-B03 are plain theorems about series.
Ground truth: `arb/CERTIFICATES.md` / `arb/RESULTS.md` (A13-A16, B03, B04).
-/

namespace IntervalArith


/-- **T12** — `sum_{k<5} exp (-k) * cos k` — interval accumulation of five terms.

enclosure `1.081186035720703708662427; 1.081186035720703708662427`, witness
`1.0811860357207037787`, worst error `2.68364479081210705425743e-22` <
`9.999999999999999547481118e-07`.

5 terms, interval accumulation; mpmath reference 1.081186035720703778700268364479081210709.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def sum_exp_cos : { x : Rat // abs ((∑ k ∈ Finset.range 5, Real.exp (-(k : ℝ)) * Real.cos (k : ℝ)) - x) < 1 / 1000000 } := by lynth

/-- **T13** — `sum_{k<100} (1/2)^(k+1)` with tolerance `1e-30`. The exact value is the rational `1 -
2^-100`, so this one is provable by exact rational arithmetic alone (Arb certifies it
independently).

enclosure `1; 1`, witness `1 - 1 / 1267650600228229401496703205376`, worst error `0` <
`1.000000000000000083336421e-30`.

exact rational identity 1 - 2^-100 = 1.00000000000000000000; Arb accumulation agrees to
[0.99999999999999999999, 1].

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def sum_geometric_half_powers : { x : Rat // abs ((∑ k ∈ Finset.range 100, (1 / 2 : ℝ) ^ (k + 1)) - x) < (10 : ℝ) ^ (-30 : ℤ) } := by lynth

/-- **T14** — `sum_{k=1..5} sin (pi k / 7)` — finite sum of exact `pi`-rationals.

enclosure `3.947402528417264910842732; 3.947402528417264910842732`, witness
`3.94740252841726495192`, worst error `8.920752184336689367028283e-21` <
`9.999999999999999547481118e-07`.

exact pi-reduction sin_pi_fmpq(k,7) per term; mpmath reference
3.94740252841726495192892075218433668954.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def sum_sin_pi_over_seven : { x : Rat // abs ((∑ k ∈ Finset.range 5, Real.sin (Real.pi * (k + 1) / 7)) - x) < 1 / 1000000 } := by lynth

noncomputable def prod_inv_sq (k : ℕ) : ℝ := (1 : ℝ) + 1 / ((k + 1 : ℝ) ^ 2)

/-- **T15** — `∏_{k=1}^∞ (1 + 1/k²) = sinh(π)/π` — infinite product via `tprod`.

enclosure `3.6760779103749777; 3.6760779103749777`, witness `3.6760779103749777`.

The infinite product converges absolutely since ∑ 1/k² converges. -/
def infinite_product_one_plus_inv_sq : { x : Rat // Multipliable prod_inv_sq ∧ abs (∏' k : ℕ, prod_inv_sq k) - x < 1 / 200 } := by lynth

/-- **B01** — **Bonus / theorem form.** `|sum_{j=1..1000} 1/j^2 - pi^2/6| < 1/500`: an infinite
series handled by an exact partial sum plus an integral tail bound (the tail is `~1/1000`).

exact rational partial sum S_1000 = 1.64393456668155990563; arb pi^2/6 =
[1.6449340668482264364724, 1.6449340668482264364725]; rigorous difference S_1000 - pi^2/6 in
[-0.0009995001666666333568073144, -0.0009995001666666333568073144] = -9.995002e-04 (approx
-9.995002e-04), |.| < 1/500 = 0.002; integral-test tail bound: sum_(j>1000) 1/j^2 <= 1/1000 (and
>= 0.000999001).

infinite series bounded by an exact partial sum + an integral tail.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem series_inv_sq_tail : abs ((∑ k ∈ Finset.range 1000, 1 / ((k : ℝ) + 1) ^ 2) - Real.pi ^ 2 / 6) < 1 / 500 := by lynth

/-- **B02** — **Bonus / theorem form.** `sum_{k<n} 1/((k+1)(k+2)) = 1 - 1/(n+1)` for every `n` — the
exact telescoping closed form.

exact rational identity verified for n = 0..39, 100, 1000, 4000; difference = 0 in every case
(telescoping is exact).

exact rational identity -- the closed form the goal states.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem sum_telescoping : ∀ n : ℕ, (∑ k ∈ Finset.range n, 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) = 1 - 1 / ((n : ℝ) + 1) := by lynth

/-- **B03** — **Bonus / theorem form.** `|sum_{k<100} (-1)^k/(2k+1) - pi/4| < 1/100` — Leibniz'
alternating series: the tail bound is the first omitted term (`1/201`), the value is `pi/4`.

arb partial sum S_100 = [0.7828982258896381910768, 0.7828982258896381910769]; arb pi/4 =
[0.7853981633974483096156, 0.7853981633974483096157]; rigorous |S_100 - pi/4| <
0.002499937507810118426931911 (2.499938e-03) < 1/100; Leibniz tail bound: the omitted tail is <=
1/(2*100+1) = 1/201 < 1/100.

alternating series + exact pi/4 enclosure.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem alternating_series_pi_over_four : abs ((∑ k ∈ Finset.range 100, (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1)) - Real.pi / 4) < 1 / 100 := by lynth

-- Axiom footprint checks.
/-- info: 'IntervalArith.sum_exp_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_exp_cos
/-- info: 'IntervalArith.sum_geometric_half_powers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_geometric_half_powers
/-- info: 'IntervalArith.sum_sin_pi_over_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_sin_pi_over_seven
/-- info: 'IntervalArith.prod_inv_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_inv_sq
/-- info: 'IntervalArith.infinite_product_one_plus_inv_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infinite_product_one_plus_inv_sq
/-- info: 'IntervalArith.series_inv_sq_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms series_inv_sq_tail
/-- info: 'IntervalArith.sum_telescoping' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_telescoping
/-- info: 'IntervalArith.alternating_series_pi_over_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alternating_series_pi_over_four

end IntervalArith

-- The repository convention (`Test/*.lean`, `Test/Grind/README.md`) pins the
-- axiom footprint of every declaration once the goals go through.  Uncomment
-- (and keep the `info` docstring in sync) when a goal starts closing:
--
-- /-- info: 'alternating_series_pi_over_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- #guard_msgs in
-- #print axioms alternating_series_pi_over_four
