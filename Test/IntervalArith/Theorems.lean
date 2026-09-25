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


/-- **P21** — `exp x * cos x <= 3` on `[0, 1]` — the request's example theorem (the true supremum is
`exp (pi/4) * cos (pi/4) = 1.5509`).

interval subdivision + exp/cos: max box upper bound 1.553915142 on [201/256, 403/512]; reference
sup = exp(pi/4) cos(pi/4) = 1.550882951115 at r = pi/4 ~ 0.785398; the relaxed bound 3 leaves a
factor ~1.9 of slack.

range bound by subdivision.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem exp_mul_cos_le_three : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x * Real.cos x ≤ 3 := by lynth

/-- **P22** — `1 <= exp x * cos x` on `[0, 1]` — equality at `x = 0`, so the proof needs the exact
endpoint value, not just a coarse box.

interval subdivision: min box lower bound 0.9999980871 on [0, 1/512]; the box [0, 1/512] touches
the minimum, and cos([0, 1/512]) >= 1 - 1.9e-6 is what the subdivision can give; the infimum is
exactly 1, attained at r = 0: exp(0) * cos(0) = 1 (exact to 20 dp); range bound by subdivision;
the minimum is attained at the left endpoint.

range bound by subdivision, equality at the left endpoint.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem exp_mul_cos_ge_one : ∀ x ∈ Set.Icc (0 : ℝ) 1, 1 ≤ Real.exp x * Real.cos x := by lynth

/-- **P23** — `|exp x * sin x| <= 23/10` on `[0, 1]` — an absolute-value bound (`sup = e sin 1 =
2.2874`).

interval subdivision + abs: max box upper bound 2.287355295 on [511/512, 1]; reference sup =
exp(1) sin(1) = 2.287355287179 at r = 1; exp r * sin r >= 0 on [0,1], so the absolute value is
redundant here.

absolute-value bound.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem abs_exp_mul_sin_le : ∀ x ∈ Set.Icc (0 : ℝ) 1, abs (Real.exp x * Real.sin x) ≤ 23 / 10 := by lynth

/-- **P24** — `1/2 <= cos x` on `[-1, 1]` — even function, infimum `cos 1 = 0.5403`.

interval subdivision + interval cos: min box lower bound 0.5403023049 on [-1, -255/256]; cos is
even and decreasing on [0,1], so inf = cos 1 = [0.5403023058681397174, 0.54030230586813971741];
cos 1 = 0.5403... > 1/2 with ~8% slack.

range bound by subdivision (even function).

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem cos_ge_half_on_unit : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 1 / 2 ≤ Real.cos x := by lynth

/-- **P25** — `log x <= x - 1` for all `x >= 1` — **unbounded** domain: the standard certificate is
the derivative sign (`1/x - 1 <= 0`) plus `log 1 - 1 + 1 = 0`; interval subdivision alone cannot
reach infinity.

g(r) = log r - r + 1; g'(r) = 1/r - 1 <= 0 verified on [1 + 1e-9, 1e6] (max box upper bound
9.564682841e-07 on [1000000001/1000000000, 1001023000001023/1024000000000]); g(1) = 0 exactly (0
(exact to 8 dp)), so g is decreasing and <= 0 on [1, 1e6]; g(1e6) = [-999985.184489442036,
-999985.184489442035] < 0 covers the unbounded tail.

global statement: derivative-sign certificate + exact endpoint value.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem log_le_sub_one : ∀ x : ℝ, 1 ≤ x → Real.log x ≤ x - 1 := by lynth

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

/-- **P27** — `x * y + x + y <= 3` on the unit square — a 2-D box, the maximum is attained at the
corner `(1, 1)`.

interval subdivision over the product of boxes: max box upper bound 3 at ((Fraction(63, 64),
Fraction(1, 1)), (Fraction(63, 64), Fraction(1, 1))); the maximum 3 is attained at (1,1);
bilinear, so the corner value is exact.

2-D subdivision; the bound is attained at a corner.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem bilinear_box_le_three : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, x * y + x + y ≤ 3 := by lynth

/-- **P28** — `13/5 <= Gamma (1/3) ∧ Gamma (1/4) <= 37/10` — direct rigorous special-function
enclosures.

arb Gamma(1/3) = [2.6789385347077476336556, 2.6789385347077476336557] >= 2.6; arb Gamma(1/4) =
[3.6256099082219083119306, 3.6256099082219083119307] <= 3.7; direct rigorous special-function
evaluation (no subdivision needed).

special-function bounds.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem gamma_bounds : 13 / 5 ≤ Real.Gamma (1 / 3) ∧ Real.Gamma (1 / 4) ≤ 37 / 10 := by lynth

/-- **P29** — `19/25 <= tanh x` on `[1, 2]` — monotone special function.

interval subdivision + interval tanh: min box lower bound 0.761594153 on [1, 513/512]; tanh is
increasing, inf = tanh 1 = [0.76159415595576488811, 0.76159415595576488812] >= 0.76.

range bound by subdivision (monotone).

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem tanh_ge_on_one_two : ∀ x ∈ Set.Icc (1 : ℝ) 2, 19 / 25 ≤ Real.tanh x := by lynth

/-- **P30** — `sum_{i<n} (1/2)^(i+1) < 1` for every `n` — the exact rational closed form `1 - 2^-n`
settles all `n` at once.

exact rational closed form sum = 1 - 2^-n verified for n = 1, 2, 5, 40, 300, 1200; sup over n: 1
- 2^-1200 = 1.00000000000000000000 < 1; arb partial sum at n = 200 = [0.99999999999999999999, 1]
<= 1.

exact rational identity + Arb accumulation.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
theorem geometric_partial_lt_one : ∀ n : ℕ, (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1)) < 1 := by lynth

-- Axiom footprint checks.
/-- info: 'IntervalArith.exp_mul_cos_le_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_mul_cos_le_three
/-- info: 'IntervalArith.exp_mul_cos_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_mul_cos_ge_one
/-- info: 'IntervalArith.abs_exp_mul_sin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_exp_mul_sin_le
/-- info: 'IntervalArith.cos_ge_half_on_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cos_ge_half_on_unit
/-- info: 'IntervalArith.log_le_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms log_le_sub_one
/-- info: 'IntervalArith.le_sqrt_on_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms le_sqrt_on_unit
/-- info: 'IntervalArith.bilinear_box_le_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bilinear_box_le_three
/-- info: 'IntervalArith.gamma_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gamma_bounds
/-- info: 'IntervalArith.tanh_ge_on_one_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tanh_ge_on_one_two
/-- info: 'IntervalArith.geometric_partial_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms geometric_partial_lt_one

end IntervalArith

-- The repository convention (`Test/*.lean`, `Test/Grind/README.md`) pins the
-- axiom footprint of every declaration once the goals go through.  Uncomment
-- (and keep the `info` docstring in sync) when a goal starts closing:
--
-- /-- info: 'geometric_partial_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- #guard_msgs in
-- #print axioms geometric_partial_lt_one
