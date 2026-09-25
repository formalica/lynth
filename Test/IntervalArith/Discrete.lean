import Mathlib
import Lynth

/-!
The discrete layer: rounding and exact integer answers of composed
expressions, in the shape

  `def name : { n : Nat // n = ⌊<composition>⌋₊ } := by lynth`
  `def name : { s : ℤ // Real.sign <composition> = (s : ℝ) } := by lynth`

`⌊·⌋₊` is mathlib's `Nat.floor : ℝ → ℕ` (the plain `⌊·⌋` is `Int.floor` and
would make the `Nat` goal ill-typed).  The certificate is a strict enclosure:
the Arb ball of the composition has to sit inside `(n, n+1)` for a floor and
inside `(n-1, n)` for a ceiling, with the margin recorded in
`arb/CERTIFICATES.md`.  MD05 is an exact integer identity
(`Nat.gcd (fib 10) (fib 15) = 5`, certified by the Bezout expression
`fib 15 - 11 * fib 10`); MD06 certifies a *sign*, not a value.
Ground truth: `arb/CERTIFICATES.md` (MD01-MD07).
-/

namespace IntervalArith


/-- **MD01** — `floor_exp_two_add_sin_div_cos`: the floor of `exp, sin, cos` composed at `x = 2, 1`,
returned as a `Nat`.

Arb enclosure of the composition: [15.2331888913818538, 15.2331888913818538]; strict floor
certificate n = 15 with margin 0.2332 (the enclosure lies strictly inside (15, 16)).

a strict enclosure between two consecutive integers decides the floor: the shape from the
review: a Nat witness equal to the floor of a composition of three functions divided by a
fourth.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def floor_exp_two_add_sin_div_cos : { n : Nat // n = ⌊(Real.exp 2 + Real.sin 1) / Real.cos 1⌋₊ } := by lynth

/-- **MD02** — `floor_gamma_quarter_add_gamma_third`: the floor of `Gamma` composed at `x = 1/4,
1/3`, returned as a `Nat`.

Arb enclosure of the composition: [6.3045484429296561, 6.3045484429296561]; strict floor
certificate n = 6 with margin 0.3045 (the enclosure lies strictly inside (6, 7)).

a strict enclosure between two consecutive integers decides the floor: .

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def floor_gamma_quarter_add_gamma_third : { n : Nat // n = ⌊Real.Gamma (1 / 4) + Real.Gamma (1 / 3)⌋₊ } := by lynth

/-- **MD03** — `floor_hundred_tanh_sqrt_two`: the floor of `tanh, sqrt` composed at `x = sqrt 2`,
returned as a `Nat`.

Arb enclosure of the composition: [88.8385561585660497, 88.8385561585660497]; strict floor
certificate n = 88 with margin 0.1614 (the enclosure lies strictly inside (88, 89)).

a strict enclosure between two consecutive integers decides the floor: .

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def floor_hundred_tanh_sqrt_two : { n : Nat // n = ⌊100 * Real.tanh (Real.sqrt 2)⌋₊ } := by lynth

/-- **MD04** — `floor_ten_sqrt_sum`: the floor of `sqrt` composed at `x = 2, 3, 5`, returned as a
`Nat`.

Arb enclosure of the composition: [53.8233234744176201, 53.8233234744176201]; strict floor
certificate n = 53 with margin 0.1767 (the enclosure lies strictly inside (53, 54)).

a strict enclosure between two consecutive integers decides the floor: sum of three radicals --
the classic test for a summation-based interval engine.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def floor_ten_sqrt_sum : { n : Nat // n = ⌊10 * (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5)⌋₊ } := by lynth

/-- **MD05** — `gcd_of_fib`: an exact integer identity over `Nat.gcd, Nat.fib` (inputs `n = 10,
15`), returned as a `Nat`.

exact integer identity: the Bezout expression `fib 15 - 11 * fib 10` has a zero-width Arb ball,
so the value 5 is exact -- no interval search.

gcd(55, 610) = 5 -- the two Fibonacci numbers share the factor 5.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def gcd_of_fib : { n : Nat // n = Nat.gcd (Nat.fib 10) (Nat.fib 15) } := by lynth

/-- **MD06** — `sign_exp_sub_cos`: the sign of `exp, cos` composed at `x = 1, 1/2`, returned as an
`Int`.

Arb enclosure [-1, -1] is strictly negative, so the sign is -1 (margin 1.0000 to 0).

the enclosure is strictly one-signed, which decides the sign: a comparison between two
transcendental values rather than a numerical value.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def sign_exp_sub_cos : { s : ℤ // Real.sign (Real.exp (-1) - Real.cos (1 / 2)) = (s : ℝ) } := by lynth

/-- **MD07** — `ceil_ten_exp_cos`: the ceiling of `exp, cos` composed at `x = 1`, returned as a
`Nat`.

Arb enclosure of the composition: [17.1652569954890346, 17.1652569954890346]; strict ceiling
certificate n = 18 with margin 0.1653 (the enclosure lies strictly inside (17, 18)).

a strict enclosure between two consecutive integers decides the ceiling: the ceiling counterpart
of the floor tests: 10 * exp (cos 1) ~ 17.165 sits between the consecutive integers 17 and 18.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`, table
`arb/compositions.py`). -/
def ceil_ten_exp_cos : { n : Nat // n = ⌈10 * Real.exp (Real.cos 1)⌉₊ } := by lynth

-- Axiom footprint checks.
/-- info: 'IntervalArith.floor_exp_two_add_sin_div_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floor_exp_two_add_sin_div_cos
/-- info: 'IntervalArith.floor_gamma_quarter_add_gamma_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floor_gamma_quarter_add_gamma_third
/-- info: 'IntervalArith.floor_hundred_tanh_sqrt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floor_hundred_tanh_sqrt_two
/-- info: 'IntervalArith.floor_ten_sqrt_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms floor_ten_sqrt_sum
/-- info: 'IntervalArith.gcd_of_fib' does not depend on any axioms -/
#guard_msgs in
#print axioms gcd_of_fib
/-- info: 'IntervalArith.sign_exp_sub_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_exp_sub_cos
/-- info: 'IntervalArith.ceil_ten_exp_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ceil_ten_exp_cos

end IntervalArith

-- The repository convention (`Test/*.lean`, `Test/Grind/README.md`) pins the
-- axiom footprint of every declaration once the goals go through.  Uncomment
-- (and keep the `info` docstring in sync) when a goal starts closing:
--
-- /-- info: 'ceil_ten_exp_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- #guard_msgs in
-- #print axioms ceil_ten_exp_cos
