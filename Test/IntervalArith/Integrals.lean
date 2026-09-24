import Mathlib
import Lynth

/-!
T15-T17: interval integrals `∫ y in a..b, ...` of non-elementary
integrands and with `Real.pi` as an endpoint; the certificates come from
rigorous quadrature (see `arb/tools.py: integral_midpoint`).
Ground truth: `arb/CERTIFICATES.md` / `arb/RESULTS.md` (A17, A18).
-/

namespace IntervalArith


/-- **T15** — `integral_0^1 exp (-x^2)` — non-elementary integrand; rigorous quadrature (midpoint
rule with an interval error term).

enclosure `0.7468234841568766047004146; 0.7468285237444967084030623`, witness
`0.7468241328124270253994674361318530053545`, worst error `4.390932069732768135866298e-06` <
`0.001000000000000000020816682`.

composite midpoint rule n=128, error <= h^3 M2/24 with interval M2; enclosure
[0.74682348415687665446, 0.74682852374449675817].

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def integral_exp_neg_sq : { x : Rat // abs ((∫ y in (0 : ℝ)..1, Real.exp (-(y ^ 2))) - x) < 1 / 1000 } := by lynth

/-- **T16** — `integral_0^pi sin = 2` — the integration endpoint is `Real.pi` itself.

enclosure `1.999999387362327185613253; 2.000101013209477862631047`, witness `2`, worst error
`0.0001010132094780230116535386` < `0.001000000000000000020816682`.

exact value 2; quadrature on [0, arb pi] = [1.99999938736232712394, 2.00010101320947802301].

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def integral_sin : { x : Rat // abs ((∫ y in (0 : ℝ)..Real.pi, Real.sin y) - x) < 1 / 1000 } := by lynth

/-- **T17** — `integral_0^pi x * sin x = pi` — irrational value, irrational endpoint.

enclosure `3.141520695921368400149731; 3.141822320107618082829504`, witness
`3.14152069592136821316`, worst error `0.000301624186249682679772377` <
`0.01000000000000000020816682`.

exact value pi = 3.141592653589793238462643383279502884197; quadrature =
[3.14152069592136821316, 3.14182232010761789585].

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def integral_x_sin : { x : Rat // abs ((∫ y in (0 : ℝ)..Real.pi, y * Real.sin y) - x) < 1 / 100 } := by lynth

end IntervalArith

-- The repository convention (`Test/*.lean`, `Test/Grind/README.md`) pins the
-- axiom footprint of every declaration once the goals go through.  Uncomment
-- (and keep the `info` docstring in sync) when a goal starts closing:
--
-- /-- info: 'integral_x_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- #guard_msgs in
-- #print axioms integral_x_sin
