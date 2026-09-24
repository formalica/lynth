import Mathlib
import Lynth

/-!
T01-T06: point values -- the request's shape
  `def name : { x : Rat // |<expr> - x| < <tolerance> } := by lynth`
over `cos`/`sin` of rational multiples of `pi`, `exp`, `log`, real powers
and `sqrt`.  Tolerances range from `1e-10` to the irrational `pi / 100`.
Ground truth: `arb/CERTIFICATES.md` (Arb, 256-bit, python-flint 0.9.0).
-/

namespace IntervalArith


/-- **T01** — `cos (8 * pi / 17)` — the example from the request. An exact rational multiple of
`pi`: the natural implementation reduces `pi` algebraically instead of evaluating an interval
`pi`.

enclosure `0.09226835946330200211029648; 0.09226835946330200211029648`, witness
`0.09226835946330199523`, worst error `9.651107154506480886548261e-21` <
`1.000000000000000081803054e-05`.

arb.cos_pi_fmpq(8,17) cross-check [0.0922683594633019952396, 0.0922683594633019952397];
enclosure width 1e-20.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def cos_eight_pi_over_seventeen : { x : Rat // abs (Real.cos (Real.pi * 8 / 17) - x) < (10 : ℝ) ^ (-5 : ℤ) } := by lynth

/-- **T02** — `sin (8 * pi / 17)` with an **irrational tolerance** `pi / 100`: the tolerance itself
is an interval quantity.

enclosure `0.995734176295034467685241; 0.995734176295034467685241`, witness
`0.99573417629503452187`, worst error `1.191178905481783822661036e-21` <
`0.0314159265358979339355372`.

arb.sin_pi_fmpq(8,17) cross-check [0.9957341762950345218711, 0.9957341762950345218712];
tolerance is irrational (pi/100).

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def sin_eight_pi_over_seventeen : { x : Rat // abs (Real.sin (Real.pi * 8 / 17) - x) < Real.pi / 100 } := by lynth

/-- **T03** — `exp 2` — the elementary transcendental value (compare `Test/Corpus.lean` style goals,
now with a rational witness).

enclosure `7.389056098930650406941822; 7.389056098930650406941822`, witness
`7.38905609893065022723`, worst error `4.274605750078132078731753e-22` <
`9.999999999999999547481118e-07`.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def exp_two : { x : Rat // abs (Real.exp 2 - x) < 1 / 1000000 } := by lynth

/-- **T04** — `log (pi / 100)` — negative value, irrational argument.

enclosure `-3.460440300138690972175937; -3.460440300138690972175937`, witness
`-3.4604403001386911939`, worst error `7.444441984330296415091405e-21` <
`1.000000000000000081803054e-05`.

log of the irrational pi/100; enclosure [-3.4604403001386911938926, -3.4604403001386911938925].

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def log_pi_over_hundred : { x : Rat // abs (Real.log (Real.pi / 100) - x) < 1 / 100000 } := by lynth

/-- **T05** — `2 ^ (1/3)` — real power (`Real.rpow`), i.e. Arb's `root 3` / `pow` path.

enclosure `1.259921049894873190666544; 1.259921049894873190666544`, witness
`1.25992104989487316476`, worst error `7.210607278228350806020189e-21` <
`9.999999999999999547481118e-07`.

two Arb paths agree: root(3) = [1.2599210498948731647672, 1.2599210498948731647673], exp(log 2 /
3) = [1.2599210498948731647672, 1.2599210498948731647673].

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def rpow_two_one_third : { x : Rat // abs ((2 : ℝ) ^ ((1 : ℝ) / 3) - x) < 1 / 1000000 } := by lynth

/-- **T06** — `sqrt 2` — algebraic value, 10-digit tolerance, needs ~20 digits of working precision
to place a rational witness.

enclosure `1.414213562373095145474622; 1.414213562373095145474622`, witness
`1.4142135623730950488`, worst error `1.688724209698078592492359e-21` <
`1.000000000000000036432197e-10`.

Arb ground truth: `arb/CERTIFICATES.md` (`arb/validate_lean_tests.py`). -/
def sqrt_two : { x : Rat // abs (Real.sqrt 2 - x) < (10 : ℝ) ^ (-10 : ℤ) } := by lynth

end IntervalArith

-- The repository convention (`Test/*.lean`, `Test/Grind/README.md`) pins the
-- axiom footprint of every declaration once the goals go through.  Uncomment
-- (and keep the `info` docstring in sync) when a goal starts closing:
--
-- /-- info: 'sqrt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- #guard_msgs in
-- #print axioms sqrt_two
