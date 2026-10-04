import Mathlib
import Lynth

/-!
# BoundSep — floor/ceil gates at an interval boundary

Three goals that pin down where the discrete-witness gate in
`Lynth/Interval/Goals/Discrete.lean` actually fails.

The gate is

* `natFloorLoop` (line 129) and `intFloorWit` (line 197): `if ⌊lo⌋ != ⌊hi⌋ then return none`
* `natCeilWit` (172) and `intCeilWit` (215): `if ⌈lo⌉ != ⌈hi⌉ then return none`
* `intRoundWit` (236): `if round lo != round hi then return none`

so `⌊·⌋`/`⌈·⌉` need both endpoints to land on the *same* integer, while
`round` has a ±½ window and only needs the endpoints to agree after rounding.
Any enclosure that strictly straddles an integer therefore kills floor/ceil and
leaves round untouched.

Common shape in all three: the floor/ceil argument is a transcendental
quantity whose *exact* value is an integer, so the enclosure straddles that
integer at every precision in `precSchedule` and can never pin it.

All three are expected to FAIL, so each is guarded with `#print axioms`: a
result of `[sorryAx]` is the confirmation that `lynth` did not close the goal
and no axiom-bearing proof slipped in.  A non-trivial axiom list here would mean
the goal was closed by something unsound, not that the gate held.

Read-only diagnostics; nothing in the repository is modified.
-/


open Lynth.Interval

/-! ### 1. `log ∘ exp = id`, argument exactly the integer 9

`Real.exp 9 ≈ 8103.08` and `Real.log 8103.08 = 9` exactly, so the enclosure of
`Real.log (Real.exp 9)` straddles 9 at every scheduled precision:
`⌊lo⌋ = 8`, `⌊hi⌋ = 9`, the gate fails. -/

def t1 : { n : Int // n = ⌊Real.log (Real.exp 9)⌋ } := by
  lynth

#print axioms t1

/-! ### 2. `⌊2 / (√2)²⌋ · π`

`(√2)² = 2` exactly, so the quotient is exactly 1 and the answer is π.  The
enclosure of `2 / (√2)²` strictly straddles 1, so `⌊lo⌋ = 0`, `⌊hi⌋ = 1` and the
gate fails.  The whole enclosure `[0, 1]·π = [0, π]` is also far too wide for the
1e-6 tolerance, so the outer goal cannot be rescued either. -/

def t2 : { x : Rat //
    abs (((⌊2 / Real.sqrt 2 ^ 2⌋ : ℤ) : ℝ) * Real.pi - x) < 1 / 1000000 } := by
  lynth

#print axioms t2

/-! ### 3. nested floor/ceil, two *independent* Gamma facts

`⌊ ⌈Γ(½)/√π⌉ + Γ(4) ⌋ · π`, true value `⌊1 + 6⌋·π = 7π`.

Unlike a single `exp (log n)` round-trip, this needs two logically unrelated
identities, which `Fns/Gamma.lean` reaches by different routes:

* the inner `⌈Γ(½)/√π⌉` needs `Γ(½) = √π`; its argument is exactly 1, so the
  enclosure is `[1, 2]` and the ceil gate fails (`1 ≠ 2`);
* the added `Γ(4)` needs `Γ(n) = (n-1)!`; its argument is exactly 6, so it
  contributes only a sub-ulp widening;
* the outer `⌊· + ·⌋` needs **both**, and its argument is exactly 7, giving
  enclosure `[7-ε, 8]` and `⌊lo⌋ = 6 ≠ ⌊hi⌋ = 8`.

So the solver has to fail twice, for two separate reasons: no single shared rule
can discharge both terms.

The `maxHeartbeats` below is **elaboration-only** — it is *not* a budget for
proving anything, and nothing here is expected to close.  At the default
200 000 the *goal type* alone dies: Lean times out at `«abstract nested proofs»`
while abstracting the `⌈·⌉`/`⌊·⌋` subproofs, and at `whnf` inside `lynth`, before
any procedure is even selected.  A timeout is fatal rather than recoverable, so
`t3` is never added to the environment and the `#print axioms t3` below would
report `Unknown constant t3` instead of the `sorryAx` that actually records the
intended failure.  400 000 (2×) is the smallest round figure that elaborates;
the file previously used 4 000 000, which is 10× more than needed. -/

set_option maxHeartbeats 400000 in
def t3 : { x : Rat //
    abs (Real.pi * (⌊((⌈Real.Gamma (1 / 2) / Real.sqrt Real.pi⌉ : ℝ) + Real.Gamma 4)⌋ : ℝ) - x)
        < 1 / 1000000 } := by
  lynth

#print axioms t3
