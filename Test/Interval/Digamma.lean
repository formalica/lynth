import Mathlib
import Lynth

open Lynth.Interval
open Lynth.Interval.Fns

-- Digamma evaluates `log`/`rpow`/`sin`/`cos` interval kernels; kernel
-- certification is slow, so these run native (per-declaration native
-- axioms, cf. `docs/interval/README.md`).
set_option lynth.interval.trust "native"

/-! # Digamma (shift + Stirling for `x > 0`, reflection for negatives).

Ground truth from the recurrence `ψ(x+1) = ψ(x) + 1/x` and
`ψ(1) = -γ`, `ψ(1/2) = -γ - 2·ln 2` with `γ = 0.5772156649`:
`ψ(1) = -0.5772156649`, `ψ(2) = 0.4227843351`, `ψ(3) = 0.9227843351`,
`ψ(1/2) = -1.9635100260`, `ψ(2.5) = 0.7031566407`,
`ψ(-1/2) = ψ(3/2) = 0.0364899740` (via `π·cot(-π/2) = 0`).
Analytic bounds are `sorry`'d (`Fns/Digamma.lean`, handoff
`/tmp/digamma_thm.lean`); `#eval!` (unsafe) is used since `#eval`
refuses `sorryAx` proofs.
-/

set_option maxHeartbeats 60000 in
-- D1: ψ(1) = -γ. -0.5772156649
def dig_one : { x : Rat //
    abs (rdig 1 - x) < 1 / 1000000 } := by
  lynth
#print axioms dig_one
#eval! dig_one.1

set_option maxHeartbeats 60000 in
-- D2: ψ(2) = 1-γ. 0.4227843351
def dig_two : { x : Rat //
    abs (rdig 2 - x) < 1 / 1000000 } := by
  lynth
#print axioms dig_two
#eval! dig_two.1

set_option maxHeartbeats 60000 in
-- D3: ψ(1/2) = -γ-2ln2. -1.9635100260
def dig_half : { x : Rat //
    abs (rdig (1 / 2) - x) < 1 / 1000000 } := by
  lynth
#print axioms dig_half
#eval! dig_half.1

set_option maxHeartbeats 60000 in
-- D4: ψ(2.5) via shifts. 0.7031566407
def dig_five_halves : { x : Rat //
    abs (rdig (5 / 2) - x) < 1 / 1000000 } := by
  lynth
#print axioms dig_five_halves
#eval! dig_five_halves.1

set_option maxHeartbeats 60000 in
-- D5: ψ(-1/2) via reflection. 0.0364899740
def dig_neg_half : { x : Rat //
    abs (rdig (-1 / 2) - x) < 1 / 1000 } := by
  lynth
#print axioms dig_neg_half
#eval! dig_neg_half.1

set_option maxHeartbeats 60000 in
-- D6: ψ(3) = 3/2-γ. 0.9227843351
def dig_three : { x : Rat //
    abs (rdig 3 - x) < 1 / 1000000 } := by
  lynth
#print axioms dig_three
#eval! dig_three.1
