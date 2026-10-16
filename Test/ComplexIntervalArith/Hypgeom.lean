import Mathlib
import Lynth

open Lynth.Interval
open Lynth.Interval.Fns

-- Hypergeometric interval checks run native (per-declaration native axioms):
-- the enclosures are wide enough that kernel certification recurses too deep.
set_option lynth.interval.trust "native"

/-! # Complex hypergeometric `pFq` (H1–H4).

`Complex.HGFun` with genuinely complex arguments goes through the complex
core (`Fns/Hypgeom.lean`, `cpfqCoreBox`): same FLINT `pfq_direct` engine
with `CBox` arithmetic. All-real arguments keep the real core (see
`Test/Interval/Hypgeom.lean` for the real-path costs).

Ground truths are closed forms / mpmath cross-checks (17-digit).
TEMPORARY: the complex core soundness is `sorry`'d (handoff:
`/tmp/hyperc`), so these carry `sorryAx` until the proofs land.
-/

namespace ComplexIntervalArith

set_option maxHeartbeats 2987 in
-- C1: real args through the complex entry take the real core:
-- ₂F₁(1,1;2;1/2) = 2ln2. 1.3862943611
def cx_hyp_real : { p : Rat × Rat //
    ‖Complex.HGFun {1, 1} {2} ((1 / 2 : ℂ)) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 1000000 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_hyp_real' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_hyp_real._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_hyp_real
#eval! cx_hyp_real.1

set_option maxHeartbeats 4428 in
-- C2: ₂F₁(1,1;2;1/4+i/4). 1.1135047380 + 0.1734974795·I
def cx_hyp_2f1 : { p : Rat × Rat //
    ‖Complex.HGFun {1, 1} {2} ((1 / 4 : ℂ) + (1 / 4 : ℂ) * Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 100 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_hyp_2f1' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_hyp_2f1._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_hyp_2f1
#eval! cx_hyp_2f1.1

set_option maxHeartbeats 6336 in
-- C3: 17 parameters, ₉F₈(1⁹;2⁸;1/4+i/8). 1.0009837614 + 0.0004981508·I
def cx_hyp_9f8 : { p : Rat × Rat //
    ‖Complex.HGFun {1, 1, 1, 1, 1, 1, 1, 1, 1} {2, 2, 2, 2, 2, 2, 2, 2} ((1 / 4 : ℂ) + (1 / 8 : ℂ) * Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 100 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_hyp_9f8' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_hyp_9f8._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_hyp_9f8
#eval! cx_hyp_9f8.1

set_option maxHeartbeats 4636 in
-- C4: terminating, ₂F₁(-2,1+i;2;1/4+i/8). 0.8515625 - 0.3411458333·I
def cx_hyp_term : { p : Rat × Rat //
    ‖Complex.HGFun {-2, 1 + Complex.I} {2} ((1 / 4 : ℂ) + (1 / 8 : ℂ) * Complex.I) - ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ < 1 / 100 } := by
  lynth
/-- info: 'ComplexIntervalArith.cx_hyp_term' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 cx_hyp_term._native.native_decide.ax_1] -/
#guard_msgs in
#print axioms cx_hyp_term
#eval! cx_hyp_term.1

end ComplexIntervalArith
