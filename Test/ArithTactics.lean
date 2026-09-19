-- End-to-end arithmetic via `lynth`: FM oracle + kernel-checked close.
import Lynth
import Lynth.Arith.Recognize
import Lynth.Arith.Fourier

open Lean Elab Tactic in
elab "lynth_trace_sys" : tactic => do
  match ← Lynth.Arith.Recognize.buildSys with
  | none => logInfo "[trace] no translatable system"
  | some sys =>
    logInfo m!"[trace] system: {sys.length} constraints"
    match Lynth.Arith.Fourier.solve sys 128 with
    | some cert => logInfo m!"[trace] REFUTED, Farkas size {cert.length}"
    | none => logInfo "[trace] no refutation"

/-- Translation + oracle fire on real elaborated `Int` hypotheses. -/
example (x : Int) (h1 : x ≤ 1) (h2 : 2 ≤ x) : x ≤ 0 := by
  lynth_trace_sys
  omega

example (x y : Int) (h : x + 2 * y = 10) : 2 * x + 4 * y ≤ 20 := by
  lynth_trace_sys
  omega

/-- `Nat` comparisons translate too (`Nat` subtraction stays opaque). -/
example (x : Nat) (h : x ≤ 1) : x ≤ 5 := by
  lynth_trace_sys
  omega

/-- B&B-only refutation: `2x = 3 ∧ x ≥ 1` is ℚ-SAT but ℤ-UNSAT. -/
example (x : Int) (h : 2 * x = 3) : x ≤ 0 := by
  lynth_trace_sys
  omega

theorem bb_demo (x : Int) (h : 2 * x = 3) : x ≤ 0 := by lynth

/-- info: 'bb_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bb_demo

theorem arith_fm1 (x : Int) (h1 : x ≤ 1) (h2 : 2 ≤ x) : x ≤ 0 := by lynth

theorem arith_fm2 (x y : Int) (h : x + 2 * y = 10) : 2 * x + 4 * y = 20 := by lynth

theorem arith_fm3 (x y : Int) (h1 : x + y ≤ 1) (h2 : 0 ≤ x) (h3 : 0 ≤ y) :
    x + y ≤ 5 := by lynth

/-- info: 'arith_fm1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arith_fm1
/-- info: 'arith_fm2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arith_fm2
/-- info: 'arith_fm3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arith_fm3
