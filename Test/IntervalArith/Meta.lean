module
import Mathlib
public import Lynth

/-! Unsupported interval goals stop before the precision retry loop, or at
their first structural failure. Numerical uncertainty still permits retries. -/

open Lean Meta Elab Tactic Qq MeasureTheory

namespace IntervalArith.FailFast

private meta def expectUnsupported (target : Lean.Expr) (attempts : Nat) : TacticM Unit := do
  let result ← Lynth.Interval.Goals.Composition.search target
  unless result.proof?.isNone && !result.retryable && result.attempts == attempts do
    throwError "expected unsupported after {attempts} attempts, got {result.attempts} \
      attempts (retryable: {result.retryable})"

example : True := by
  run_tac withMainContext do
    let target ← Lean.Elab.Term.elabTerm (← `(term|
      ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≤ Real.sqrt x)) none
    expectUnsupported target 0
  trivial

example : True := by
  run_tac withMainContext do
    let target ← Lean.Elab.Term.elabTerm (← `(term| {n : ℕ // 0 < n})) none
    expectUnsupported target 0
  trivial

example (f : ℝ → ℝ) : True := by
  run_tac withMainContext do
    let some decl := (← getLCtx).findFromUserName? `f | throwError "no function"
    let fn : Q(ℝ → ℝ) := decl.toExpr
    let target : Q(Prop) := q(|$fn (∫ x in (0 : ℝ)..1, x)| < 2)
    expectUnsupported target 1
  trivial

example : True := by
  run_tac withMainContext do
    let target ← Lean.Elab.Term.elabTerm (← `(term|
      |∑' k : ℕ, Real.sin (k : ℝ)| < 2)) none
    expectUnsupported target 1
  trivial

example : True := by
  run_tac withMainContext do
    let target ← Lean.Elab.Term.elabTerm (← `(term|
      (∫ x in (0 : ℝ)..1, x) = (1 / 2 : ℝ))) none
    expectUnsupported target 1
  trivial

example (f : ℝ → ℝ) : True := by
  run_tac withMainContext do
    let some decl := (← getLCtx).findFromUserName? `f | throwError "no function"
    let fn : Q(ℝ → ℝ) := decl.toExpr
    let target : Q(Prop) := q(|∑' k : ℕ, $fn (k : ℝ)| < 2)
    expectUnsupported target 1
  trivial

example (f : ℝ → ℝ) : True := by
  run_tac withMainContext do
    let some decl := (← getLCtx).findFromUserName? `f | throwError "no function"
    let fn : Q(ℝ → ℝ) := decl.toExpr
    let target : Q(Prop) := q(|∫ x in (0 : ℝ)..1, $fn x| < 2)
    expectUnsupported target 1
  trivial

/-- A successful numerical field must not leak its witness when another
field is unsupported. -/
example (f : ℝ → ℝ) : True := by
  run_tac withMainContext do
    let witness : Q(ℚ) ← mkFreshExprMVar q(ℚ)
    let some decl := (← getLCtx).findFromUserName? `f | throwError "no function"
    let fn : Q(ℝ → ℝ) := decl.toExpr
    let target : Q(Prop) := q($fn 0 < 1 ∧
      |(∫ x in (0 : ℝ)..1, x) - ($witness : ℝ)| < 1 / 100)
    expectUnsupported target 1
    if ← witness.mvarId!.isAssigned then
      throwError "failed composition search leaked a witness assignment"
  trivial

/-- This supported comparison needs more than 64 bits; structural rejection
must not disable the normal numerical precision schedule. -/
public theorem preciseFiniteSum :
    (∑ _k ∈ Finset.range 1, Real.exp 1) <
      (27182818284590452353602874713526624977572470936999595749669676277240767 : ℝ) /
        10 ^ 70 := by
  run_tac withMainContext do
    let goal ← getMainGoal
    let result ← Lynth.Interval.Goals.Composition.search (← goal.getType)
    unless result.attempts > 1 do
      throwError "expected a genuine numerical precision retry"
    let some proof := result.proof? | throwError "supported precision retry failed"
    goal.assign proof
    replaceMainGoal []

/-- info: 'IntervalArith.FailFast.preciseFiniteSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms preciseFiniteSum

/-- Rounding a ratio just below one up to one must still request more
precision, rather than being classified as an unsupported series. -/
public theorem geometricRatioNeedsPrecision :
    (∑' k : ℕ, (1 - 1 / (2 : ℝ) ^ 100) ^ k) < (2 : ℝ) ^ 120 := by
  run_tac withMainContext do
    let goal ← getMainGoal
    let result ← Lynth.Interval.Goals.Composition.search (← goal.getType)
    unless result.attempts > 1 do
      throwError "expected a retry for the rounded geometric ratio"
    let some proof := result.proof? | throwError "geometric precision retry failed"
    goal.assign proof
    replaceMainGoal []

/-- info: 'IntervalArith.FailFast.geometricRatioNeedsPrecision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 geometricRatioNeedsPrecision._native.native_decide.ax_1_4] -/
#guard_msgs in
#print axioms geometricRatioNeedsPrecision

end IntervalArith.FailFast
