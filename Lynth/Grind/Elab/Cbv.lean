/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Lynth.Grind.Elab.Basic
import Lean.Meta.Tactic.Cbv.Main
namespace Lean.Lynth.Grind.Elab
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta

@[builtin_lynth_grind_tactic Parser.Tactic.Grind.symCbv] def evalSymCbv : GrindTactic := fun _ => withMainContext do
  ensureSym
  let goal ← getMainGoal
  let result ← liftGrindM <|
    Lean.Meta.Tactic.Cbv.cbvGoalCore goal.mvarId
  match result with
  | none => replaceMainGoal []
  | some mvarId => replaceMainGoal [{ goal with mvarId }]

end Lean.Lynth.Grind.Elab
