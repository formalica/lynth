/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.AC.Util
open Lean.Meta
public section
namespace Lean.Lynth.Grind.AC
open Lean.Grind
variable [Monad M] [MonadGetStruct M] [MonadError M]
/-- Explicit denotation helpers over `Lean.Grind.AC` types.
Core defines these as dot-notation extensions in the types' own
namespace; we cannot reuse those names (core owns them and is loaded
in every Mathlib session), so they live here under explicit names
with identical bodies. -/
def seqDenoteExpr (s : AC.Seq) : M Expr := do
  match s with
  | .var x => return (← getStruct).vars[x]!
  | .cons x s => return mkApp2 (← getStruct).op (← getStruct).vars[x]! (← seqDenoteExpr s)

def acExprDenoteExpr (e : AC.Expr) : M Expr := do
  match e with
  | .var x => return (← getStruct).vars[x]!
  | .op lhs rhs => return mkApp2 (← getStruct).op (← acExprDenoteExpr lhs) (← acExprDenoteExpr rhs)


def EqCnstr.denoteExpr (c : EqCnstr) : M Expr := do
  let s ← getStruct
  return mkApp3 (mkConst ``Eq [s.u]) s.type (← seqDenoteExpr c.lhs) (← seqDenoteExpr c.rhs)

def DiseqCnstr.denoteExpr (c : DiseqCnstr) : M Expr := do
  let s ← getStruct
  return mkApp3 (mkConst ``Ne [s.u]) s.type (← seqDenoteExpr c.lhs) (← seqDenoteExpr c.rhs)


end Lean.Lynth.Grind.AC
