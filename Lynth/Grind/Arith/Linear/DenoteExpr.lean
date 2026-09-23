/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Lynth.Grind.Arith.Util
public import Lynth.Grind.Arith.Linear.Util
import Lynth.Grind.Simp
import Lynth.Grind.Arith.CommRing.DenoteExpr
open Lean.Meta
public section
namespace Lean.Lynth.Grind.Arith.Linear
/-!
Helper functions for converting reified terms back into their denotations.
-/
variable [Monad M] [MonadGetStruct M] [MonadError M]

private def mkEq (a b : Expr) : M Expr := do
  let s ← getStruct
  return mkApp3 (mkConst ``Eq [s.u.succ]) s.type a b

def DiseqCnstr.denoteExpr (c : DiseqCnstr) : M Expr := do
  return mkNot (← mkEq (← c.p.denoteExpr) (← getStruct).ofNatZero)

private def denoteIneq (p : Poly) (strict : Bool) : M Expr := do
  if strict then
    return mkApp2 (← getLtFn) (← p.denoteExpr) (← getStruct).ofNatZero
  else
    return mkApp2 (← getLeFn) (← p.denoteExpr) (← getStruct).ofNatZero

def IneqCnstr.denoteExpr (c : IneqCnstr) : M Expr := do
  denoteIneq c.p c.strict

def EqCnstr.denoteExpr (c : EqCnstr) : M Expr := do
  mkEq (← c.p.denoteExpr) (← getStruct).ofNatZero

private def denoteNum (k : Int) : LinearM Expr := do
  return mkApp2 (← getStruct).zsmulFn (mkIntLit k) (← getOne)

end Lean.Lynth.Grind.Arith.Linear
