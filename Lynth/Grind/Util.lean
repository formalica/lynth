/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Simp.Simproc
public import Init.Simproc
import Lean.Meta.Tactic.Clear
import Lean.Meta.Sym.Util
public import Init.Grind.Config
import Init.Grind.Util
import Lean.Structure
open Lean.Meta
public section
namespace Lean.Lynth.Grind
/--
In the `lynth_grind` tactic, during `Expr` internalization, we don't expect to find `Expr.mdata`.
This function ensures `Expr.mdata` is not found during internalization.
Recall that we do not internalize `Expr.lam` children.
Recall that we still have to process `Expr.forallE` because of `ForallProp.lean`.
Moreover, we may not want to reduce `p → q` to `¬p ∨ q` when `(p q : Prop)`.
-/
def eraseIrrelevantMData (e : Expr) : CoreM Expr := do
  if Option.isNone <| e.find? fun e => e.isMData then return e
  let pre (e : Expr) := do
    match e with
    | .letE .. | .lam .. => return .done e
    | .mdata _ e => return .visit e
    | _ => return .continue e
  Core.transform e (pre := pre)

/--
Converts nested `Expr.proj`s into projection applications if possible.
-/
def foldProjs (e : Expr) : MetaM Expr :=
  Sym.foldProjs e

set_option compiler.ignoreBorrowAnnotation true in
/--
Normalizes the given expression using the `lynth_grind` simplification theorems and simprocs.
This function is used for normalizing E-matching patterns. Note that it does not return a proof.
-/
@[extern "lean_grind_normalize"] -- forward definition
opaque normalize (e : Expr) (config : Lean.Grind.Config) : MetaM Expr

/--
Returns `Lean.Grind.MatchCond e`.
We have special support for propagating is truth value.
See comment at `MatchCond.lean`.
-/
def markAsMatchCond (e : Expr) : Expr :=
  mkApp (mkConst ``Lean.Grind.MatchCond) e

def isMatchCond (e : Expr) : Bool :=
  e.isAppOfArity ``Lean.Grind.MatchCond 1

/--
Returns `Lean.Grind.PreMatchCond e`.
Recall that `Lean.Grind.PreMatchCond` is an identity function,
but the simproc `reducePreMatchCond` is used to prevent the term `e` from being simplified.
`Lean.Grind.PreMatchCond` is later converted into `Lean.Grind.MatchCond`.
See comment at `MatchCond.lean`.
-/
def markAsPreMatchCond(e : Expr) : Expr :=
  mkApp (mkConst ``Lean.Grind.PreMatchCond) e

def isPreMatchCond (e : Expr) : Bool :=
  e.isAppOfArity ``Lean.Grind.PreMatchCond 1

def reducePreMatchCond : Lean.Meta.Simp.DSimproc := fun e => do
  let_expr Lean.Grind.PreMatchCond _ ← e | return .continue
  return .done e

simproc_pattern% (Nat.succ _) => reducePreMatchCond
/-- Adds `reducePreMatchCond` to `s` -/
def addPreMatchCondSimproc (s : Simprocs) : CoreM Simprocs := do
  s.add ``reducePreMatchCond (post := false)

/--
Converts `Lean.Grind.PreMatchCond` into `Lean.Grind.MatchCond`.
Recall that `Lean.Grind.PreMatchCond` uses default reducibility setting, but
`Lean.Grind.MatchCond` does not.
-/
def replacePreMatchCond (e : Expr) : MetaM Simp.Result := do
  if e.find? isPreMatchCond |>.isNone then
    return { expr := e }
  else
    let pre (e : Expr) := do
      let_expr Lean.Grind.PreMatchCond p := e | return .continue e
      return .continue (markAsMatchCond p)
    let e' ← Core.transform e (pre := pre)
    return { expr := e', proof? := mkExpectedPropHint (← mkEqRefl e') (← mkEq e e') }

def isIte (e : Expr) :=
  e.isAppOf ``ite && e.getAppNumArgs >= 5

def isDIte (e : Expr) :=
  e.isAppOf ``dite && e.getAppNumArgs >= 5

def getBinOp (e : Expr) : Option Expr :=
  if !e.isApp then none else
  let f := e.appFn!
  if !f.isApp then none else
  some f.appFn!

end Lean.Lynth.Grind
