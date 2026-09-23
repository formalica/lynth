/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Simp.Simproc
import Init.Grind.Util
import Init.Simproc
import Lean.Meta.Tactic.Simp.Rewrite
open Lean.Meta
public section
namespace Lean.Lynth.Grind
/--
Returns `Lean.Grind.simpMatchDiscrsOnly e`. Recall that `Lean.Grind.simpMatchDiscrsOnly` is
a gadget for instructing the `lynth_grind` simplifier to only normalize/simplify
the discriminants of a `match`-expression. See `reduceSimpMatchDiscrsOnly`.
-/
def markAsSimpMatchDiscrsOnly (e : Expr) : MetaM Expr :=
  mkAppM ``Lean.Grind.simpMatchDiscrsOnly #[e]

def isSimpMatchDiscrsOnly (e : Expr) :=
  e.isAppOfArity ``Lean.Grind.simpMatchDiscrsOnly 2

def reduceSimpMatchDiscrsOnly : Lean.Meta.Simp.Simproc := fun e => do
  let_expr Lean.Grind.simpMatchDiscrsOnly _ m ← e | return .continue
  let .const declName _ := m.getAppFn
    | return .done { expr := e }
  let some info ← getMatcherInfo? declName
    | return .done { expr := e }
  if let some r ← Simp.simpMatchDiscrs? info m then
    return .done { r with expr := (← markAsSimpMatchDiscrsOnly r.expr) }
  return .done { expr := e }

simproc_pattern% (Lean.Grind.simpMatchDiscrsOnly _) => reduceSimpMatchDiscrsOnly
/-- Adds `reduceSimpMatchDiscrsOnly` to `s` -/

def addSimpMatchDiscrsOnly (s : Simprocs) : CoreM Simprocs := do
  s.add ``reduceSimpMatchDiscrsOnly (post := false)

/-- Erases `Lean.Grind.simpMatchDiscrsOnly` annotations. -/
def eraseSimpMatchDiscrsOnly (e : Expr) : MetaM Simp.Result := do
  if e.find? isSimpMatchDiscrsOnly |>.isNone then
    return { expr := e }
  else
    let pre (e : Expr) := do
      let_expr Lean.Grind.simpMatchDiscrsOnly _ a := e | return .continue e
      return .continue a
    let e' ← Core.transform e (pre := pre)
    /-
    `lynth_grind` uses the `.reducible` transparency setting, and `Lean.Grind.simpMatchDiscrsOnly` is not
    reducible. Thus, `e` and `e'` are not definitionally equal in this setting, and we must
    add a hint.
    -/
    return { expr := e', proof? := mkExpectedPropHint (← mkEqRefl e') (← mkEq e e') }

end Lean.Lynth.Grind
