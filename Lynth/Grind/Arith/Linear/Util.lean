/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.Arith.Linear.LinearM
import Lynth.Grind.Arith.Util
import Init.Data.Int.Gcd
import Lean.Meta.Tactic.Grind.Arith.Linear.Util
open Lean.Meta
public section
namespace Lean.Lynth.Grind.Arith.Linear

open Lean

def getZero : LinearM Expr :=
  return (← getStruct).zero

def getOne : LinearM Expr := do
  let some one := (← getStruct).one?
    | throwNotRing
  return one

def isCommRing : LinearM Bool :=
  return (← getStruct).ringId?.isSome

def isOrderedCommRing : LinearM Bool := do
  return (← isCommRing) && (← getStruct).orderedRingInst?.isSome

def isLinearOrder : LinearM Bool :=
  return (← getStruct).isLinearInst?.isSome

def hasNoNatZeroDivisors : LinearM Bool :=
  return (← getStruct).noNatDivInst?.isSome

def getTermStructId? (e : Expr) : GoalM (Option Nat) := do
  return (← get').exprToStructId.find? { expr := e }

def setTermStructId (e : Expr) : LinearM Unit := do
  let structId ← getStructId
  if let some structId' ← getTermStructId? e then
    unless structId' == structId do
      reportIssue! "expression in two different structure in linarith module{indentExpr e}"
    return ()
  modify' fun s => { s with
    exprToStructId := s.exprToStructId.insert { expr := e } structId
    exprToStructIdEntries := s.exprToStructIdEntries.push (e, structId)
  }

def getNoNatDivInst : LinearM Expr := do
  let some inst := (← getStruct).noNatDivInst?
    | throwError "`lynth_grind linarith` internal error, structure does not implement `NoNatZeroDivisors`"
  return inst

def getLEInst : LinearM Expr := do
  let some inst := (← getStruct).leInst?
    | throwError "`lynth_grind linarith` internal error, structure does not support LE"
  return inst

def getLTInst : LinearM Expr := do
  let some inst := (← getStruct).ltInst?
    | throwError "`lynth_grind linarith` internal error, structure does not support LT"
  return inst

def getLawfulOrderLTInst : LinearM Expr := do
  let some inst := (← getStruct).lawfulOrderLTInst?
    | throwError "`lynth_grind linarith` internal error, structure does not have a lawful LT instance"
  return inst

def getIsPreorderInst : LinearM Expr := do
  let some inst := (← getStruct).isPreorderInst?
    | throwError "`lynth_grind linarith` internal error, structure is not a preorder"
  return inst

def getOrderedAddInst : LinearM Expr := do
  let some inst := (← getStruct).orderedAddInst?
    | throwError "`lynth_grind linarith` internal error, structure is not an ordered module"
  return inst

def isOrderedAdd : LinearM Bool :=
  return (← getStruct).orderedAddInst?.isSome

def getLtFn [Monad m] [MonadError m] [MonadGetStruct m] : m Expr := do
  let some lt := (← getStruct).ltFn?
    | throwError "`lynth_grind linarith` internal error, structure is not an ordered module"
  return lt

def getLeFn [Monad m] [MonadError m] [MonadGetStruct m] : m Expr := do
  let some le := (← getStruct).leFn?
    | throwError "`lynth_grind linarith` internal error, structure is not an ordered int module"
  return le

def getIsLinearOrderInst : LinearM Expr := do
  let some inst := (← getStruct).isLinearInst?
    | throwError "`lynth_grind linarith` internal error, structure is not a linear order"
  return inst

def getRingInst : LinearM Expr := do
  let some inst := (← getStruct).ringInst?
    | throwError "`lynth_grind linarith` internal error, structure is not a ring"
  return inst

def getCommRingInst : LinearM Expr := do
  let some inst := (← getStruct).commRingInst?
    | throwError "`lynth_grind linarith` internal error, structure is not a commutative ring"
  return inst

def getOrderedRingInst : LinearM Expr := do
  let some inst := (← getStruct).orderedRingInst?
    | throwError "`lynth_grind linarith` internal error, structure is not an ordered ring"
  return inst

/--
Returns `.true` if `c` is satisfied by the current partial model,
`.undef` if `c` contains unassigned variables, and `.false` otherwise.
-/

def evalPoly? (p : Poly) : LinearM (Option Rat) := do
  let a := (← getStruct).assignment
  let rec go (v : Rat) : Poly → Option Rat
    | .nil => some v
    | .add k x p =>
      if _ : x < a.size then
        go (v + k*a[x]) p
      else
        none
  return go 0 p

def IneqCnstr.satisfied (c : IneqCnstr) : LinearM LBool := do
  let some v ← evalPoly? c.p | return .undef
  if c.strict then
    return decide (v < 0) |>.toLBool
  else
    return decide (v <= 0) |>.toLBool

def DiseqCnstr.satisfied (c : DiseqCnstr) : LinearM LBool := do
  let some v ← evalPoly? c.p | return .undef
  return decide (v != 0) |>.toLBool

/-- Resets the assignment of any variable bigger or equal to `x`. -/
def resetAssignmentFrom (x : Var) : LinearM Unit := do
  modifyStruct fun s => { s with assignment := shrink s.assignment x }

def getVar (x : Var) : LinearM Expr :=
  return (← getStruct).vars[x]!

/-- Returns `true` if the linarith state is inconsistent. -/

def inconsistent : LinearM Bool := do
  if (← isInconsistent) then return true
  return (← getStruct).conflict?.isSome

/-- Returns `true` if `x` has been eliminated using an equality constraint. -/
def eliminated (x : Var) : LinearM Bool :=
  return (← getStruct).elimEqs[x]!.isSome

/-- Returns occurrences of `x`. -/
def getOccursOf (x : Var) : LinearM VarSet :=
  return (← getStruct).occurs[x]!

/--
Adds `y` as an occurrence of `x`.
That is, `x` occurs in `lowers[y]`, `uppers[y]`, or `diseqs[y]`.
-/
def addOcc (x : Var) (y : Var) : LinearM Unit := do
  unless (← getOccursOf x).contains y do
    modifyStruct fun s => { s with occurs := s.occurs.modify x fun ys => ys.insert y }

/-- Explicit polynomial helpers over `Lean.Grind.Linarith.Poly`.
Core defines these as dot-notation extensions in the type's own
namespace; we cannot reuse those names (core owns them and is loaded
in every Mathlib session), so they live here under explicit names
with identical bodies, operating on our `LinearM` state. -/
partial def updateOccsPoly (p : Poly) : LinearM Unit := do
  let .add _ y p := p | throwError "`lynth_grind linarith` internal error, unexpected constant polynomial"
  let rec go (p : Poly) : LinearM Unit := do
    let .add _ x p := p | return ()
    addOcc x y; go p
  go p

/--
Given a polynomial `p`, returns `some (x, k, c)` if `p` contains the monomial `k*x`,
and `x` has been eliminated using the equality `c`.
-/
def findVarToSubstPoly (p : Poly) : LinearM (Option (Int × Var × EqCnstr)) := do
  match p with
  | .nil => return none
  | .add k x p =>
    if let some c := (← getStruct).elimEqs[x]! then
      return some (k, x, c)
    else
      findVarToSubstPoly p

def checkOccsPoly (p : Poly) : LinearM Unit := do
  let .add _ y p := p | return ()
  let rec go (p : Poly) : LinearM Unit := do
    let .add _ x p := p | return ()
    assert! (← getOccursOf x).contains y
    go p
  go p

def checkNoElimVarsPoly (p : Poly) : LinearM Unit := do
  let .add _ x p := p | return ()
  assert! !(← eliminated x)
  checkNoElimVarsPoly p


/-- Explicit sortedness/coefficient checks over `Lean.Grind.Linarith.Poly`.
Core defines these as dot-notation extensions in the type's own namespace
(which is private to core's module); they live here under explicit names
with identical bodies. -/
def isSortedPoly (p : Poly) : Bool :=
  go none p
where
  go : Option Var → Poly → Bool
  | _,      .nil       => true
  | none,   .add _ y p => go (some y) p
  | some x, .add _ y p => x > y && go (some y) p

/-- Returns `true` if all coefficients are not `0`. -/
def checkCoeffsPoly : Poly → Bool
  | .nil => true
  | .add k _ p => k != 0 && checkCoeffsPoly p

def checkCnstrOfPoly (p : Poly) (x : Var) : LinearM Unit := do
  assert! isSortedPoly p
  assert! checkCoeffsPoly p
  unless (← inconsistent) do
    checkNoElimVarsPoly p
    checkOccsPoly p
    pure ()
  let .add _ y _ := p | unreachable!
  assert! x == y

end Lean.Lynth.Grind.Arith.Linear
