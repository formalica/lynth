/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.Arith.Cutsat.Types
import Lean.Meta.Tactic.Simp.Arith.Int.Simp
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
open Lean.Meta
public section

namespace Lean.Lynth.Grind.Arith.Cutsat

open Lean

def get' : GoalM State := do
  cutsatExt.getState

@[inline] def modify' (f : State → State) : GoalM Unit := do
  cutsatExt.modifyState f

/-- Returns `true` if the cutsat state is inconsistent. -/
def inconsistent : GoalM Bool := do
  if (← isInconsistent) then return true
  return (← get').conflict?.isSome

set_option compiler.ignoreBorrowAnnotation true in
/-- Creates a new variable in the cutsat module. -/
@[extern "lean_grind_cutsat_mk_var"] -- forward definition
opaque mkVar (e : Expr) : GoalM Var

def getVars : GoalM (PArray Expr) :=
  return (← get').vars

def getVar (x : Var) : GoalM Expr :=
  return (← get').vars[x]!


def ppPoly (p : Poly) : GoalM MessageData := do
  match p with
  | .num k => return m!"{k}"
  | .add 1 x p => go (quoteIfArithTerm (← getVar x)) p
  | .add k x p => go m!"{k}*{quoteIfArithTerm (← getVar x)}" p
where
  go (r : MessageData)  (p : Int.Internal.Linear.Poly) : GoalM MessageData := do
    match p with
    | .num 0 => return r
    | .num k => return m!"{r} + {k}"
    | .add 1 x p => go m!"{r} + {quoteIfArithTerm (← getVar x)}" p
    | .add k x p => go m!"{r} + {k}*{quoteIfArithTerm (← getVar x)}" p

def denoteExprPoly (p : Poly) : GoalM Expr := do
  let vars ← getVars
  return (← p.denoteExpr (vars[·]!))

def evalPoly? (p : Poly) : GoalM (Option Rat) := do
  let a := (← get').assignment
  let rec go (v : Rat) : Poly → Option Rat
    | .num k => some (v + k)
    | .add k x p =>
      if _ : x < a.size then
        go (v + k*a[x]) p
      else
        none
  return go 0 p

def satisfiedLePoly (p : Poly) : GoalM LBool := do
  let some v ← evalPoly? p | return .undef
  return decide (v <= 0) |>.toLBool

def findVarToSubstPoly (p : Poly) : GoalM (Option (Int × Var × EqCnstr)) := do
  match p with
  | .num _ => return none
  | .add k x p =>
    if let some c := (← get').elimEqs[x]! then
      return some (k, x, c)
    else
      findVarToSubstPoly p

/-- Returns `true` if `e` is already associated with a cutsat variable. -/
def hasVar (e : Expr) : GoalM Bool :=
  return (← get').varMap.contains { expr := e }

def isIntTerm (e : Expr) : GoalM Bool :=
  hasVar e

/-- Returns `true` if `x` has been eliminated using an equality constraint. -/
def eliminated (x : Var) : GoalM Bool :=
  return (← get').elimEqs[x]!.isSome

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_grind_cutsat_assert_eq"] -- forward definition
opaque EqCnstr.assert (c : EqCnstr) : GoalM Unit

/-- Resets the assignment of any variable bigger or equal to `x`. -/
def resetAssignmentFrom (x : Var) : GoalM Unit := do
  modify' fun s => { s with assignment := shrink s.assignment x }

def DvdCnstr.isTrivial (c : DvdCnstr) : Bool :=
  match c.p with
  | .num k' => k' % c.d == 0
  | _ => c.d == 1

def DvdCnstr.pp (c : DvdCnstr) : GoalM MessageData := do
  return m!"{c.d} ∣ {← ppPoly c.p}"

def DvdCnstr.denoteExpr (c : DvdCnstr) : GoalM Expr := do
  return mkIntDvd (toExpr c.d) (← denoteExprPoly c.p)

def DvdCnstr.throwUnexpected (c : DvdCnstr) : GoalM α := do
  throwError "`lynth_grind` internal error, unexpected{indentD (← c.pp)} "

def DiseqCnstr.isTrivial (c : DiseqCnstr) : Bool :=
  match c.p with
  | .num k => k != 0
  | _ => c.p.getConst % c.p.gcdCoeffs' != 0

def DiseqCnstr.pp (c : DiseqCnstr) : GoalM MessageData := do
  return m!"{← ppPoly c.p} ≠ 0"

def DiseqCnstr.throwUnexpected (c : DiseqCnstr) : GoalM α := do
  throwError "`lynth_grind` internal error, unexpected{indentD (← c.pp)}"

def DiseqCnstr.denoteExpr (c : DiseqCnstr) : GoalM Expr := do
  return mkNot (mkIntEq (← denoteExprPoly c.p) (mkIntLit 0))

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_grind_cutsat_assert_le"] -- forward definition
opaque LeCnstr.assert (c : LeCnstr) : GoalM Unit

def LeCnstr.isTrivial (c : LeCnstr) : Bool :=
  match c.p with
  | .num k => k ≤ 0
  | _ => false

def LeCnstr.pp (c : LeCnstr) : GoalM MessageData := do
  return m!"{← ppPoly c.p} ≤ 0"

def LeCnstr.denoteExpr (c : LeCnstr) : GoalM Expr := do
  return mkIntLE (← denoteExprPoly c.p) (mkIntLit 0)

def LeCnstr.throwUnexpected (c : LeCnstr) : GoalM α := do
  throwError "`lynth_grind` internal error, unexpected{indentD (← c.pp)}"

def EqCnstr.isTrivial (c : EqCnstr) : Bool :=
  match c.p with
  | .num k => k == 0
  | _ => false

def EqCnstr.pp (c : EqCnstr) : GoalM MessageData := do
  return m!"{← ppPoly c.p} = 0"

def EqCnstr.denoteExpr (c : EqCnstr) : GoalM Expr := do
  return mkIntEq (← denoteExprPoly c.p) (mkIntLit 0)

def EqCnstr.throwUnexpected (c : EqCnstr) : GoalM α := do
  throwError "`lynth_grind` internal error, unexpected{indentD (← c.pp)}"

/-- Returns occurrences of `x`. -/
def getOccursOf (x : Var) : GoalM VarSet :=
  return (← get').occurs[x]!

/--
Adds `y` as an occurrence of `x`.
That is, `x` occurs in `lowers[y]`, `uppers[y]`, or `dvdCnstrs[y]`.
-/
def addOcc (x : Var) (y : Var) : GoalM Unit := do
  unless (← getOccursOf x).contains y do
    modify' fun s => { s with occurs := s.occurs.modify x fun ys => ys.insert y }

/-- Explicit polynomial helpers over `Int.Internal.Linear.Poly`.
Core defines these as dot-notation extensions in the type's own
namespace; we cannot reuse those names (core owns them and is loaded
in every Mathlib session), so they live here under explicit names
with identical bodies, operating on our `GoalM` state. -/
partial def updateOccsPoly (p : Poly) : GoalM Unit := do
  let .add _ y p := p | throwError "`lynth_grind` internal error, unexpected constant polynomial"
  let rec go (p : Poly) : GoalM Unit := do
    let .add _ x p := p | return ()
    addOcc x y; go p
  go p

/--
Given a polynomial `p`, returns `some (x, k, c)` if `p` contains the monomial `k*x`,
and `x` has been eliminated using the equality `c`.
-/
partial def updateOccsForElimEqPoly (p : Poly) (x : Var) : GoalM Unit := do
  let rec go (p : Poly) : GoalM Unit := do
    let .add _ y p := p | return ()
    unless x == y do addOcc y x
    go p
  go p

/-- Returns `true` if all coefficients are not `0`. -/
def checkCoeffsPoly : Poly → Bool
  | .num _ => true
  | .add k _ p => k != 0 && checkCoeffsPoly p

def checkNoElimVarsPoly (p : Poly) : GoalM Unit := do
  let .add _ x p := p | return ()
  assert! !(← eliminated x)
  checkNoElimVarsPoly p

def checkOccsPoly (p : Poly) : GoalM Unit := do
  let .add _ y p := p | return ()
  let rec go (p : Poly) : GoalM Unit := do
    let .add _ x p := p | return ()
    assert! (← getOccursOf x).contains y
    go p
  go p

def checkCnstrOfPoly (p : Poly) (x : Var) : GoalM Unit := do
  assert! p.isSorted
  assert! checkCoeffsPoly p
  unless (← inconsistent) do
    checkNoElimVarsPoly p
    checkOccsPoly p
  let .add _ y _ := p | unreachable!
  assert! x == y
/--
Tries to evaluate the polynomial `p` using the partial model/assignment built so far.
The result is `none` if the polynomial contains variables that have not been assigned.
-/
abbrev LeCnstr.isUnsat (c : LeCnstr) : Bool :=
  c.p.isUnsatLe

abbrev DvdCnstr.isUnsat (c : DvdCnstr) : Bool :=
  c.p.isUnsatDvd c.d

/--
Returns `.true` if `c` is satisfied by the current partial model,
`.undef` if `c` contains unassigned variables, and `.false` otherwise.
-/
def DvdCnstr.satisfied (c : DvdCnstr) : GoalM LBool := do
  let some v ← evalPoly? c.p | return .undef
  if v.den != 1 then return .false
  return decide (c.d ∣ v.num) |>.toLBool

/--
Returns `.true` if `c` is satisfied by the current partial model,
`.undef` if `c` contains unassigned variables, and `.false` otherwise.
-/
def LeCnstr.satisfied (c : LeCnstr) : GoalM LBool := do
  satisfiedLePoly c.p

/--
Returns `.true` if `c` is satisfied by the current partial model,
`.undef` if `c` contains unassigned variables, and `.false` otherwise.
-/
def DiseqCnstr.satisfied (c : DiseqCnstr) : GoalM LBool := do
  let some v ← evalPoly? c.p | return .undef
  return v != 0 |>.toLBool

/--
Returns `.true` if `c` is satisfied by the current partial model,
`.undef` if `c` contains unassigned variables, and `.false` otherwise.
-/
def EqCnstr.satisfied (c : EqCnstr) : GoalM LBool := do
  let some v ← evalPoly? c.p | return .undef
  return v == 0 |>.toLBool

/--
Given a polynomial `p`, returns `some (x, k, c)` if `p` contains the monomial `k*x`,
and `x` has been eliminated using the equality `c`.
-/
def CooperSplitPred.numCases (pred : CooperSplitPred) : Nat :=
  let a  := pred.c₁.p.leadCoeff
  let b  := pred.c₂.p.leadCoeff
  match pred.c₃? with
  | none => if pred.left then a.natAbs else b.natAbs
  | some c₃ =>
    let c  := c₃.p.leadCoeff
    let d  := c₃.d
    if pred.left then
      Int.lcm a (a * d / Int.gcd (a * d) c)
    else
      Int.lcm b (b * d / Int.gcd (b * d) c)

def CooperSplitPred.pp (pred : CooperSplitPred) : GoalM MessageData := do
  return m!"{← pred.c₁.pp}, {← pred.c₂.pp}, {← if let some c₃ := pred.c₃? then c₃.pp else pure "none"}"

def UnsatProof.pp (h : UnsatProof) : GoalM MessageData := do
  match h with
  | .le c | .eq c | .dvd c | .diseq c => c.pp
  | .cooper c₁ c₂ c₃ => return m!"{← c₁.pp}, {← c₂.pp}, {← c₃.pp}"

end Lean.Lynth.Grind.Arith.Cutsat
