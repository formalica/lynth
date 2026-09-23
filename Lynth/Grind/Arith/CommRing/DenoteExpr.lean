/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.Arith.CommRing.Functions
open Lean.Meta
public section
namespace Lean.Lynth.Grind.Arith.CommRing
open Sym.Arith
/-!
Helper functions for converting reified terms back into their denotations.
-/

variable [Monad M] [MonadError M] [MonadLiftT MetaM M] [MonadCanon M] [MonadRing M]

def denoteNum (k : Int) : M Expr := do
  let ring ← getRing
  let n := mkRawNatLit k.natAbs
  let ofNatInst ← if let some inst ← synthInstance? (mkApp2 (mkConst ``OfNat [ring.u]) ring.type n) then
    pure inst
  else
    pure <| mkApp3 (mkConst ``Lean.Grind.Semiring.ofNat [ring.u]) ring.type ring.semiringInst n
  let n := mkApp3 (mkConst ``OfNat.ofNat [ring.u]) ring.type n ofNatInst
  if k < 0 then
    return mkApp (← getNegFn) n
  else
    return n

@[specialize]
private def denoteExprCore (getVar : Nat → Expr) (e : RingExpr) : M Expr := do
  go e
where
  go : RingExpr → M Expr
  | .num k => denoteNum k
  | .natCast k => return mkApp (← getNatCastFn) (mkNatLit k)
  | .intCast k => return mkApp (← getIntCastFn) (mkIntLit k)
  | .var x => return getVar x
  | .add a b => return mkApp2 (← getAddFn) (← go a) (← go b)
  | .sub a b => return mkApp2 (← getSubFn) (← go a) (← go b)
  | .mul a b => return mkApp2 (← getMulFn) (← go a) (← go b)
  | .pow a k => return mkApp2 (← getPowFn) (← go a) (toExpr k)
  | .neg a => return mkApp (← getNegFn) (← go a)

private def mkEq (a b : Expr) : M Expr := do
  let r ← getRing
  return mkApp3 (mkConst ``Eq [r.u.succ]) r.type a b

def powerDenoteExpr (pw : Power) : M Expr := do
  let x := (← getRing).vars[pw.x]!
  if pw.k == 1 then
    return x
  else
    return mkApp2 (← getPowFn) x (toExpr pw.k)

def monDenoteExpr (m : Mon) : M Expr := do
  match m with
  | .unit => denoteNum 1
  | .mult pw m => go m (← powerDenoteExpr pw)
where
  go (m : Mon) (acc : Expr) : M Expr := do
    match m with
    | .unit => return acc
    | .mult pw m => go m (mkApp2 (← getMulFn) acc (← powerDenoteExpr pw))

def polyDenoteExpr (p : Poly) : M Expr := do
  match p with
  | .num k => denoteNum k
  | .add k m p => go p (← denoteTerm k m)
where
  denoteTerm (k : Int) (m : Mon) : M Expr := do
    if k == 1 then
      monDenoteExpr m
    else
      return mkApp2 (← getMulFn) (← denoteNum k) (← monDenoteExpr m)
  go (p : Poly) (acc : Expr) : M Expr := do
    match p with
    | .num 0 => return acc
    | .num k => return mkApp2 (← getAddFn) acc (← denoteNum k)
    | .add k m p => go p (mkApp2 (← getAddFn) acc (← denoteTerm k m))

def ringDenoteExpr (e : RingExpr) : M Expr := do
  let ring ← getRing
  denoteExprCore (fun x => ring.vars[x]!) e

def ringDenoteExpr' (vars : Array Expr) (e : RingExpr) : M Expr := do
  denoteExprCore (fun x => vars[x]!) e


def EqCnstr.denoteExpr (c : EqCnstr) : M Expr := do
  mkEq (← polyDenoteExpr c.p) (← denoteNum 0)

def PolyDerivation.denoteExpr (d : PolyDerivation) : M Expr := do
  polyDenoteExpr d.p

def DiseqCnstr.denoteExpr (c : DiseqCnstr) : M Expr := do
  return mkNot (← mkEq (← c.d.denoteExpr) (← denoteNum 0))

end Lean.Lynth.Grind.Arith.CommRing
