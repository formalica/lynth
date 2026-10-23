module

public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Lynth.Interval.Integral.Math.ComplexIntegral
public import Lynth.Interval.Integral.Math.Integrand
public import Lynth.Interval.Integral.Math.NestedDefs
public import Lynth.Interval.Integral.Math.NestedSyntax
import all Lynth.Interval.Integral.Math.ComplexIntegral

/-! Real algebraic identities for principal complex projections. -/
namespace Intgrl
open Lynth.Interval.Integral.Nested

@[expose] public def complexCleanUnary (op : Unary) (a : NExpr) : NExpr :=
  if op == .sqrt then
    match a with
    | .pow a 2 => .unary .abs a
    | .binary .div (.binary .add (.unary .abs a) b) (.rat 2) =>
        if a == b then CParts.un .sqrt a else CParts.un op (.binary .div
          (.binary .add (.unary .abs a) b) (.rat 2))
    | .binary .div (.binary .sub (.unary .abs a) b) (.rat 2) =>
        if a == b then CParts.un .sqrt (neg a) else CParts.un op (.binary .div
          (.binary .sub (.unary .abs a) b) (.rat 2))
    | .rat q => if q ≤ 0 then .rat 0 else CParts.un op a
    | _ => CParts.un op a
  else CParts.un op a

@[expose] public def complexCleanBinary (op : Binary) (a b : NExpr) : NExpr :=
  match op,a,b with
  | .add,a,.unary .neg b => sub a b
  | .add,.unary .neg a,b => sub b a
  | .sub,a,.unary .neg b => add a b
  | .add,a,.binary .sub b c =>
      if a == c && !a.hasIntegral then b else simplify (.binary .add a (.binary .sub b c))
  | .add,.binary .sub a b,c =>
      if b == c && !b.hasIntegral then a else simplify (.binary .add (.binary .sub a b) c)
  | .div,a,.rat 0 => if !a.hasIntegral then .rat 0 else .binary .div a b
  | .div,.rat 0,b => if !b.hasIntegral then .rat 0 else .binary .div a b
  | _,_,_ => simplify (.binary op a b)

@[expose] public def complexCleanPow (a : NExpr) (n : Nat) : NExpr :=
  match a with
  | .rat q => .rat (q^n)
  | _ => pow a n

def NExpr.complexClean : NExpr → NExpr
  | .unary op a => complexCleanUnary op a.complexClean
  | .binary op a b => complexCleanBinary op a.complexClean b.complexClean
  | .pow a n => complexCleanPow a.complexClean n
  | .rpow a q => rpow a.complexClean q
  | .integral k a b f => .integral k a.complexClean b.complexClean f.complexClean
  | e => e
end Intgrl
