import Lynth.Interval.Integral.Math.ComplexClean

/-! Resolve the real-axis branch step on each side of a real binder's zero.
Endpoint changes are on a null set; no recursive integral is erased. -/
namespace Intgrl
open Lynth.Interval.Integral.Nested

private def axisStep (n : Nat) (e : NExpr) : Bool :=
  e == CParts.negative (.var n) || e == CParts.negative (neg (.var n))

def hasAxisStep (n : Nat) (e : NExpr) : Bool :=
  axisStep n e || match e with
    | .unary _ a | .pow a _ | .rpow a _ => hasAxisStep n a
    | .binary _ a b => hasAxisStep n a || hasAxisStep n b
    | _ => false

def resolveAxisStep (n : Nat) (positive : Bool) (e : NExpr) : NExpr :=
  if e == CParts.negative (.var n) then .rat (if positive then 0 else -1)
  else if e == CParts.negative (neg (.var n)) then .rat (if positive then -1 else 0)
  else match e with
    | .unary op a => complexCleanUnary op (resolveAxisStep n positive a)
    | .binary op a b => complexCleanBinary op
        (resolveAxisStep n positive a) (resolveAxisStep n positive b)
    | .pow a m => complexCleanPow (resolveAxisStep n positive a) m
    | .rpow a q => rpow (resolveAxisStep n positive a) q
    | e => e

/-- On a subinterval of [0,1], log(x) is nonpositive; its branch step
is constant away from the null endpoints. -/
def resolveUnitLog (n : Nat) (e : NExpr) : NExpr :=
  let L := NExpr.unary .log (.var n)
  if e == .unary .sqrt L then .rat 0
  else if e == .unary .abs L then neg L
  else if e == CParts.negative L then .rat (-1)
  else if e == CParts.negative (neg L) then .rat 0
  else match e with
    | .unary op a => complexCleanUnary op (resolveUnitLog n a)
    | .binary op a b => complexCleanBinary op (resolveUnitLog n a) (resolveUnitLog n b)
    | .pow a m => complexCleanPow (resolveUnitLog n a) m
    | .rpow a q => rpow (resolveUnitLog n a) q
    | e => e

def complexBranchIntegral (n : Nat) (a b f : NExpr) : Option NExpr := do
  if f.hasIntegral then none else do
    let .rat p := a | none
    let .rat q := b | none
    if p ≥ q then none else do
      let F := if 0 ≤ p && q ≤ 1 then resolveUnitLog n f else f
      if !hasAxisStep n F then
        if F == f then none else some (.integral .interval a b F)
      else
        let left := resolveAxisStep n false F
        let right := resolveAxisStep n true F
        let left := if 0 ≤ p && q ≤ 1 then resolveUnitLog n left else left
        let right := if 0 ≤ p && q ≤ 1 then resolveUnitLog n right else right
        if q ≤ 0 then some (.integral .interval a b left)
        else if 0 ≤ p then some (.integral .interval a b right)
        else some (add (.integral .interval a (.rat 0) left)
          (.integral .interval (.rat 0) b right))
end Intgrl
