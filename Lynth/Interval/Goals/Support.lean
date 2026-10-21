import Lynth.Interval.Integral.Reify
import Lynth.Interval.Series.Cert

/-! Structural tail support and rounding-sensitive boundaries, shared by the
ordinary and compositional series handlers. -/
namespace Lynth.Interval.Goals
open Lean Meta Elab Tactic Qq Integral

private def headName : Lean.Expr → Name
  | .const name _ => name
  | _ => .anonymous

/-- A tail with one of the supported summable shapes may become usable after
rounding improves. Constant, growing and unknown models need a different rule. -/
def summableShape : RAsy → Bool
  | .geo .. => true
  | .pow _ exponent .. => exponent < -1
  | _ => false

/-- A closed coefficient can round across a geometric-ratio or exponential
sign boundary. Such a missing tail model is numerical, unlike an operation
for which no asymptotic rule exists. Parameter boxes do not shrink with precision. -/
partial def tailNeedsPrecision (t index : Lean.Expr) (prec : Nat)
    (fuel : Nat := 16) : TacticM Bool := do
  if fuel == 0 then return false
  let t := t.headBeta
  let head := t.getAppFn
  let args := t.getAppArgs
  let straddles (I : Ival) (v : Dy) := match I.lo,I.hi with
    | some l,some u => Dy.ltB l u && Dy.leB l v && Dy.leB v u
    | _,_ => false
  if head.isConstOf ``HPow.hPow && args.size ≥ 2 then
    let base := args[args.size-2]!
    let exponent := args.back!
    unless (← whnfR (← inferType exponent)).isConstOf ``Nat do return false
    if !exponent.containsFVar index.fvarId! then
      return ← tailNeedsPrecision base index prec (fuel-1)
    unless !base.hasFVar && !base.hasMVar do return false
    try
      let r ← Reify.reify {} base
      unless r.ty == .real do return false
      let e ← evalExprVal .real r.expr
      return straddles (Ival.abs (e.eval (Ctx.make prec) {})) Dy.one
    catch ex =>
      if ex.isInterrupt then throw ex
      return false
  if head.isConstOf ``Real.exp && !args.isEmpty then
    let arg := args.back!
    if (arg.find? fun e => e.isFVar && e != index).isSome then return false
    try
      let r ← Reify.reify (({} : Reify.RCtx).push index .nat) arg
      let e ← evalExprVal .real r.expr
      match e.asy (Ctx.make prec) 8 with
      | .pow _ exponent I _ => return exponent == 1 && straddles I Dy.zero
      | _ => return false
    catch ex =>
      if ex.isInterrupt then throw ex
      return false
  if let some op := unaryHead? (headName head) then
    if op == .neg || op == .inv || op == .abs then
      return ← tailNeedsPrecision args.back! index prec (fuel-1)
  if let some op := binaryHead? (headName head) then
    if op == .add || op == .sub || op == .mul || op == .div then
      return (← tailNeedsPrecision args[args.size-2]! index prec (fuel-1)) ||
        (← tailNeedsPrecision args.back! index prec (fuel-1))
  if let some value ← Reify.unfoldHead? t then
    if value != t then return ← tailNeedsPrecision value index prec (fuel-1)
  return false

end Lynth.Interval.Goals
