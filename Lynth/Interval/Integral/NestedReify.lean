module

meta import all Lynth.Interval.Integral.NestedSearch
import all Lynth.Interval.Integral.NestedSearch
meta import all Lynth.Interval.Integral.Reify
import all Lynth.Interval.Integral.Reify

/-! Proof-producing binder-aware compilation. Each bound is compiled before
entering its binder. Shadowing uses free-variable identities, not names. -/
meta section

namespace Lynth.Interval.Integral.Nested
open Lean Meta Elab Tactic Intgrl Qq

def quoteDomain (k : NDomain) : Lean.Expr := mkConst (match k with
  | .interval => ``NDomain.interval | .icc => ``NDomain.icc | .ioc => ``NDomain.ioc
  | .ico => ``NDomain.ico | .ioo => ``NDomain.ioo | .right => ``NDomain.right
  | .left => ``NDomain.left | .whole => ``NDomain.whole)

def quoteExpr : Expr → Lean.Expr
  | .var i => mkApp (mkConst ``NExpr.var) (toExpr i)
  | .rat q => mkApp (mkConst ``NExpr.rat) (toExpr q)
  | .pi => mkConst ``NExpr.pi
  | .unary op a => mkApp2 (mkConst ``NExpr.unary) (quoteUnary op) (quoteExpr a)
  | .binary op a b => mkApp3 (mkConst ``NExpr.binary) (quoteBinary op) (quoteExpr a) (quoteExpr b)
  | .pow a n => mkApp2 (mkConst ``NExpr.pow) (quoteExpr a) (toExpr n)
  | .rpow a q => mkApp2 (mkConst ``NExpr.rpow) (quoteExpr a) (toExpr q)
  | .integral k a b f => mkApp4 (mkConst ``NExpr.integral)
      (quoteDomain k) (quoteExpr a) (quoteExpr b) (quoteExpr f)

def arrayExpr (type : Lean.Expr) (xs : Array Lean.Expr) : Lean.Expr :=
  mkApp2 (mkConst ``Array.mk [0]) type (quoteList type xs.toList)

def quoteChange : Change → Lean.Expr
  | .identity => mkConst ``Change.identity | .affine => mkConst ``Change.affine
  | .right => mkConst ``Change.right | .left => mkConst ``Change.left
  | .power m right => mkApp2 (mkConst ``Change.power) (toExpr m) (toExpr right)

def quotePlan (p : Plan) : Lean.Expr := mkAppN (mkConst ``Plan.mk)
  #[quoteChange p.change,quoteDy p.a,quoteDy p.b,toExpr p.reverse,quoteDy p.left,
    quoteDy p.right,toExpr p.decay,quoteList (mkConst ``Piece) (p.pieces.map quotePiece)]

def quoteEntry (e : Entry) : Lean.Expr := mkApp3 (mkConst ``Entry.mk) (quoteExpr e.expr)
  (arrayExpr (mkConst ``Ival) (e.env.map quoteIval)) (match e.method with
    | .split => mkConst ``EntryMethod.split
    | .panels p => mkApp (mkConst ``EntryMethod.panels) (quotePlan p))

def quoteCert (cert : Cert) : Lean.Expr := mkApp2 (mkConst ``Cert.mk)
  (arrayExpr (mkConst ``NodeTable) (cert.tables.map quoteTable))
  (arrayExpr (mkConst ``Entry) (cert.entries.map quoteEntry))

structure Request where
  kind : NDomain
  f : Lean.Expr
  a : Lean.Expr
  b : Lean.Expr
  closed : Bool := false

def zeroR : Lean.Expr := q((0 : ℝ))

def parseDomain (s : Lean.Expr) : MetaM (Option (NDomain × Lean.Expr × Lean.Expr × Bool)) := do
  let s ← instantiateMVars s
  let head := s.getAppFn
  let args := s.getAppArgs
  if head.isConstOf ``Set.univ then return some (.whole,zeroR,zeroR,false)
  if args.isEmpty then return none
  if head.isConstOf ``Set.Ioi then return some (.right,args.back!,zeroR,false)
  if head.isConstOf ``Set.Ici then return some (.right,args.back!,zeroR,true)
  if head.isConstOf ``Set.Iio then return some (.left,args.back!,zeroR,false)
  if head.isConstOf ``Set.Iic then return some (.left,args.back!,zeroR,true)
  if args.size < 2 then return none
  let a := args[args.size-2]!
  let b := args.back!
  if head.isConstOf ``Set.Icc then return some (.icc,a,b,false)
  if head.isConstOf ``Set.Ioc then return some (.ioc,a,b,false)
  if head.isConstOf ``Set.Ico then return some (.ico,a,b,false)
  if head.isConstOf ``Set.Ioo then return some (.ioo,a,b,false)
  return none

def parse (t : Lean.Expr) : MetaM (Option Request) := do
  let args := t.getAppArgs
  if t.getAppFn.isConstOf ``intervalIntegral && args.size ≥ 4 then
    unless ← isDefEq args.back! q(MeasureTheory.volume : MeasureTheory.Measure ℝ) do return none
    return some ⟨.interval,args[args.size-4]!,args[args.size-3]!,args[args.size-2]!,false⟩
  if t.getAppFn.isConstOf ``MeasureTheory.integral && args.size ≥ 2 then
    let μ := args[args.size-2]!
    let f := args.back!
    if μ.getAppFn.isConstOf ``MeasureTheory.Measure.restrict then
      let ma := μ.getAppArgs
      unless ← isDefEq ma[ma.size-2]! q(MeasureTheory.volume : MeasureTheory.Measure ℝ) do return none
      if let some (k,a,b,closed) ← parseDomain ma.back! then return some ⟨k,f,a,b,closed⟩
    else if ← isDefEq μ q(MeasureTheory.volume : MeasureTheory.Measure ℝ) then
      return some ⟨.whole,f,zeroR,zeroR,false⟩
  return none

structure Compiled where
  term : Expr
  proof : Lean.Expr

def realAt (e : Expr) (env : Array Lean.Expr) : Lean.Expr :=
  mkApp2 (mkConst ``NExpr.real) (quoteExpr e) (quoteList (mkConst ``Real) env.toList)

partial def compile (env : Array Lean.Expr) (t : Lean.Expr) (fuel := 256) : MetaM Compiled := do
  if fuel == 0 then throwError "nested integration: expression is too deep"
  let t := (← instantiateMVars t).headBeta
  if let some i := env.findIdx? (· == t) then return ⟨.var i, ← mkEqRefl t⟩
  if t.isConstOf ``Real.pi then return ⟨.pi,← mkEqRefl t⟩
  if !t.hasFVar && !t.hasMVar && !Reify.isTranscendentalHead t then
    if let some r ← Reify.exact? .real t ({} : Reify.RCtx).senv then
      if let some q ← Reify.ratValue? (α := q(ℝ)) t then return ⟨.rat q,r.proof⟩
  if let some req ← parse t then
    let a ← compile env req.a (fuel-1)
    let b ← compile env req.b (fuel-1)
    let f ← withLocalDeclD `x (mkConst ``Real) fun x => do
      let r ← compile (env.push x) (mkApp req.f x).headBeta (fuel-1)
      return (r.term, ← mkLambdaFVars #[x] r.proof)
    let result : Expr := .integral req.kind a.term b.term f.1
    let p ← mkAppM ``NDomain.value_congr #[quoteDomain req.kind,f.2,a.proof,b.proof]
    if req.closed then
      let eq' ← mkAppM (if req.kind == .right then ``NDomain.right_closed else
        ``NDomain.left_closed) #[req.f,req.a]
      return ⟨result, ← mkEqTrans eq' p⟩
    return ⟨result,p⟩
  let .const head _ := t.getAppFn | throwError "nested integration: unsupported {t}"
  let args := t.getAppArgs
  if head == ``Real.tan && args.size == 1 then
    let a ← compile env args[0]! (fuel-1)
    let p ← mkAppM ``congrArg #[mkConst ``Real.tan,a.proof]
    return ⟨.binary .div (.unary .sin a.term) (.unary .cos a.term),
      ← mkEqTrans p (mkApp (mkConst ``Real.tan_eq_sin_div_cos) (realAt a.term env))⟩
  if let some op := unaryHead? head then
    let a ← compile env args.back! (fuel-1)
    let fn := mkAppN t.getAppFn (args.extract 0 (args.size-1))
    return ⟨.unary op a.term,← mkAppM ``congrArg #[fn,a.proof]⟩
  if let some op := binaryHead? head then
    let a ← compile env args[args.size-2]! (fuel-1)
    let b ← compile env args.back! (fuel-1)
    let fn := mkAppN t.getAppFn (args.extract 0 (args.size-2))
    return ⟨.binary op a.term b.term,← mkAppM ``congrArg₂ #[fn,a.proof,b.proof]⟩
  if (head == ``HPow.hPow || head == ``Real.rpow) && args.size ≥ 2 then
    let a ← compile env args[args.size-2]! (fuel-1)
    let exponent := args.back!
    if (← whnfR (← inferType exponent)).isConstOf ``Nat then
      let some v ← Reify.ratValue? (α := q(ℕ)) exponent | throwError "nonconstant power"
      unless v.den == 1 && v.num ≥ 0 do throwError "invalid natural exponent"
      return ← withLocalDeclD `z (mkConst ``Real) fun z => do
        let fn ← mkLambdaFVars #[z]
          (mkAppN t.getAppFn ((args.extract 0 (args.size-2)).push z |>.push exponent))
        return ⟨.pow a.term v.num.toNat,← mkAppM ``congrArg #[fn,a.proof]⟩
    else
      let b ← compile env exponent (fuel-1)
      let .rat v := b.term | throwError "nonconstant real exponent"
      let fn := mkAppN t.getAppFn (args.extract 0 (args.size-2))
      return ⟨.rpow a.term v,← mkAppM ``congrArg₂ #[fn,a.proof,b.proof]⟩
  if head == ``Int.cast && args.size > 0 then
    let arg := args.back!
    if arg.getAppFn.isConstOf ``Int.floor then
      let a ← compile env arg.getAppArgs.back! (fuel-1)
      let fn : Lean.Expr := q(fun z : ℝ => ((⌊z⌋ : ℤ) : ℝ))
      return ⟨.unary .floor a.term,← mkAppM ``congrArg #[fn,a.proof]⟩
  if let some t' ← Reify.unfoldHead? t then return ← compile env t'.headBeta (fuel-1)
  throwError "nested integration: unsupported function {head}"

end Lynth.Interval.Integral.Nested
