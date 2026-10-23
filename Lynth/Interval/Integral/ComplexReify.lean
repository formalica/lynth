module

meta import all Lynth.Interval.Integral.NestedReify
import all Lynth.Interval.Integral.NestedReify
meta import all Lynth.Interval.Integral.Math.ComplexIntegral
import all Lynth.Interval.Integral.Math.ComplexIntegral

/-! Compile complex functions while keeping every integration variable real. -/
meta section

namespace Lynth.Interval.Integral.ComplexReify
open Lean Meta Elab Tactic Intgrl Qq

structure Compiled where
  term : CExpr
  proof : Lean.Expr

def quote : CExpr → Lean.Expr
  | .real a => mkApp (mkConst ``CExpr.real) (Nested.quoteExpr a)
  | .i => mkConst ``CExpr.i
  | .unary op a => mkApp2 (mkConst ``CExpr.unary) (quoteUnary op) (quote a)
  | .binary op a b => mkApp3 (mkConst ``CExpr.binary) (quoteBinary op) (quote a) (quote b)
  | .pow a n => mkApp2 (mkConst ``CExpr.pow) (quote a) (toExpr n)
  | .positivePower b a => mkApp2 (mkConst ``CExpr.positivePower) (toExpr b) (quote a)
  | .integral k a b f => mkApp4 (mkConst ``CExpr.integral) (Nested.quoteDomain k)
      (Nested.quoteExpr a) (Nested.quoteExpr b) (quote f)

def unary? (head : Name) : Option Unary :=
  if head == ``Neg.neg then some .neg else
  if head == ``Inv.inv then some .inv else
  if head == ``Complex.exp then some .exp else
  if head == ``Complex.sin then some .sin else
  if head == ``Complex.cos then some .cos else
  if head == ``Complex.sinh then some .sinh else
  if head == ``Complex.cosh then some .cosh else
  if head == ``Complex.log then some .log else
  if head == ``Complex.sqrt then some .sqrt else none

partial def compile (env : Array Lean.Expr) (t : Lean.Expr) (fuel := 256) : MetaM Compiled := do
  if fuel == 0 then throwError "complex integration: expression is too deep"
  let t := (← instantiateMVars t).headBeta
  if t.isConstOf ``Complex.I then return ⟨.i,← mkEqRefl t⟩
  let head := t.getAppFn
  let args := t.getAppArgs
  if head.isConstOf ``Complex.ofReal then
    let a ← Nested.compile env args.back! (fuel-1)
    return ⟨.real a.term,← mkAppM ``congrArg #[mkConst ``Complex.ofReal,a.proof]⟩
  if !t.hasFVar && !t.hasMVar && !Reify.isTranscendentalHead t then
    if let some v ← Reify.ratValue? (α := q(ℂ)) t then
      let vq : Q(ℚ) := toExpr v
      let rhs : Q(ℂ) := q(($vq : ℂ))
      if let some p ← Reify.normNumEq? (α := q(ℂ)) t rhs then
        let cast ← mkAppM ``Complex.ofReal_ratCast #[vq]
        return ⟨.real (.rat v),← mkEqTrans p (← mkEqSymm cast)⟩
  if let some req ← Nested.parse t then
    if req.closed then throwError "complex integration: use an open half-line endpoint"
    let a ← Nested.compile env req.a (fuel-1)
    let b ← Nested.compile env req.b (fuel-1)
    let f ← withLocalDeclD `x (mkConst ``Real) fun x => do
      let r ← compile (env.push x) (mkApp req.f x).headBeta (fuel-1)
      return (r.term,← mkLambdaFVars #[x] r.proof)
    let p ← mkAppM ``NDomain.cvalue_congr #[Nested.quoteDomain req.kind,f.2,a.proof,b.proof]
    return ⟨.integral req.kind a.term b.term f.1,p⟩
  if let .const n _ := head then
    if let some op := unary? n then
      let a ← compile env args.back! (fuel-1)
      let fn := mkAppN head (args.extract 0 (args.size-1))
      return ⟨.unary op a.term,← mkAppM ``congrArg #[fn,a.proof]⟩
    if let some op := binaryHead? n then
      unless op == .add || op == .sub || op == .mul || op == .div do
        throwError "complex integration: unsupported binary operation"
      let a ← compile env args[args.size-2]! (fuel-1)
      let b ← compile env args.back! (fuel-1)
      let fn := mkAppN head (args.extract 0 (args.size-2))
      return ⟨.binary op a.term b.term,← mkAppM ``congrArg₂ #[fn,a.proof,b.proof]⟩
    if (n == ``HPow.hPow || n == ``Complex.cpow) && args.size ≥ 2 then
      let base := args[args.size-2]!
      let exponent := args.back!
      let et ← whnfR (← inferType exponent)
      if et.isConstOf ``Nat then
        let a ← compile env base (fuel-1)
        let some v ← Reify.ratValue? (α := q(ℕ)) exponent | throwError "nonconstant power"
        let n := v.num.toNat
        return ← withLocalDeclD `z (mkConst ``Complex) fun z => do
          let fn ← mkLambdaFVars #[z]
            (mkAppN head ((args.extract 0 (args.size-2)).push z |>.push exponent))
          return ⟨.pow a.term n,← mkAppM ``congrArg #[fn,a.proof]⟩
      if let some v ← Reify.ratValue? (α := q(ℂ)) exponent then
        if v == 1/2 then
          let a ← compile env base (fuel-1)
          let some hp ← Reify.normNumEq? (α := q(ℂ)) exponent q((2:ℂ)⁻¹) |
            throwError "could not normalize the square-root exponent"
          let fn := mkAppN head (args.extract 0 (args.size-2))
          return ⟨.unary .sqrt a.term,← mkAppM ``congrArg₂ #[fn,a.proof,hp]⟩
      let some v ← Reify.ratValue? (α := q(ℂ)) base |
        throwError "complex integration: powers require a positive rational base or exponent 1/2"
      unless v > 0 do throwError "complex integration: the constant power base must be positive"
      let a ← compile env exponent (fuel-1)
      let vq : Q(ℚ) := toExpr v
      let some hb ← Reify.normNumEq? (α := q(ℂ)) base q(($vq : ℂ)) |
        throwError "could not normalize the constant power base"
      let fn := mkAppN head (args.extract 0 (args.size-2))
      return ⟨.positivePower v a.term,← mkAppM ``congrArg₂ #[fn,hb,a.proof]⟩
  if let some t' ← Reify.unfoldHead? t then return ← compile env t'.headBeta (fuel-1)
  throwError "complex integration: unsupported expression {t}"
end Lynth.Interval.Integral.ComplexReify
