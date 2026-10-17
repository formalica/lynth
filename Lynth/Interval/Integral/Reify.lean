import Lynth.Interval.Integral.Engine
import Lynth.Interval.Goals.Approx

/-! Proof-producing compiler from real functions to integration expressions. -/

namespace Lynth.Interval.Integral

open Lean Meta Elab Tactic Intgrl Qq

def quoteUnary (op : Unary) : Lean.Expr :=
  mkConst (match op with
    | .neg => ``Unary.neg | .inv => ``Unary.inv | .exp => ``Unary.exp
    | .sin => ``Unary.sin | .cos => ``Unary.cos | .sinh => ``Unary.sinh
    | .cosh => ``Unary.cosh | .log => ``Unary.log | .sqrt => ``Unary.sqrt
    | .abs => ``Unary.abs | .floor => ``Unary.floor | .atan => ``Unary.atan)

def quoteBinary (op : Binary) : Lean.Expr :=
  mkConst (match op with
    | .add => ``Binary.add | .sub => ``Binary.sub | .mul => ``Binary.mul
    | .div => ``Binary.div | .max => ``Binary.max | .min => ``Binary.min)

def quoteTerm : Intgrl.Term → Lean.Expr
  | .var => mkConst ``Intgrl.Term.var | .pi => mkConst ``Intgrl.Term.pi
  | .rat q => mkApp (mkConst ``Intgrl.Term.rat) (toExpr q)
  | .unary op a => mkApp2 (mkConst ``Intgrl.Term.unary) (quoteUnary op) (quoteTerm a)
  | .binary op a b => mkApp3 (mkConst ``Intgrl.Term.binary) (quoteBinary op) (quoteTerm a) (quoteTerm b)
  | .pow a n => mkApp2 (mkConst ``Intgrl.Term.pow) (quoteTerm a) (toExpr n)
  | .rpow a q => mkApp2 (mkConst ``Intgrl.Term.rpow) (quoteTerm a) (toExpr q)

def quoteRegion (k : Region) : Lean.Expr :=
  mkConst (match k with
    | .interval => ``Region.interval | .icc => ``Region.icc | .ioc => ``Region.ioc
    | .ico => ``Region.ico | .ioo => ``Region.ioo | .ioi => ``Region.ioi
    | .ici => ``Region.ici | .univ => ``Region.univ)

def quoteDy (d : Dy) : Lean.Expr :=
  mkApp2 (mkConst ``Vendor.Dyadic.mk) (toExpr d.mantissa) (toExpr d.exponent)

def quoteList (type : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x tail => mkApp3 (mkConst ``List.cons [0]) type x tail)
    (mkApp (mkConst ``List.nil [0]) type)

def quoteIval (I : Ival) : Lean.Expr :=
  let endpoint := fun o => match o with
    | none => mkApp (mkConst ``Option.none [0]) (mkConst ``Vendor.Dyadic)
    | some d => mkApp2 (mkConst ``Option.some [0]) (mkConst ``Vendor.Dyadic) (quoteDy d)
  mkApp2 (mkConst ``Ival.mk) (endpoint I.lo) (endpoint I.hi)

def quoteTable (t : NodeTable) : Lean.Expr :=
  mkApp2 (mkConst ``NodeTable.mk) (quoteList
    (mkApp2 (mkConst ``Prod [0,0]) (mkConst ``Vendor.Dyadic) (mkConst ``Vendor.Dyadic))
    (t.roots.map fun (a,b) => mkApp4 (mkConst ``Prod.mk [0,0])
      (mkConst ``Vendor.Dyadic) (mkConst ``Vendor.Dyadic) (quoteDy a) (quoteDy b)))
    (quoteList (mkConst ``Ival) (t.certWeights.map quoteIval))

def quoteMethod : Method → Lean.Expr
  | .direct => mkConst ``Method.direct
  | .gauss n ρ => mkApp2 (mkConst ``Method.gauss) (toExpr n) (quoteDy ρ)

def quotePiece (p : Piece) : Lean.Expr :=
  mkApp3 (mkConst ``Piece.mk) (quoteDy p.a) (quoteDy p.b) (quoteMethod p.method)

def quoteCert (cert : Certificate) : Lean.Expr :=
  mkApp5 (mkConst ``Certificate.mk) (quoteDy cert.a) (quoteDy cert.b) (toExpr cert.reverse)
    (mkApp2 (mkConst ``Array.mk [0]) (mkConst ``NodeTable)
      (quoteList (mkConst ``NodeTable) (cert.tables.toList.map quoteTable)))
    (quoteList (mkConst ``Piece) (cert.pieces.map quotePiece))

def quoteIntegralCert : IntegralCertificate → Lean.Expr
  | .finite c => mkApp (mkConst ``IntegralCertificate.finite) (quoteCert c)
  | .tail r c => mkApp2 (mkConst ``IntegralCertificate.tail) (quoteDy r) (quoteCert c)
  | .logarithm r c => mkApp2 (mkConst ``IntegralCertificate.logarithm) (quoteDy r) (quoteCert c)
  | .sqrtWeight n c => mkApp2 (mkConst ``IntegralCertificate.sqrtWeight) (toExpr n) (quoteCert c)

structure Compiled where
  term : Intgrl.Term
  proof : Lean.Expr

def unaryHead? (n : Name) : Option Unary :=
  if n == ``Neg.neg then some .neg else
  if n == ``Inv.inv then some .inv else
  if n == ``Real.exp then some .exp else
  if n == ``Real.sin then some .sin else
  if n == ``Real.cos then some .cos else
  if n == ``Real.sinh then some .sinh else
  if n == ``Real.cosh then some .cosh else
  if n == ``Real.log then some .log else
  if n == ``Real.sqrt then some .sqrt else
  if n == ``abs then some .abs else
  if n == ``Real.arctan then some .atan else none

def binaryHead? (n : Name) : Option Binary :=
  if n == ``HAdd.hAdd then some .add else
  if n == ``HSub.hSub then some .sub else
  if n == ``HMul.hMul then some .mul else
  if n == ``HDiv.hDiv then some .div else
  if n == ``Max.max then some .max else
  if n == ``Min.min then some .min else none

/-- The proof is t = term.real x; unsupported functions leave the goal untouched. -/
partial def compileTerm (x t : Lean.Expr) (fuel : Nat := 256) : MetaM Compiled := do
  if fuel == 0 then throwError "integration compiler: expression is too deep"
  let t ← instantiateMVars t
  if t == x then return ⟨.var, ← mkEqRefl t⟩
  if t.isConstOf ``Real.pi then return ⟨.pi, ← mkEqRefl t⟩
  if !t.hasFVar && !t.hasMVar && !Reify.isTranscendentalHead t then
    let rc : Reify.RCtx := {}
    if let some r ← Reify.exact? .real t rc.senv then
      if let some q ← Reify.ratValue? (α := q(ℝ)) t then
        return ⟨.rat q,r.proof⟩
  let .const head _ := t.getAppFn | throwError "integration compiler: unsupported {t}"
  let args := t.getAppArgs
  if head == ``Real.tan && args.size == 1 then
    let a ← compileTerm x args[0]! (fuel-1)
    let result : Intgrl.Term := .binary .div (.unary .sin a.term) (.unary .cos a.term)
    let eq' ← mkAppM ``congrArg #[mkConst ``Real.tan,a.proof]
    let p ← mkEqTrans eq' (mkApp (mkConst ``Real.tan_eq_sin_div_cos)
      (mkApp2 (mkConst ``Intgrl.Term.real) (quoteTerm a.term) x))
    return ⟨result,p⟩
  if let some op := unaryHead? head then
    let some arg := args.back? | throwError "integration compiler: missing unary argument"
    let a ← compileTerm x arg (fuel-1)
    let fn := mkAppN t.getAppFn (args.extract 0 (args.size-1))
    return ⟨.unary op a.term, ← mkAppM ``congrArg #[fn,a.proof]⟩
  if let some op := binaryHead? head then
    if args.size < 2 then throwError "integration compiler: missing binary argument"
    let a ← compileTerm x args[args.size-2]! (fuel-1)
    let b ← compileTerm x args[args.size-1]! (fuel-1)
    let fn := mkAppN t.getAppFn (args.extract 0 (args.size-2))
    return ⟨.binary op a.term b.term, ← mkAppM ``congrArg₂ #[fn,a.proof,b.proof]⟩
  if (head == ``HPow.hPow || head == ``Real.rpow) && args.size ≥ 2 then
    let base := args[args.size-2]!
    let exponent := args[args.size-1]!
    let a ← compileTerm x base (fuel-1)
    let et ← whnfR (← inferType exponent)
    if et.isConstOf ``Nat then
      let some v ← Reify.ratValue? (α := q(ℕ)) exponent |
        throwError "integration compiler: nonconstant exponent"
      let n := v.num.toNat
      unless v.den == 1 && v.num ≥ 0 do throwError "integration compiler: invalid natural exponent"
      return ← withLocalDeclD `z (mkConst ``Real) fun z => do
        let fn ← mkLambdaFVars #[z]
          (mkAppN t.getAppFn ((args.extract 0 (args.size-2)).push z |>.push exponent))
        return ⟨.pow a.term n, ← mkAppM ``congrArg #[fn,a.proof]⟩
    else
      let b ← compileTerm x exponent (fuel-1)
      let .rat v := b.term | throwError "integration compiler: nonconstant real exponent"
      let fn := mkAppN t.getAppFn (args.extract 0 (args.size-2))
      return ⟨.rpow a.term v, ← mkAppM ``congrArg₂ #[fn,a.proof,b.proof]⟩
  if head == ``Int.cast && args.size > 0 then
    let arg := args.back!
    if arg.getAppFn.isConstOf ``Int.floor then
      let a ← compileTerm x arg.getAppArgs.back! (fuel-1)
      let fn : Lean.Expr := q(fun z : ℝ => ((⌊z⌋ : ℤ) : ℝ))
      return ⟨.unary .floor a.term, ← mkAppM ``congrArg #[fn,a.proof]⟩
  if let some t' ← Reify.unfoldHead? t then
    return ← compileTerm x t'.headBeta (fuel-1)
  throwError "integration compiler: unsupported function {head}"

def compileBody (f : Lean.Expr) : MetaM Compiled := do
  withLocalDeclD `x (mkConst ``Real) fun x => do
    let r ← compileTerm x (mkApp f x).headBeta
    return ⟨r.term, ← mkLambdaFVars #[x] r.proof⟩

def compileClosed (t : Lean.Expr) : MetaM Compiled := do
  let zero : Lean.Expr := q((0 : ℝ))
  compileTerm zero t

end Lynth.Interval.Integral
