module

meta import Lynth.Options
import Lynth.Options
meta import all Lynth.Interval.Goals.NestedIntegral
import all Lynth.Interval.Goals.NestedIntegral
meta import all Lynth.Interval.Integral.ComplexReify
import all Lynth.Interval.Integral.ComplexReify
meta import all Lynth.Interval.Integral.Math.ComplexReduction
import all Lynth.Interval.Integral.Math.ComplexReduction

/-! Certified complex-valued integration over real ranges. The two scalar
projections use the existing Gauss–Legendre/Petras certificates. -/
meta section

namespace Lynth.Interval.Goals
open Lean Meta Elab Tactic Intgrl Integral Qq

namespace CI

structure Component where
  q : ℚ
  proof : Lean.Expr

/-- Search is untrusted. Each returned component includes the reconstructed
convergence and numerical-error proof from the independent checker. -/
private def componentRaw (prec : Nat) (e : NExpr) (T : Intgrl.Term) (tol : ℚ) : TacticM (Option Component) := do
  let c := Ctx.make prec
  let steps := lynth.interval.complexIntegralSteps.get (← getOptions)
  let attempt : Option Nested.Cert := do
    if !e.scoped 0 || tol ≤ 0 then none else do
      let (_,s) ← (Nested.evaluate c e #[] (tol/32)).run {remaining := steps}
      return ⟨s.pool.tables,s.entries⟩
  let some cert := attempt |
    trace[lynth.interval] "complex component: search failed, prec={prec}, size={e.size}"
    return none
  let some I := Nested.enclosure c e cert |
    trace[lynth.interval] "complex component: replay failed, prec={prec}, size={e.size}"
    return none
  let (some lo,some hi) := (I.lo,I.hi) | return none
  let width := hi.toRat-lo.toRat
  if width ≥ tol/4 then
    trace[lynth.interval] "complex component: enclosure too wide, prec={prec}, width={width}"
    return none
  for q in shortRats ((lo.toRat+hi.toRat)/2) (tol/8-width/2) do
    unless closeCheck c I q T do continue
    let ctxE := mkApp (mkConst ``Ctx.make) (toExpr prec)
    let certE := Nested.quoteCert cert
    let chk := mkAppN (mkConst ``Nested.check)
      #[ctxE,Nested.quoteExpr e,certE,toExpr q,quoteTerm T]
    let h ← certify chk (NI.cost prec e cert)
    let proof := mkAppN (mkConst ``Nested.check_sound)
      #[ctxE,mkApp (mkConst ``Ctx.make_valid) (toExpr prec),
        Nested.quoteExpr e,certE,toExpr q,quoteTerm T,h]
    return some ⟨q,proof⟩
  return none

/-- Exact affine phases avoid subdividing thousands of oscillations. Their
mathematical transport theorem still returns convergence of the original AST. -/
def component (prec : Nat) (e : NExpr) (T : Intgrl.Term) (tol : ℚ) :
    TacticM (Option Component) := do
  let reduced := e.reduceComplexIntegral 0
  if !(reduced == e) then
    if let some r ← componentRaw prec reduced T tol then
      let hs ← mkDecideProof (← mkEq
        (mkApp2 (mkConst ``NExpr.scoped) (mkNatLit 0) (Nested.quoteExpr e))
        (mkConst ``Bool.true))
      let tolE := mkApp2 (mkConst ``Intgrl.Term.real) (quoteTerm T) q((0:ℝ))
      let proof := mkAppN (mkConst ``NExpr.reduceComplexIntegral_result)
        #[Nested.quoteExpr e,toExpr r.q,tolE,hs,r.proof]
      return some ⟨r.q,proof⟩
  componentRaw prec e T tol

private partial def parseAlias (z : Lean.Expr) (fuel : Nat := 32) :
    MetaM (Option Nested.Request) := do
  if let some req ← Nested.parse z then return some req
  if fuel == 0 then return none
  if let some z' ← Reify.unfoldHead? z then return ← parseAlias z' (fuel-1)
  return none

def tryClose (g : MVarId) : IntegralM Bool := do
  let ty := (← instantiateMVars (← g.getType)).headBeta
  let_expr LT.lt _ _ lhs tol := ty | return false
  unless lhs.getAppFn.isConstOf ``Norm.norm do return false
  let diff := lhs.getAppArgs.back!
  unless diff.getAppFn.isConstOf ``HSub.hSub do return false
  let da := diff.getAppArgs
  let z := da[da.size-2]!
  let target := da.back!
  unless ← isDefEq (← inferType z) (mkConst ``Complex) do return false
  let some req ← parseAlias z | return false
  if req.closed then return false
  let a ← Nested.compile #[] req.a
  let b ← Nested.compile #[] req.b
  let (body,hf) ← withLocalDeclD `x (mkConst ``Real) fun x => do
    let r ← ComplexReify.compile #[x] (mkApp req.f x).headBeta
    return (r.term,← mkLambdaFVars #[x] r.proof)
  let root : CExpr := .integral req.kind a.term b.term body
  let (re,im) := root.parts
  let t ← compileClosed tol
  let T : Intgrl.Term := .binary .div t.term (.rat 4)
  let tl ← tolLower tol
  if tl ≤ 0 then return false
  let hs ← mkDecideProof (mkApp (mkConst ``CExpr.Supported) (ComplexReify.quote body))
  let hlog ← mkDecideProof (mkApp (mkConst ``CExpr.LogProjectionSafe) (ComplexReify.quote body))
  for prec in precSchedule (lynth.interval.maxPrec.get (← getOptions)) do
    let some r ← liftM (component prec re T tl : TacticM _) | continue
    let some i ← liftM (component prec im T tl : TacticM _) | continue
    let qr : Q(ℚ) := toExpr r.q
    let qi : Q(ℚ) := toExpr i.q
    let value : Q(ℂ) := q(($qr : ℂ)+($qi : ℂ)*Complex.I)
    let st ← liftM (saveState : TacticM Tactic.SavedState)
    unless ← isDefEq target value do liftM (st.restore : TacticM Unit); continue
    let tolE := mkApp2 (mkConst ``Intgrl.Term.real) (quoteTerm t.term) q((0:ℝ))
    let pf := mkAppN (mkConst ``complex_result_of_parts)
      #[req.f,req.a,req.b,tolE,ComplexReify.quote body,
        Nested.quoteExpr a.term,Nested.quoteExpr b.term,Nested.quoteDomain req.kind,
        toExpr r.q,toExpr i.q,hs,hlog,hf,a.proof,b.proof,r.proof,i.proof]
    let conv ← mkAppM ``And.left #[pf]
    let close ← mkAppM ``And.right #[pf]
    let close ← mkAppM ``lt_of_lt_of_eq #[close,← mkEqSymm t.proof]
    unless ← isDefEq (← inferType close) ty do
      liftM (st.restore : TacticM Unit)
      continue
    g.assign close
    modify fun fs => fs.push ⟨conv⟩
    trace[lynth.interval] "complex integral: prec={prec}, q=({r.q}, {i.q})"
    return true
  return false

/-- Expose a rational pair's fields before solving its proof fields. -/
def preparePair (g : MVarId) : TacticM Unit := do
  let ty ← whnf (← g.getType)
  let some (a,b) ← prodArgs? ty | return
  unless a.isConstOf ``Rat && b.isConstOf ``Rat do return
  let x ← mkFreshExprMVar a
  let y ← mkFreshExprMVar b
  g.assign (← mkAppM ``Prod.mk #[x,y])
end CI

partial def solveComplexIntegral (g : MVarId) (fuel : Nat := 16) : IntegralM Bool := do
  if ← g.isAssigned then return true
  if fuel == 0 then return false
  let ty := (← instantiateMVars (← g.getType)).headBeta
  for fact in ← get do
    if ← isDefEq ty (← inferType fact.converges) then g.assign fact.converges; return true
  if ← CI.tryClose g then return true
  let ty ← whnf ty
  let .const name _ := ty.getAppFn | return false
  let constructors ←
    if name == ``And then pure [``And.intro] else
    if name == ``Subtype then pure [``Subtype.mk] else
    if name == ``PSum then pure [``PSum.inl,``PSum.inr] else do
      let some (.inductInfo info) := (← getEnv).find? name | return false
      if info.ctors.length != 2 || info.isRec then return false
      pure info.ctors
  for ctor in constructors do
    let st ← liftM (saveState : TacticM Tactic.SavedState)
    let facts ← get
    try
      let gs ← g.apply (← mkConstWithFreshMVarLevels ctor)
      let mut proofs : List MVarId := []
      let mut data : List MVarId := []
      for child in gs do
        if ← isProp (← child.getType) then proofs := child::proofs
        else
          liftM (CI.preparePair child : TacticM Unit)
          data := data ++ [child]
      let mut ok := true
      for child in proofs++data do
        if !(← solveComplexIntegral child (fuel-1)) then ok := false; break
      if ok then return true
    catch ex => trace[lynth.interval] "complex integral constructor {ctor}: {ex.toMessageData}"
    liftM (st.restore : TacticM Unit)
    set facts
  return false

def proveComplexIntegral? (ty : Lean.Expr) : TacticM (Option Lean.Expr) := do
  if (ty.find? fun e => e.isConstOf ``Complex).isNone then return none
  let saved ← saveState
  try
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    if ← (solveComplexIntegral g.mvarId!).run' #[] then
      return some (← instantiateMVars g)
  catch ex => trace[lynth.interval] "complex integral: {ex.toMessageData}"
  saved.restore
  return none
end Lynth.Interval.Goals
