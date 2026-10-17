import Lynth.Interval.Integral.Reify
import Lynth.Interval.Integral.Divergence

/-! Numerical integral goals and user-defined result constructors. -/

namespace Lynth.Interval.Goals

open Lean Meta Elab Tactic Intgrl Integral Qq

structure IntegralRequest where
  f : Lean.Expr
  a : Lean.Expr
  b : Lean.Expr
  kind : Region

def realZero : Lean.Expr := q((0 : ℝ))

def parseSet (s : Lean.Expr) : MetaM (Option (Region × Lean.Expr × Lean.Expr)) := do
  let s ← instantiateMVars s
  let fn := s.getAppFn
  let args := s.getAppArgs
  if fn.isConstOf ``Set.univ then return some (.univ,realZero,realZero)
  if args.size == 0 then return none
  if fn.isConstOf ``Set.Ioi then return some (.ioi,args.back!,realZero)
  if fn.isConstOf ``Set.Ici then return some (.ici,args.back!,realZero)
  if args.size < 2 then return none
  let a := args[args.size-2]!
  let b := args.back!
  if fn.isConstOf ``Set.Icc then return some (.icc,a,b)
  if fn.isConstOf ``Set.Ioc then return some (.ioc,a,b)
  if fn.isConstOf ``Set.Ico then return some (.ico,a,b)
  if fn.isConstOf ``Set.Ioo then return some (.ioo,a,b)
  return none

def parseIntegral (t : Lean.Expr) : MetaM (Option IntegralRequest) := do
  let t ← instantiateMVars t
  let args := t.getAppArgs
  if t.getAppFn.isConstOf ``intervalIntegral && args.size ≥ 4 then
    return some ⟨args[args.size-4]!,args[args.size-3]!,args[args.size-2]!,.interval⟩
  if t.getAppFn.isConstOf ``MeasureTheory.integral && args.size ≥ 2 then
    let μ := args[args.size-2]!
    let f := args.back!
    if μ.getAppFn.isConstOf ``MeasureTheory.Measure.restrict then
      if let some (k,a,b) ← parseSet μ.getAppArgs.back! then return some ⟨f,a,b,k⟩
  return none

structure IntegralFact where
  converges : Lean.Expr

abbrev IntegralM := StateRefT (Array IntegralFact) TacticM

def integralEvalCost : Intgrl.Term → Nat
  | .var | .rat _ | .pi => 1
  | .unary op a => integralEvalCost a + match op with
      | .exp | .sin | .cos | .sinh | .cosh | .log | .atan => 60
      | .sqrt => 20
      | _ => 2
  | .binary _ a b => integralEvalCost a + integralEvalCost b + 4
  | .pow a n => integralEvalCost a + 2 * (Nat.log2 (n+1) + 1)
  | .rpow a _ => integralEvalCost a + 120

/-- Account for root verification, analytic bounds, samples and precision.
The common trust driver applies the user's kernel/native/auto setting. -/
def integralCheckCost (prec : Nat) (e : Intgrl.Term) (cert : IntegralCertificate) : Nat :=
  let core := cert.core
  let nodes := core.tables.foldl (fun acc t =>
    acc + 20 * t.roots.length * t.roots.length) 0
  let ec := integralEvalCost e
  let panels := core.pieces.foldl (fun acc p => acc + match p.method with
    | .direct => 4 * ec
    | .gauss i _ =>
        let n := (core.tables[i]?).map (fun t => t.roots.length) |>.getD 0
        n * (32 * ec + 80) + 128 * ec) 0
  checkCost prec (nodes + panels)

/-- Untrusted initial precision hint. Samples away from the midpoint keep
cancellation from hiding the integrand's scale. Small-valued integrals can
retain low precision even with tiny absolute tolerances. -/
def integralPrecSchedule (maxPrec : Nat) (e A B : Intgrl.Term) (kind : Region)
    (tol : ℚ) : List Nat := Id.run do
  let schedule := precSchedule maxPrec
  if !kind.isFinite || tol ≥ (show Dy from ⟨1,-32⟩).toRat then return schedule
  let c := Ctx.make 64
  let (some a,some b) := ((evalR c A Ival.zero).mid,(evalR c B Ival.zero).mid)
    | return schedule
  let mut magnitude := Dy.zero
  for i in [0:5] do
    let x := Ival.ofRat 64 (a.toRat + (b.toRat-a.toRat) * ((i : Nat) : ℚ)/4)
    let some m := (Ival.abs (evalR c e x)).hi | return schedule
    magnitude := Dy.max magnitude m
  let scale := magnitude.toRat * |b.toRat-a.toRat|
  if scale ≤ tol then return schedule
  let ratio := scale/tol
  let bits := ratio.num.natAbs.log2 + 1 - ratio.den.log2
  let hint := min (schedule.getLast?.getD 64) (max 64 (bits+24))
  return schedule.filter (· ≥ hint)

partial def parseConverges (t : Lean.Expr) : MetaM (Option IntegralRequest) := do
  let t ← instantiateMVars t
  let args := t.getAppArgs
  if t.getAppFn.isConstOf ``IntervalIntegrable && args.size ≥ 4 then
    return some ⟨args[args.size-4]!,args[args.size-2]!,args.back!,.interval⟩
  if t.getAppFn.isConstOf ``MeasureTheory.IntegrableOn && args.size ≥ 3 then
    if let some (k,a,b) ← parseSet args[args.size-2]! then
      return some ⟨args[args.size-3]!,a,b,k⟩
  if let some t' ← Reify.unfoldHead? t then return ← parseConverges t'
  return none

def tryIntegralDivergence (g : MVarId) : IntegralM Bool := do
  let ty := (← instantiateMVars (← g.getType)).headBeta
  let_expr Not P := ty | return false
  let some req ← parseConverges P | return false
  let body ← compileBody req.f
  let a ← compileClosed req.a
  let b ← compileClosed req.b
  for prec in [64,128,256] do
    let ctx := Ctx.make prec
    unless divergenceCheck ctx body.term a.term b.term req.kind do continue
    let ctxE := mkApp (mkConst ``Ctx.make) (toExpr prec)
    let chk := mkAppN (mkConst ``divergenceCheck)
      #[ctxE,quoteTerm body.term,quoteTerm a.term,quoteTerm b.term,quoteRegion req.kind]
    let h ← certify chk (checkCost prec 40)
    let hc := mkApp (mkConst ``Ctx.make_valid) (toExpr prec)
    let pf := mkAppN (mkConst ``not_converges_of_check)
      #[req.f,req.a,req.b,quoteTerm body.term,quoteTerm a.term,quoteTerm b.term,ctxE,
        quoteRegion req.kind,hc,body.proof,a.proof,b.proof,h]
    if ← isDefEq (← inferType pf) ty then
      g.assign pf
      return true
  return false

def tryIntegralClose (g : MVarId) : IntegralM Bool := do
  let ty := (← instantiateMVars (← g.getType)).headBeta
  let_expr LT.lt _ _ lhs tol := ty | return false
  unless lhs.getAppFn.isConstOf ``abs do return false
  let some diff := lhs.getAppArgs.back? | return false
  unless diff.getAppFn.isConstOf ``HSub.hSub do return false
  let da := diff.getAppArgs
  if da.size < 2 then return false
  let some req ← parseIntegral da[da.size-2]! | return false
  let cast := da.back!
  unless cast.isAppOfArity ``Rat.cast 3 do return false
  let qvar ← instantiateMVars cast.appArg!
  let body ← compileBody req.f
  let a ← compileClosed req.a
  let b ← compileClosed req.b
  let t ← compileClosed tol
  if divergenceCheck (Ctx.make 64) body.term a.term b.term req.kind then return false
  let tl ← tolLower tol
  if tl ≤ 0 then return false
  let maxPrec := lynth.interval.maxPrec.get (← getOptions)
  for prec in integralPrecSchedule maxPrec body.term a.term b.term req.kind tl do
    let ctx := Ctx.make prec
    let some (cert,S) := searchIntegralEstimate ctx body.term a.term b.term req.kind tl | continue
    let (some lo,some hi) := (S.lo,S.hi) | continue
    let mid := (lo.toRat+hi.toRat)/2
    let width := hi.toRat-lo.toRat
    if width ≥ tl then continue
    for candidate in shortRats mid (tl/2-width/2) do
      -- Witness selection uses the untrusted search estimate. The certified
      -- check below independently recomputes every panel and error bound.
      unless closeCheck ctx S candidate t.term do continue
      let state ← liftM (saveState : TacticM Tactic.SavedState)
      unless ← isDefEq qvar (toExpr candidate) do liftM (state.restore : TacticM Unit); continue
      let ctxE := mkApp (mkConst ``Ctx.make) (toExpr prec)
      let certE ← quoteIntegralCertShared cert
      let chk := mkAppN (mkConst ``integralCheck)
        #[ctxE,quoteTerm body.term,quoteTerm a.term,quoteTerm b.term,quoteRegion req.kind,
          certE,toExpr candidate,quoteTerm t.term]
      let hchk ← certify chk (integralCheckCost prec body.term cert)
      let hc := mkApp (mkConst ``Ctx.make_valid) (toExpr prec)
      let pf := mkAppN (mkConst ``integration_result_of_check)
        #[req.f,req.a,req.b,tol,quoteTerm body.term,quoteTerm a.term,quoteTerm b.term,
          quoteTerm t.term,ctxE,quoteRegion req.kind,certE,toExpr candidate,
          hc,body.proof,a.proof,b.proof,t.proof,hchk]
      let close ← mkAppM ``And.right #[pf]
      let conv ← mkAppM ``And.left #[pf]
      unless ← isDefEq (← inferType close) ty do
        liftM (state.restore : TacticM Unit)
        continue
      g.assign close
      modify fun fs => fs.push ⟨conv⟩
      trace[lynth.interval] "integral: prec={prec}, pieces={cert.core.pieces.length}, nodes={cert.core.tables.map fun t => t.roots.length}, q={candidate}"
      return true
  return false

/-- Proof fields are solved before data fields, allowing the numerical check
to assign a rational witness metavariable introduced by any result constructor. -/
partial def solveIntegral (g : MVarId) (fuel : Nat := 12) : IntegralM Bool := do
  if ← g.isAssigned then return true
  if fuel == 0 then return false
  let ty := (← instantiateMVars (← g.getType)).headBeta
  for fact in ← get do
    if ← isDefEq ty (← inferType fact.converges) then
      g.assign fact.converges
      return true
  if ← tryIntegralClose g then return true
  if ← tryIntegralDivergence g then return true
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
      let mut proofGoals : List MVarId := []
      let mut dataGoals : List MVarId := []
      for child in gs do
        if ← isProp (← child.getType) then
          proofGoals := child :: proofGoals
        else dataGoals := dataGoals ++ [child]
      let mut ok := true
      for child in proofGoals ++ dataGoals do
        if !(← solveIntegral child (fuel-1)) then ok := false; break
      if ok then return true
    catch ex => trace[lynth.interval] "integral constructor {ctor}: {ex.toMessageData}"
    liftM (st.restore : TacticM Unit)
    set facts
  return false

def proveIntegral? (ty : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let saved ← saveState
  try
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    if ← (solveIntegral g.mvarId!).run' #[] then
      return some (← instantiateMVars g)
  catch ex => trace[lynth.interval] "integral: {ex.toMessageData}"
  saved.restore
  return none

end Lynth.Interval.Goals
