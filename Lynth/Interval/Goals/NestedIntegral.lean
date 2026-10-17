import Lynth.Interval.Goals.Integral
import Lynth.Interval.Integral.NestedReify
import Lynth.Interval.Integral.NestedSound

/-! Recursive integral fallback. The existing one-dimensional solver is tried
first, preserving its certificates, trust decisions and heartbeat budgets. -/
namespace Lynth.Interval.Goals
open Lean Meta Elab Tactic Intgrl Integral Qq
namespace NI
open Integral.Nested

def evalCost : NExpr → Nat
  | .var _ | .rat _ | .pi => 1
  | .unary op a => evalCost a + match op with
      | .exp | .sin | .cos | .sinh | .cosh | .log | .atan => 60
      | .sqrt => 20 | _ => 2
  | .binary _ a b => evalCost a+evalCost b+4
  | .pow a n => evalCost a+2*(Nat.log2 (n+1)+1)
  | .rpow a _ => evalCost a+120
  | .integral _ a b f => evalCost a+evalCost b+8*evalCost f

def cost (prec : Nat) (e : NExpr) (cert : Cert) : Nat :=
  checkCost prec (evalCost e + cert.tables.foldl (fun s t => s+20*t.roots.length^2) 0 +
    cert.entries.foldl (fun s entry => s + match entry.method with
      | .split => 32*evalCost entry.expr
      | .panels p => p.pieces.foldl (fun s piece => s+ match piece.method with
          | .direct => 4*evalCost entry.expr
          | .gauss i _ =>
            let n := cert.tables[i]?.map (fun t => t.roots.length) |>.getD 0
            n*(32*evalCost entry.expr+80)+128*evalCost entry.expr) 0) 0)

def tryClose (g : MVarId) : IntegralM Bool := do
  let ty := (← instantiateMVars (← g.getType)).headBeta
  let_expr LT.lt _ _ lhs tol := ty | return false
  unless lhs.getAppFn.isConstOf ``abs do return false
  let some diff := lhs.getAppArgs.back? | return false
  unless diff.getAppFn.isConstOf ``HSub.hSub do return false
  let da := diff.getAppArgs
  if da.size < 2 then return false
  let some req ← parse da[da.size-2]! | return false
  -- Closed half-line goals are handled by the equality compiler below;
  -- their convergence facts use the corresponding Mathlib endpoint lemma.
  let cast := da.back!
  unless cast.isAppOfArity ``Rat.cast 3 do return false
  let qvar ← instantiateMVars cast.appArg!
  let a ← compile #[] req.a
  let b ← compile #[] req.b
  let (body,hf) ← withLocalDeclD `x (mkConst ``Real) fun x => do
    let r ← compile #[x] (mkApp req.f x).headBeta
    return (r.term,← mkLambdaFVars #[x] r.proof)
  let root : NExpr := .integral req.kind a.term b.term body
  let T ← compileClosed tol
  let tl ← tolLower tol
  if tl ≤ 0 then return false
  for prec in precSchedule (lynth.interval.maxPrec.get (← getOptions)) do
    let c := Ctx.make prec
    let some cert := search c root tl | continue
    let some I := enclosure c root cert | continue
    let (some lo,some hi) := (I.lo,I.hi) | continue
    let mid := (lo.toRat+hi.toRat)/2
    let width := hi.toRat-lo.toRat
    if width ≥ tl then continue
    for q in shortRats mid (tl/2-width/2) do
      unless check c root cert q T.term do continue
      let st ← liftM (saveState : TacticM Tactic.SavedState)
      unless ← isDefEq qvar (toExpr q) do liftM (st.restore : TacticM Unit); continue
      let ctxE := mkApp (mkConst ``Ctx.make) (toExpr prec)
      let certE := Integral.Nested.quoteCert cert
      let h ← certify (mkAppN (mkConst ``Integral.Nested.check)
        #[ctxE,quoteExpr root,certE,toExpr q,quoteTerm T.term]) (cost prec root cert)
      let hc := mkApp (mkConst ``Ctx.make_valid) (toExpr prec)
      let mut pf := mkAppN (mkConst ``Integral.Nested.result_of_check)
        #[req.f,req.a,req.b,tol,quoteExpr body,quoteExpr a.term,quoteExpr b.term,
          quoteTerm T.term,ctxE,quoteDomain req.kind,certE,toExpr q,hc,hf,a.proof,b.proof,T.proof,h]
      if req.closed then
        pf ← mkAppM (if req.kind == .right then ``closedRight else ``closedLeft) #[pf]
      let close ← mkAppM ``And.right #[pf]
      let conv ← mkAppM ``And.left #[pf]
      unless ← isDefEq (← inferType close) ty do
        liftM (st.restore : TacticM Unit)
        continue
      g.assign close
      modify fun fs => fs.push ⟨conv⟩
      trace[lynth.interval] "nested integral: prec={prec}, entries={cert.entries.size}, tables={cert.tables.map fun t => t.roots.length}, q={q}"
      return true
  return false
end NI

partial def solveNested (g : MVarId) (fuel : Nat := 16) : IntegralM Bool := do
  if ← g.isAssigned then return true
  if fuel == 0 then return false
  let ty := (← instantiateMVars (← g.getType)).headBeta
  for fact in ← get do
    if ← isDefEq ty (← inferType fact.converges) then g.assign fact.converges; return true
  if ← NI.tryClose g then return true
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
        if ← isProp (← child.getType) then proofs := child::proofs else data := data++[child]
      let mut ok := true
      for child in proofs++data do
        if !(← solveNested child (fuel-1)) then ok := false; break
      if ok then return true
    catch ex => trace[lynth.interval] "nested constructor {ctor}: {ex.toMessageData}"
    liftM (st.restore : TacticM Unit)
    set facts
  return false

def proveNestedIntegral? (ty : Lean.Expr) : TacticM (Option Lean.Expr) := do
  if (ty.find? fun e => e.isConstOf ``intervalIntegral || e.isConstOf ``MeasureTheory.integral).isNone then
    -- An answer constructor can hide the outer integral in a proof field,
    -- while its function argument is an alias for an iterated integral.
    let .const name _ := ty.getAppFn | return none
    let some (.inductInfo info) := (← getEnv).find? name | return none
    let mut found := false
    for ctor in info.ctors do
      let ct := (← getConstInfo ctor).type
      if (ct.find? fun e => e.isConstOf ``intervalIntegral ||
          e.isConstOf ``MeasureTheory.integral).isSome then found := true; break
    unless found do return none
  let saved ← saveState
  try
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    if ← (solveNested g.mvarId!).run' #[] then return some (← instantiateMVars g)
  catch ex => trace[lynth.interval] "nested integral: {ex.toMessageData}"
  saved.restore
  return none
end Lynth.Interval.Goals
