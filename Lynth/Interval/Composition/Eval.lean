import Lynth.Interval.Composition.Bounds
import Lynth.Interval.Goals.NestedIntegral
import Lynth.Interval.Goals.Series

/-! Compositional real enclosures. Every leaf returns an interval and a proof.
Finite binders are specialized hygienically; series tails retain parameter boxes.
The fast integral checker is reused, with measurable interval panels as fallback.
-/
namespace Lynth.Interval.Goals.Composition
open Lean Meta Elab Tactic Qq
open Lynth.Interval.Composition
open Integral

structure Bound where
  term : Lean.Expr
  interval : Ival
  proof : Lean.Expr

structure TailModel where
  value : RAsy
  expr : Lean.Expr
  proof : Lean.Expr

structure Context where
  rc : Reify.RCtx := {}
  env : IEnv := {}
  envExpr : Lean.Expr := emptyIEnvExpr
  holds : Lean.Expr := mkConst ``IEnv.holds_empty

structure Settings where
  precision : Nat
  scope : Array FVarId := #[]

structure RetryInfo where
  reason? : Option MessageData := none

abbrev M := ReaderT Settings
  (StateRefT (Array Lean.Expr) (StateRefT RetryInfo TacticM))

initialize retryExceptionId : InternalExceptionId ←
  registerInternalExceptionId `lynth.interval.compositionRetry

def isRetryException : Exception → Bool
  | .internal id _ => id == retryExceptionId
  | _ => false

/-- Only numerical failures may request another precision or a longer prefix.
Structural and reification errors remain ordinary exceptions. -/
def requestRetry (reason : MessageData) : M α := do
  modifyThe RetryInfo fun _ => ⟨some reason⟩
  throw (.internal retryExceptionId {})

inductive SolveResult where
  | solved
  | unsupported (reason : MessageData)
  | retry (reason : MessageData)

structure SearchResult where
  proof? : Option Lean.Expr := none
  attempts : Nat := 0
  retryable : Bool := false
  reason? : Option MessageData := none

def ctxExpr (prec : Nat) : Lean.Expr := mkApp (mkConst ``Ctx.make) (toExpr (prec:Nat))
def ctxValid (prec : Nat) : Lean.Expr := mkApp (mkConst ``Ctx.make_valid) (toExpr (prec:Nat))

def context (bs : Array Bound) : MetaM Context := do
  let mut out : Context := {}
  for b in bs do
    let I := quoteIval b.interval
    let hh ← mkAppM ``Lynth.Interval.Composition.pushReal #[out.holds, b.proof]
    out := ⟨out.rc.push b.term .real, out.env.push .real b.interval,
      mkApp3 (mkConst ``IEnv.push) out.envExpr (toExpr Ty.real) I, hh⟩
  return out

def record (proof : Lean.Expr) : M Unit := do
  let proof ← instantiateMVars proof
  let ty ← instantiateMVars (← inferType proof)
  let scope := (← read).scope
  let outside (e : Lean.Expr) :=
    (e.find? fun e => e.isFVar && !scope.contains e.fvarId!).isSome
  unless proof.hasMVar || ty.hasMVar || outside proof || outside ty do
    modify (·.push proof)

def tacticProof (ty : Lean.Expr) (tac : Syntax) : TacticM Lean.Expr := do
  let previous ← getGoals
  let g ← mkFreshExprSyntheticOpaqueMVar ty
  try
    setGoals [g.mvarId!]
    evalTactic tac
    unless ← g.mvarId!.isAssigned do throwError "composition: auxiliary proof was not solved"
    return ← instantiateMVars g
  finally setGoals previous

mutual
/-- Expand finite binders before entering them. Substitution uses Lean's binder
operations, so a sum variable cannot capture a surrounding integration variable. -/
partial def expandFinite (t : Lean.Expr) (fuel : Nat := 256) : MetaM (Lean.Expr × Lean.Expr) := do
  if fuel == 0 then throwError "composition: finite expression is too deep"
  let mut t ← instantiateMVars t
  -- A balanced prefix introduces several index-shifting lambdas. Reduce the
  -- complete application before passing its body to the integral compiler.
  while t.headBeta != t do t := t.headBeta
  if t.getAppFn.isConstOf ``Finset.sum then
    let args := t.getAppArgs
    if args.size ≥ 2 then
      let s := args[args.size-2]!
      let f := args.back!
      if s.isAppOf ``Finset.range then
        if let some n ← Reify.ratValue? (α := q(ℕ)) s.appArg! then
          if n.den == 1 && 0 ≤ n.num && n.num ≤ 4096 then
            return ← expandRange f n.num.toNat (fuel-1)
  unless (t.find? fun e => e.isConstOf ``Finset.sum).isSome do return (t,← mkEqRefl t)
  match t with
  | .app f a =>
    let (f',hf) ← expandFinite f (fuel-1)
    let (a',ha) ← expandFinite a (fuel-1)
    return (mkApp f' a',← mkCongr hf ha)
  | .lam name ty body bi =>
    withLocalDecl name bi ty fun x => do
      let (v,h) ← expandFinite (body.instantiate1 x) (fuel-1)
      let fn ← mkLambdaFVars #[x] v
      let hfn ← mkAppM ``funext #[← mkLambdaFVars #[x] h]
      return (fn,hfn)
  | .mdata _ body => expandFinite body (fuel-1)
  | _ => return (t,← mkEqRefl t)

/-- A balanced addition tree keeps the depth logarithmic in the prefix length. -/
partial def expandRange (f : Lean.Expr) (n fuel : Nat) : MetaM (Lean.Expr × Lean.Expr) := do
  if fuel == 0 then throwError "composition: finite sum is too deep"
  if n == 0 then
    return (q((0 : ℝ)), ← mkAppM ``Lynth.Interval.Composition.sum_zero #[f])
  if n == 1 then
    let (v,h) ← expandFinite (mkApp f (toExpr (0 : Nat))) (fuel-1)
    return (v, ← mkAppM ``Lynth.Interval.Composition.sum_one #[f,h])
  let m := n / 2
  let g ← withLocalDeclD `j q(ℕ) fun j => do
    mkLambdaFVars #[j] (mkApp f (← mkAppM ``HAdd.hAdd #[toExpr m,j]))
  let (a,ha) ← expandRange f m (fuel-1)
  let (b,hb) ← expandRange g (n-m) (fuel-1)
  return (← mkAppM ``HAdd.hAdd #[a,b],
    ← mkAppM ``Lynth.Interval.Composition.sum_split #[f,toExpr m,toExpr (n-m),ha,hb])
end

/-- Convert numerical arithmetic back to an explicitly quoted interval, avoiding
large evaluator expressions in all subsequent certificate types. -/
def freeze (term : Lean.Expr) (I : Ival) (hp : Lean.Expr) : TacticM Bound := do
  let ty ← inferType hp
  let old := ty.getAppArgs[ty.getAppArgs.size-2]!
  let chk := mkApp2 (mkConst ``Lynth.Interval.Composition.covers) old (quoteIval I)
  let h ← certify chk 500
  let proof ← mkAppM ``Lynth.Interval.Composition.mem_of_covers #[hp,h]
  return ⟨term,I,proof⟩

/-- Real variables with rational bounds from the local context. This also
recognizes conjunctions such as membership in a closed interval. -/
partial def inequalities (h : Lean.Expr) (ty : Lean.Expr) (fuel := 4) :
    MetaM (Array (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  if fuel == 0 then return #[]
  match_expr ty with
  | LE.le α _ a b =>
    if ← isDefEq α q(ℝ) then return #[(a,b,h)] else return #[]
  | LT.lt α _ a b =>
    if ← isDefEq α q(ℝ) then return #[(a,b,← mkAppM ``le_of_lt #[h])] else return #[]
  | And a b =>
    return (← inequalities (← mkAppM ``And.left #[h]) a (fuel-1)) ++
      (← inequalities (← mkAppM ``And.right #[h]) b (fuel-1))
  | _ =>
    let ty' ← whnf ty
    if ty' == ty then return #[]
    inequalities h ty' (fuel-1)

def initialBoxes (prec : Nat) : TacticM (Array Bound) := do
  let lctx ← getLCtx
  let mut comparisons := #[]
  for decl in lctx do
    if ← isProp decl.type then
      comparisons := comparisons ++ (← inequalities decl.toExpr decl.type)
  let mut out := #[]
  for decl in lctx do
    unless decl.type.isConstOf ``Real do continue
    let x := decl.toExpr
    let mut lower : Option (ℚ × Lean.Expr × Lean.Expr) := none
    let mut upper : Option (ℚ × Lean.Expr × Lean.Expr) := none
    for (a,b,h) in comparisons do
      if b == x then
        if let some q ← Reify.ratValue? (α := q(ℝ)) a then
          if lower.all (fun v => v.1 < q) then lower := some (q,a,h)
      if a == x then
        if let some q ← Reify.ratValue? (α := q(ℝ)) b then
          if upper.all (fun v => q < v.1) then upper := some (q,b,h)
    if let (some (lo,a,ha),some (hi,b,hb)) := (lower,upper) then
      let aq : Q(ℝ) := a
      let bq : Q(ℝ) := b
      let lq : Q(ℚ) := toExpr lo
      let uq : Q(ℚ) := toExpr hi
      let some ea ← Reify.normNumEq? (α := q(ℝ)) aq q(($lq : ℝ)) | continue
      let some eb ← Reify.normNumEq? (α := q(ℝ)) bq q(($uq : ℝ)) | continue
      let h ← mkAppM ``Lynth.Interval.Composition.local_box
        #[toExpr prec,toExpr lo,toExpr hi,ea,eb,ha,hb]
      out := out.push (← freeze x (Ival.ofRats prec lo hi) h)
  return out

def safeName (e : Lean.Expr) : Name := match e with | .const n _ => n | _ => .anonymous

def hasAggregate (t : Lean.Expr) : Bool :=
  (t.find? fun e => e.isConstOf ``intervalIntegral || e.isConstOf ``MeasureTheory.integral ||
    e.isConstOf ``tsum || e.isConstOf ``Finset.sum).isSome

/-- Composition handles aggregates and their user aliases. Scalar range goals
are outside this handler's supported scope and yield before numerical search. -/
partial def hasAggregateOrAlias (t : Lean.Expr) (fuel : Nat := 16) : MetaM Bool := do
  if hasAggregate t then return true
  if fuel == 0 then return false
  let t := t.headBeta
  if let some value ← Reify.unfoldHead? t then
    if value != t && (← hasAggregateOrAlias value (fuel-1)) then return true
  match t with
  | .forallE _ _ body _ | .lam _ _ body _ => hasAggregateOrAlias body (fuel-1)
  | .letE _ _ value body _ =>
    return (← hasAggregateOrAlias value (fuel-1)) || (← hasAggregateOrAlias body (fuel-1))
  | .mdata _ body => hasAggregateOrAlias body (fuel-1)
  | .app .. =>
    for arg in t.getAppArgs do
      if ← hasAggregateOrAlias arg (fuel-1) then return true
    return false
  | _ => return false

def findFact (ty : Lean.Expr) : M Lean.Expr := do
  for pf in ← get do
    if ← isDefEq ty (← inferType pf) then return pf
  throwError "composition: missing convergence certificate for {ty}"

mutual
partial def enclose (t : Lean.Expr) (bs : Array Bound) (tol : ℚ) (fuel : Nat := 64) : M Bound := do
  let previous ← getThe RetryInfo
  let result ← encloseCore t bs tol fuel
  -- A successful fallback has resolved the earlier numerical failure. Do not
  -- let that failure turn a later unsupported expression into a retry.
  modifyThe RetryInfo fun _ => previous
  return result

partial def encloseCore (t : Lean.Expr) (bs : Array Bound) (tol : ℚ) (fuel : Nat) : M Bound := do
  let prec := (← read).precision
  if fuel == 0 then throwError "composition: expression recursion budget exhausted"
  let t := (← instantiateMVars t).headBeta
  -- Unrelated sibling bounds need not appear in this subexpression's proof
  -- environment. In particular, a long prefix must not accumulate all earlier
  -- integral certificates in every later integral certificate.
  let bs := bs.filter fun b => (t.find? (· == b.term)).isSome
  if let some b := bs.find? (·.term == t) then return b
  let (expanded,he) ← expandFinite t
  if expanded != t then
    let r ← enclose expanded bs tol (fuel-1)
    if let some req ← Integral.Nested.parse t then
      if let some req' ← Integral.Nested.parse expanded then
        let cvType := mkApp4 (mkConst ``Intgrl.NDomain.Converges)
          (Integral.Nested.quoteDomain req'.kind) req'.f req'.a req'.b
        -- A local binder's numerical enclosure can be used even when its
        -- convergence fact cannot be retained in the outer goal's scope.
        let cv? ← try pure (some (← findFact cvType)) catch _ => pure none
        if let some cv := cv? then
          let (_,hf) ← expandFinite req.f
          let (_,ha) ← expandFinite req.a
          let (_,hb) ← expandFinite req.b
          record (← mkAppM ``Lynth.Interval.Composition.transportConverges
            #[Integral.Nested.quoteDomain req.kind,hf,ha,hb,cv])
    return ⟨t,r.interval,← mkAppM ``Lynth.Interval.Composition.mem_transport #[he,r.proof]⟩
  if let some f ← seqArg? t ``tsum then return ← series t f bs tol (fuel-1)
  if let some req ← Integral.Nested.parse t then
    let saved ← liftM (saveState : TacticM Tactic.SavedState)
    let facts ← get
    try return ← fastIntegral t req bs tol
    catch _ => pure ()
    liftM saved.restore
    set facts
    if req.kind == .interval then return ← finiteIntegral t req bs tol (fuel-1)
    throwError "composition: no certified enclosure for this improper integral"
  let cx ← abstractLeaves t bs tol (fuel-1)
  let rc ← context cx
  try
    let r ← Reify.reify rc.rc t
    unless r.ty == .real do throwError "composition: expected a real expression"
    let e ← evalExprVal .real r.expr
    let I : Ival := e.eval (Ctx.make prec) rc.env
    unless I.isFinite do requestRetry "composition: expression enclosure is unbounded"
    let chk := mkAppN (mkConst ``Lynth.Interval.Composition.evalCheck)
      #[(ctxExpr prec),r.expr,rc.envExpr,quoteIval I]
    let h ← certify chk (max 500 (propositionWork (.lt e (.lit 0))))
    let p ← mkAppM ``Lynth.Interval.Composition.evalCheck_sound
      #[(ctxValid prec),h,rc.holds,r.proof]
    return ⟨t,I,p⟩
  catch ex =>
    if let some t' ← Reify.unfoldHead? t then
      if t' != t then return ← enclose t'.headBeta bs tol (fuel-1)
    throw ex

/-- Abstract only complete evaluated subexpressions, never a subterm containing
an unbound index. Each new arithmetic variable carries its membership proof. -/
partial def abstractLeaves (t : Lean.Expr) (bs : Array Bound) (tol : ℚ) (fuel : Nat) :
    M (Array Bound) := do
  if fuel == 0 then throwError "composition: abstraction depth exceeded"
  if (bs.find? (·.term == t)).isSome then return bs
  let reduced := t.headBeta
  if reduced != t && (← whnfR (← inferType t)).isConstOf ``Real then
    -- Applying an integrand introduces beta redexes below arithmetic nodes.
    -- Retain the original application as an atom with its certified value.
    let b ← enclose reduced bs (tol/16) (fuel-1)
    return bs.push {b with term := t}
  if hasAggregate t then
    if (← Integral.Nested.parse t.headBeta).isSome || (← seqArg? t.headBeta ``tsum).isSome then
      let b ← enclose t.headBeta bs (tol/16) (fuel-1)
      return bs.push {b with term := t}
  let head := t.getAppFn
  let args := t.getAppArgs
  -- Count arithmetic operands, rather than the implicit arguments in Lean's
  -- application spine. Expanded finite prefixes can contain many summands.
  if (head.isConstOf ``LT.lt || head.isConstOf ``LE.le || head.isConstOf ``And ||
      head.isConstOf ``Or || (binaryHead? (safeName head)).isSome) && args.size ≥ 2 then
    let bs ← abstractLeaves args[args.size-2]! bs tol (fuel-1)
    return ← abstractLeaves args.back! bs tol (fuel-1)
  if (unaryHead? (safeName head)).isSome && !args.isEmpty then
    return ← abstractLeaves args.back! bs tol (fuel-1)
  if !hasAggregate t then
    if (← whnfR (← inferType t)).isConstOf ``Real && !t.isMVar then
      let rc ← context bs
      try
        let _ ← Reify.reify rc.rc t
        return bs
      catch _ =>
        if let some value ← Reify.unfoldHead? t then
          if value != t then
            let r ← enclose value.headBeta bs (tol/16) (fuel-1)
            return bs.push {r with term := t}
    return bs
  match t with
  | .app f a =>
    let bs ← abstractLeaves f bs tol (fuel-1)
    abstractLeaves a bs tol (fuel-1)
  | .mdata _ b => abstractLeaves b bs tol (fuel-1)
  | _ => return bs

partial def ordinarySeries (t f : Lean.Expr) (bs : Array Bound) (tol : ℚ) (fuel : Nat) :
    M Bound := do
  let prec := (← read).precision
  withLocalDeclD `k q(ℕ) fun k => do
    let body := (mkApp f k).headBeta
    -- Independent integral/sum parameters are ordinary interval arguments.
    let cx ← abstractIndependent body k bs tol fuel
    let rc ← context cx
    let rr ← Reify.reify (rc.rc.push k .nat) body
    unless rr.ty == .real do throwError "composition: series body is not real"
    let hf ← mkLambdaFVars #[k] rr.proof
    let e ← evalExprVal .real rr.expr
    let mut result := none
    let mut numerical ← liftM <| tailNeedsPrecision body k prec
    unless summableShape
        (ParametricSeries.asy (Ctx.make prec) (seriesNs.getLast?.getD 8) rc.env e) do
      if numerical then requestRetry "composition: summable tail bound needs refinement"
      throwError "composition: no supported summable tail bound"
    for n in seriesNs do
      numerical := numerical || summableShape (ParametricSeries.asy (Ctx.make prec) n rc.env e)
      if let some I := Lynth.Interval.Composition.seriesEncl (Ctx.make prec) e rc.env n then
        result := some (n,I)
        let model := ParametricSeries.asy (Ctx.make prec) n rc.env e
        if let some T := Series.tailEncl (Ctx.make prec) n model then
          if let (some l,some u) := (T.lo,T.hi) then
            if u.toRat-l.toRat < tol/8 then break
    let some (n,I) := result | do
      if numerical then requestRetry "composition: summable tail bound needs refinement"
      throwError "composition: no supported summable tail bound"
    unless I.isFinite do requestRetry "composition: unbounded series enclosure"
    let chk := mkAppN (mkConst ``Lynth.Interval.Composition.seriesCheck)
      #[(ctxExpr prec),rr.expr,rc.envExpr,toExpr n,quoteIval I]
    let hc ← certify chk (checkCost prec (n*20+500))
    let p ← mkAppM ``Lynth.Interval.Composition.seriesCheck_sound #[(ctxValid prec),hc,rc.holds,hf]
    record (← mkAppM ``And.left #[p])
    return ⟨t,I,← mkAppM ``And.right #[p]⟩

partial def series (t f : Lean.Expr) (bs : Array Bound) (tol : ℚ) (fuel : Nat) : M Bound := do
  let saved ← liftM (saveState : TacticM Tactic.SavedState)
  let facts ← get
  try return ← ordinarySeries t f bs tol fuel
  catch ex =>
    if isRetryException ex || ex.isInterrupt then throw ex
  liftM saved.restore
  set facts
  integralSeries t f bs tol fuel

/-- Compose a tail certificate for the entire summand, including integral
subexpressions. Each algebraic operation uses the same asymptotic proof rules
as the ordinary series checker. -/
partial def integralSeries (t f : Lean.Expr) (bs : Array Bound) (tol : ℚ) (fuel : Nat) :
    M Bound := do
  let prec := (← read).precision
  withLocalDeclD `k q(ℕ) fun k => do
    let body := (mkApp f k).headBeta
    let mut result := none
    let mut numerical := false
    for n in seriesNs do
      let saved ← liftM (saveState : TacticM Tactic.SavedState)
      let facts ← get
      try
        let model ← tailModel body k bs n tol fuel
        numerical := numerical || summableShape model.value
        if let some T := Series.tailEncl (Ctx.make prec) n model.value then
          result := some (n,model,T)
          if let (some l,some u) := (T.lo,T.hi) then
            if u.toRat-l.toRat < tol/8 then break
      catch ex =>
        liftM saved.restore
        set facts
        unless isRetryException ex do throw ex
    let some (n,model,T) := result | do
      if numerical then requestRetry "composition: summable integral tail needs refinement"
      throwError "composition: no supported summable integral tail"
    let chk := mkAppN (mkConst ``Lynth.Interval.Composition.modelTailCheck)
      #[(ctxExpr prec),toExpr n,model.expr,quoteIval T]
    let tail ← mkAppM ``Lynth.Interval.Composition.modelTailCheck_sound
      #[(ctxValid prec),← certify chk 1000,model.proof]
    let fq : Q(ℕ → ℝ) := f
    let nq : Q(ℕ) := toExpr n
    let partialSum : Q(ℝ) := q(∑ j ∈ Finset.range $nq, $fq j)
    let P ← enclose partialSum bs (tol/8) fuel
    let pf ← mkAppM ``Lynth.Interval.Composition.prefix_tail #[toExpr prec,P.proof,tail]
    record (← mkAppM ``And.left #[pf])
    liftM <| freeze t (Ival.add prec P.interval T) (← mkAppM ``And.right #[pf])

partial def tailModel (t index : Lean.Expr) (bs : Array Bound) (N : Nat) (tol : ℚ)
    (fuel : Nat) : M TailModel := do
  let prec := (← read).precision
  if fuel == 0 then throwError "composition: tail recursion budget exhausted"
  let t := t.headBeta
  let saved ← liftM (saveState : TacticM Tactic.SavedState)
  let previousFacts ← get
  try
    let cx ← abstractIndependent t index bs tol fuel
    let rc ← context cx
    let rr ← Reify.reify (rc.rc.push index .nat) t
    let e ← evalExprVal .real rr.expr
    let value := ParametricSeries.asy (Ctx.make prec) N rc.env e
    unless value.isTop do
      let expr ← mkAppM ``ParametricSeries.asy #[(ctxExpr prec),toExpr N,rc.envExpr,rr.expr]
      let proof ← mkAppM ``Lynth.Interval.Composition.asy_source
        #[(ctxValid prec),rr.expr,toExpr N,rc.holds,← mkLambdaFVars #[index] rr.proof]
      return ⟨value,expr,proof⟩
  catch _ => pure ()
  liftM saved.restore
  set previousFacts
  if ← liftM <| tailNeedsPrecision t index prec then
    requestRetry "composition: asymptotic coefficient needs more precision"
  if let some req ← Integral.Nested.parse t then
    if req.kind != .interval then
      throwError "composition: no uniform tail model for this improper integration domain"
    let A ← endpointBox req.a index bs N tol (fuel-1)
    let B ← endpointBox req.b index bs N tol (fuel-1)
    let X := Ival.hull A.1 B.1
    let some L := (Ival.abs (Ival.sub prec B.1 A.1)).hi |
      requestRetry "composition: unbounded series integration domain"
    let lenCheck := mkApp2 (mkConst ``Ival.leB)
      (mkApp (mkConst ``Ival.abs) (mkApp3 (mkConst ``Ival.sub) (toExpr prec)
        (quoteIval B.1) (quoteIval A.1))) (mkApp (mkConst ``Ival.pt) (quoteDy L))
    let hlenCheck ← certify lenCheck 500
    let hlen ← withLocalDeclD `j q(ℕ) fun j => do
      let hjTy ← mkAppM ``LE.le #[toExpr N,j]
      withLocalDeclD `hj hjTy fun hj => do
        let h ← mkAppM ``Lynth.Interval.Composition.lengthCheck_sound
          #[toExpr prec,hlenCheck,mkApp2 A.2 j hj,mkApp2 B.2 j hj]
        mkLambdaFVars #[j,hj] h
    let aFn ← mkLambdaFVars #[index] req.a
    let bFn ← mkLambdaFVars #[index] req.b
    let hdom ← withLocalDeclD `j q(ℕ) fun j => do
      let hjTy ← mkAppM ``LE.le #[toExpr N,j]
      withLocalDeclD `hj hjTy fun hj => do
        withLocalDeclD `x q(ℝ) fun x => do
          let hxTy ← mkAppM ``Membership.mem #[← mkAppM ``Set.uIcc #[mkApp aFn j,mkApp bFn j],x]
          withLocalDeclD `hx hxTy fun hx => do
            let h ← mkAppM ``Lynth.Interval.Composition.hull_between
              #[mkApp2 A.2 j hj,mkApp2 B.2 j hj,hx]
            let r ← liftM <| freeze x X h
            mkLambdaFVars #[j,hj,x,hx] r.proof
    let g ← mkLambdaFVars #[index] req.f
    let hmTy ← withLocalDeclD `j q(ℕ) fun j => do
      mkForallFVars #[j] (← mkAppM ``Measurable #[mkApp g j])
    let hm ← liftM <| tacticProof hmTy (← `(tactic| intro j; fun_prop))
    let (m,hb) ← withLocalDeclD `x q(ℝ) fun x => do
      let hxTy ← mkAppM ``Membership.mem #[quoteIval X,x]
      withLocalDeclD `hx hxTy fun hx => do
        let m ← tailModel (mkApp req.f x).headBeta index (bs.push ⟨x,X,hx⟩) N tol (fuel-1)
        return (m,← mkLambdaFVars #[x,hx] m.proof)
    let value := Lynth.Interval.Composition.integralAsy prec L m.value
    let expr := mkApp3 (mkConst ``Lynth.Interval.Composition.integralAsy)
      (toExpr prec) (quoteDy L) m.expr
    let proof ← mkAppM ``Lynth.Interval.Composition.integralAsy_sound #[toExpr prec,hm,hlen,hdom,hb]
    return ⟨value,expr,proof⟩
  let head := t.getAppFn
  let args := t.getAppArgs
  if head.isConstOf ``HPow.hPow && args.size ≥ 2 then
    let exponent := args.back!
    if (← whnfR (← inferType exponent)).isConstOf ``Nat then
      if let some n ← Reify.ratValue? (α := q(ℕ)) exponent then
        if n.den == 1 && 0 ≤ n.num then
          let m ← tailModel args[args.size-2]! index bs N tol (fuel-1)
          let n := n.num.toNat
          return ⟨Lynth.Interval.Composition.powerModel prec N m.value n,
            mkApp4 (mkConst ``Lynth.Interval.Composition.powerModel)
              (toExpr prec) (toExpr N) m.expr (toExpr n),
            ← mkAppM ``Lynth.Interval.Composition.powerModel_sound
              #[toExpr prec,toExpr N,toExpr n,m.proof]⟩
  if let some op := unaryHead? (safeName head) then
    let m ← tailModel args.back! index bs N tol (fuel-1)
    if op == .neg then
      return ⟨RAsy.neg m.value,mkApp (mkConst ``RAsy.neg) m.expr,
        ← mkAppM ``RAsy.neg_holds #[m.proof]⟩
    if op == .inv then
      return ⟨RAsy.inv prec m.value,mkApp2 (mkConst ``RAsy.inv) (toExpr (prec:Nat)) m.expr,
        ← mkAppM ``Lynth.Interval.Composition.model_inv #[toExpr (prec:Nat),toExpr N,m.proof]⟩
    if op == .abs then
      return ⟨RAsy.abs m.value,mkApp (mkConst ``RAsy.abs) m.expr,
        ← mkAppM ``RAsy.abs_holds #[m.proof]⟩
  if let some op := binaryHead? (safeName head) then
    let a ← tailModel args[args.size-2]! index bs N tol (fuel-1)
    let mut b ← tailModel args.back! index bs N tol (fuel-1)
    if op == .sub then
      b := ⟨RAsy.neg b.value,mkApp (mkConst ``RAsy.neg) b.expr,← mkAppM ``RAsy.neg_holds #[b.proof]⟩
    if op == .div then
      b := ⟨RAsy.inv prec b.value,mkApp2 (mkConst ``RAsy.inv) (toExpr (prec:Nat)) b.expr,
        ← mkAppM ``Lynth.Interval.Composition.model_inv #[toExpr (prec:Nat),toExpr N,b.proof]⟩
    let (value,name,proofName) ←
      if op == .add || op == .sub then
        pure (RAsy.add prec N a.value b.value,``RAsy.add,``Lynth.Interval.Composition.model_add)
      else if op == .mul || op == .div then
        pure (RAsy.mul prec N a.value b.value,``RAsy.mul,``Lynth.Interval.Composition.model_mul)
      else throwError "composition: unsupported asymptotic binary operation"
    let expr := mkApp4 (mkConst name) (toExpr (prec:Nat)) (toExpr N) a.expr b.expr
    let proof ← mkAppM proofName #[toExpr (prec:Nat),toExpr N,a.proof,b.proof]
    -- Subtraction and division are definitionally addition/negation and multiplication/inversion.
    let target ← mkLambdaFVars #[index] t
    let ty ← mkAppM ``RAsy.Holds #[toExpr N,target,expr]
    unless ← isDefEq (← inferType proof) ty do
      let targetEq ← withLocalDeclD `j q(ℕ) fun j => do
        let instantiated := t.replaceFVar index j
        let proofTy ← inferType proof
        let fn := proofTy.getAppArgs[1]!
        let rhs := mkApp fn j
        let he ← liftM <| tacticProof (← mkEq instantiated rhs)
          (← `(tactic| simp only [sub_eq_add_neg, div_eq_mul_inv]))
        mkLambdaFVars #[j] he
      let proof ← mkAppM ``Lynth.Interval.Composition.model_eq #[proof,targetEq]
      return ⟨value,expr,proof⟩
    return ⟨value,expr,proof⟩
  let (expanded,he) ← expandFinite t
  if expanded != t then
    let m ← tailModel expanded index bs N tol (fuel-1)
    let proof ← mkAppM ``Lynth.Interval.Composition.model_eq
      #[m.proof,← mkLambdaFVars #[index] he]
    return {m with proof := proof}
  if let some t' ← Reify.unfoldHead? t then
    if t' != t then return ← tailModel t'.headBeta index bs N tol (fuel-1)
  throwError "composition: no tail model for {t}"

/-- Enclose an endpoint for every index in a summation tail. Bounded
index-dependent endpoints use their asymptotic model, not a sample index. -/
partial def endpointBox (t index : Lean.Expr) (bs : Array Bound) (N : Nat)
    (tol : ℚ) (fuel : Nat) : M (Ival × Lean.Expr) := do
  let prec := (← read).precision
  if !(t.containsFVar index.fvarId!) then
    let r ← enclose t bs (tol/64) fuel
    let hkTy ← mkAppM ``LE.le #[toExpr N,index]
    let proof ← withLocalDeclD `hk hkTy fun hk => mkLambdaFVars #[index,hk] r.proof
    return (r.interval,proof)
  let m ← tailModel t index bs N tol fuel
  let some I := Lynth.Interval.Composition.uniformEncl (Ctx.make prec) N m.value |
    requestRetry "composition: cannot bound an index-dependent integral endpoint uniformly"
  let chk := mkAppN (mkConst ``Lynth.Interval.Composition.uniformCheck)
    #[(ctxExpr prec),toExpr N,m.expr,quoteIval I]
  let proof ← mkAppM ``Lynth.Interval.Composition.uniformCheck_sound
    #[(ctxValid prec),← certify chk 1000,m.proof]
  return (I,proof)

partial def abstractIndependent (t index : Lean.Expr) (bs : Array Bound) (tol : ℚ)
    (fuel : Nat) : M (Array Bound) := do
  if fuel == 0 then throwError "composition: series abstraction depth exceeded"
  if (bs.find? (·.term == t)).isSome then return bs
  if !hasAggregate t then return bs
  if !(t.containsFVar index.fvarId!) then return ← abstractLeaves t bs tol fuel
  match t with
  | .app f a =>
    let bs ← abstractIndependent f index bs tol (fuel-1)
    abstractIndependent a index bs tol (fuel-1)
  | .mdata _ b => abstractIndependent b index bs tol (fuel-1)
  | _ => return bs

partial def fastIntegral (t : Lean.Expr) (req : Integral.Nested.Request)
    (bs : Array Bound) (tol : ℚ) : M Bound := do
  return (← fastIntegralPair t req bs tol).1

partial def fastIntegralPair (t : Lean.Expr) (req : Integral.Nested.Request)
    (bs : Array Bound) (tol : ℚ) : M (Bound × Lean.Expr) := do
  let prec := (← read).precision
  let r ← Integral.Nested.compile (bs.map (·.term)) t
  let env := bs.map (·.interval)
  let broad := (bs.zipIdx).any fun (b,i) =>
    r.term.uses i && (match b.interval.lo,b.interval.hi with
      | some l,some u => u.toRat-l.toRat > tol | _,_ => true)
  let cert ←
    if broad && (Lynth.Interval.Composition.integralEncl (Ctx.make prec) r.term env {}).isSome then
      pure ({} : Integral.Nested.Cert)
    else do
      let (some (_,s)) := (Integral.Nested.evaluate (Ctx.make prec) r.term env (tol/16)).run {} |
        requestRetry "composition: adaptive integral search failed"
      pure (⟨s.pool.tables,s.entries⟩ : Integral.Nested.Cert)
  let some I := Lynth.Interval.Composition.integralEncl (Ctx.make prec) r.term env cert |
    requestRetry "composition: integral certificate replay failed"
  let mut hx := mkConst ``Lynth.Interval.Composition.emptyEnvMem
  for b in bs do hx ← mkAppM ``Integral.Nested.EnvMem.push #[hx,b.proof]
  let chk := mkAppN (mkConst ``Lynth.Interval.Composition.integralCheck)
    #[(ctxExpr prec),Integral.Nested.quoteExpr r.term,
      Integral.Nested.arrayExpr (mkConst ``Ival) (env.map quoteIval),
      Integral.Nested.quoteCert cert,quoteIval I]
  let hc ← certify chk (NI.cost prec r.term cert)
  let p ← mkAppM ``Lynth.Interval.Composition.integralCheck_sound #[(ctxValid prec),hc,hx,r.proof]
  -- Extract the root integral's convergence assertion.
  let root ← mkAppM ``And.left #[p]
  let ra ← Integral.Nested.compile (bs.map (·.term)) req.a
  let rb ← Integral.Nested.compile (bs.map (·.term)) req.b
  let hf ← withLocalDeclD `x q(ℝ) fun x => do
    let r ← Integral.Nested.compile ((bs.map (·.term)).push x) (mkApp req.f x).headBeta
    mkLambdaFVars #[x] r.proof
  let cv ← mkAppM ``Lynth.Interval.Composition.integralConverges #[root,hf,ra.proof,rb.proof]
  record cv
  return (⟨t,I,← mkAppM ``And.right #[p]⟩,cv)

partial def finiteIntegral (t : Lean.Expr) (req : Integral.Nested.Request)
    (bs : Array Bound) (tol : ℚ) (fuel : Nat) : M Bound := do
  let saved ← liftM (saveState : TacticM Tactic.SavedState)
  let facts ← get
  try return ← linearIntegral t req bs tol fuel
  catch _ => pure ()
  liftM saved.restore
  set facts
  try return ← tsumIntegral t req bs tol fuel
  catch _ => pure ()
  liftM saved.restore
  set facts
  let g ← withLocalDeclD `u q(ℝ) fun u => do
    let width ← mkAppM ``HSub.hSub #[req.b,req.a]
    let x ← mkAppM ``HAdd.hAdd #[req.a,← mkAppM ``HMul.hMul #[width,u]]
    mkLambdaFVars #[u] (← mkAppM ``HMul.hMul #[width,mkApp req.f x])
  let hmTy ← mkAppM ``Measurable #[g]
  let hm ← liftM <| tacticProof hmTy (← `(tactic| fun_prop))
  let (I,p) ← panels g hm bs 0 1 tol fuel 0
  let p ← mkAppM ``Lynth.Interval.Composition.unit_panel #[p]
  let he ← mkAppM ``Lynth.Interval.Composition.affine_integral #[req.f,req.a,req.b]
  let mem ← mkAppM ``Lynth.Interval.Composition.mem_transport #[he,← mkAppM ``And.right #[p]]
  let conv ← mkAppOptM ``Lynth.Interval.Composition.affine_integrable
    #[some req.f,some req.a,some req.b,some (← mkAppM ``And.left #[p])]
  record conv
  return ← liftM <| freeze t I mem

/-- Linearity preserves the fast backend for linear arithmetic around a
series or another compositional integrand. Local facts are scoped to this call. -/
partial def linearIntegral (t : Lean.Expr) (req : Integral.Nested.Request)
    (bs : Array Bound) (tol : ℚ) (fuel : Nat) : M Bound := do
  let prec := (← read).precision
  let previous ← get
  let scope := (← getLCtx).foldl (fun acc d => acc.push d.fvarId) #[]
  let (result,conv) ← try
    withReader (fun cfg => {cfg with scope := scope}) do
      withLocalDeclD `x q(ℝ) fun x => do
        let body := (mkApp req.f x).headBeta
        let args := body.getAppArgs
        let some op := binaryHead? (safeName body.getAppFn) | throwError "not a linear integrand"
        unless args.size ≥ 2 do throwError "incomplete integrand"
        let a := args[args.size-2]!
        let b := args.back!
        let build (body : Lean.Expr) : M (Bound × Lean.Expr) := do
          let f ← mkLambdaFVars #[x] body
          let fq : Q(ℝ → ℝ) := f
          let aq : Q(ℝ) := req.a
          let bq : Q(ℝ) := req.b
          let value : Q(ℝ) := q(∫ y in $aq..$bq, $fq y)
          let r ← enclose value bs (tol/8) fuel
          let conv := mkApp4 (mkConst ``Intgrl.NDomain.Converges)
            (Integral.Nested.quoteDomain .interval) f req.a req.b
          return (r,← findFact conv)
        let (I,pf) ←
          if op == .add || op == .sub then do
            let A ← build a
            let B ← build b
            let name := if op == .add then ``Lynth.Interval.Composition.integral_add_bounds
              else ``Lynth.Interval.Composition.integral_sub_bounds
            let p ← mkAppM name #[toExpr prec,A.2,B.2,A.1.proof,B.1.proof]
            pure ((if op == .add then Ival.add else Ival.sub) prec A.1.interval B.1.interval,p)
          else if op == .mul && !(a.containsFVar x.fvarId!) then do
            let C ← enclose a bs (tol/8) fuel
            let B ← build b
            let p ← mkAppM ``Lynth.Interval.Composition.integral_scale_bounds
              #[toExpr prec,C.proof,B.2,B.1.proof]
            pure (Ival.mul prec C.interval B.1.interval,p)
          else if (op == .mul || op == .div) && !(b.containsFVar x.fvarId!) then do
            let A ← build a
            let C ← enclose b bs (tol/8) fuel
            let name := if op == .mul then ``Lynth.Interval.Composition.integral_scale_right_bounds
              else ``Lynth.Interval.Composition.integral_div_bounds
            let p ← mkAppM name #[toExpr prec,A.2,A.1.proof,C.proof]
            pure ((if op == .mul then Ival.mul else Ival.div) prec A.1.interval C.interval,p)
          else throwError "not a linear integrand"
        let r ← liftM <| freeze t I (← mkAppM ``And.right #[pf])
        return (r,← mkAppM ``And.left #[pf])
    finally set previous
  record conv
  return result

/-- Truncate a series uniformly on the integration domain, integrate its
finite prefix with the existing Gauss checker, then add a certified tail error. -/
partial def tsumIntegral (t : Lean.Expr) (req : Integral.Nested.Request)
    (bs : Array Bound) (tol : ℚ) (fuel : Nat) : M Bound := do
  let prec := (← read).precision
  let A ← enclose req.a bs (tol/prec) fuel
  let B ← enclose req.b bs (tol/prec) fuel
  let X := Ival.hull A.interval B.interval
  let some L := (Ival.abs (Ival.sub prec B.interval A.interval)).hi |
    requestRetry "composition: unbounded series integration domain"
  let lenCheck := mkApp2 (mkConst ``Ival.leB)
    (mkApp (mkConst ``Ival.abs) (mkApp3 (mkConst ``Ival.sub) (toExpr (prec:Nat))
      (quoteIval B.interval) (quoteIval A.interval))) (mkApp (mkConst ``Ival.pt) (quoteDy L))
  let hlen ← mkAppM ``Lynth.Interval.Composition.lengthCheck_sound
    #[toExpr prec,← certify lenCheck 500,A.proof,B.proof]
  let (n,T,partialFn,htail) ← withLocalDeclD `x q(ℝ) fun x => do
    let body := (mkApp req.f x).headBeta
    let some f ← seqArg? body ``tsum | throwError "composition: integrand is not a series"
    let hxTy ← mkAppM ``Membership.mem #[← mkAppM ``Set.uIcc #[req.a,req.b],x]
    withLocalDeclD `hx hxTy fun hx => do
      let hxbox ← mkAppM ``Lynth.Interval.Composition.hull_between #[A.proof,B.proof,hx]
      let xb ← liftM <| freeze x X hxbox
      let rc ← context (bs.push xb)
      let (expr,hf) ← withLocalDeclD `k q(ℕ) fun k => do
        let rr ← Reify.reify (rc.rc.push k .nat) (mkApp f k).headBeta
        return (rr.expr,← mkLambdaFVars #[k] rr.proof)
      let e ← evalExprVal .real expr
      let mut result := none
      let mut numerical ← withLocalDeclD `k q(ℕ) fun k =>
        liftM <| tailNeedsPrecision (mkApp f k).headBeta k prec
      for n in seriesNs do
        let model := ParametricSeries.asy (Ctx.make prec) n rc.env e
        numerical := numerical || summableShape model
        let some T := Series.tailEncl (Ctx.make prec) n model | continue
        if let some D := (Ival.abs T).hi then
          result := some (n,T)
          if D.toRat*(1+L.toRat) < tol/32 then break
      let some (n,T) := result | do
        if numerical then requestRetry "composition: uniform series tail needs refinement"
        throwError "composition: no supported uniform summable series tail"
      let chk := mkAppN (mkConst ``Lynth.Interval.Composition.remainderCheck)
        #[(ctxExpr prec),expr,rc.envExpr,toExpr n,quoteIval T]
      let h ← mkAppM ``Lynth.Interval.Composition.remainderCheck_sound
        #[(ctxValid prec),← certify chk 1000,rc.holds,hf]
      let fq : Q(ℕ → ℝ) := f
      let nq : Q(ℕ) := toExpr n
      let pp : Q(ℝ) := q(∑ k ∈ Finset.range $nq, $fq k)
      return (n,T,← mkLambdaFVars #[x] pp,
        ← mkLambdaFVars #[x,hx] (← mkAppM ``And.right #[h]))
  let (p,heq) ← expandFinite partialFn
  let htail ← mkAppM ``Lynth.Interval.Composition.rewrite_remainder #[heq,htail]
  let pq : Q(ℝ → ℝ) := p
  let aq : Q(ℝ) := req.a
  let bq : Q(ℝ) := req.b
  let target : Q(ℝ) := q(∫ x in $aq..$bq, $pq x)
  let some pReq ← Integral.Nested.parse target |
    throwError "composition: invalid finite prefix integral"
  let (P,hint) ← fastIntegralPair target pReq bs (tol/4)
  let hm ← liftM <| tacticProof (← mkAppM ``Measurable #[req.f]) (← `(tactic| fun_prop))
  let hmp ← liftM <| tacticProof (← mkAppM ``Measurable #[p]) (← `(tactic| fun_prop))
  let some D := (Ival.abs T).hi | requestRetry "composition: unbounded uniform remainder"
  let hd ← mkEqRefl (mkApp2 (mkConst ``Option.some [0]) (mkConst ``Dy) (quoteDy D))
  let result ← mkAppM ``Lynth.Interval.Composition.integral_remainder
    #[toExpr prec,hm,hmp,hint,P.proof,hlen,htail,hd]
  record (← mkAppM ``And.left #[result])
  trace[lynth.interval] "composition: integrated {n} terms with a certified infinite remainder"
  liftM <| freeze t (Ival.widen prec P.interval (Dy.mulU prec D L)) (← mkAppM ``And.right #[result])

partial def panels (f hm : Lean.Expr) (bs : Array Bound) (a b tol : ℚ)
    (fuel depth : Nat) : M (Ival × Lean.Expr) := do
  let prec := (← read).precision
  let r ← withLocalDeclD `x q(ℝ) fun x => do
    let qa : Q(ℚ) := toExpr a
    let qb : Q(ℚ) := toExpr b
    let set ← mkAppM ``Set.Icc #[q(($qa : ℝ)),q(($qb : ℝ))]
    let ht ← mkAppM ``Membership.mem #[set,x]
    withLocalDeclD `hx ht fun hx => do
      let hp ← mkAppM ``Lynth.Interval.Composition.mem_box #[toExpr prec,hx]
      let X := Ival.ofRats prec a b
      let xb ← liftM <| freeze x X hp
      let r ← enclose (mkApp f x).headBeta (bs.push xb) (tol/16) fuel
      return (r.interval,← mkLambdaFVars #[x,hx] r.proof)
  let (some lo,some hi) := (r.1.lo,r.1.hi) | requestRetry "composition: panel is unbounded"
  let I := Ival.mul prec (Ival.ofRat prec (b-a)) r.1
  let width := match I.lo,I.hi with | some l,some u => u.toRat-l.toRat | _,_ => tol+1
  if width > tol && depth < 10 then
    let m := (a+b)/2
    let l ← panels f hm bs a m (tol/2) fuel (depth+1)
    let r ← panels f hm bs m b (tol/2) fuel (depth+1)
    let p ← mkAppM ``Lynth.Interval.Composition.join #[toExpr prec,l.2,r.2]
    return (Ival.add prec l.1 r.1,p)
  let hab ← liftM <| tacticProof (← mkAppM ``LE.le #[toExpr a,toExpr b]) (← `(tactic| norm_num))
  let hlo ← mkEqRefl (mkApp2 (mkConst ``Option.some [0]) (mkConst ``Dy) (quoteDy lo))
  let hhi ← mkEqRefl (mkApp2 (mkConst ``Option.some [0]) (mkConst ``Dy) (quoteDy hi))
  let p ← mkAppM ``Lynth.Interval.Composition.panel #[toExpr prec,hm,hab,r.2,hlo,hhi]
  return (I,p)
end

partial def prove (ty : Lean.Expr) (tol : ℚ := 1 / 100000)
    (known : Array Bound := #[]) : M Lean.Expr := do
  let prec := (← read).precision
  let (expanded,he) ← expandFinite ty
  if expanded != ty then
    return ← mkEqMP (← mkEqSymm he) (← prove expanded tol known)
  let bs ← abstractLeaves ty ((← liftM <| initialBoxes prec) ++ known) tol 128
  let rc ← context bs
  let r ← Reify.reifyProp rc.rc ty
  let p ← evalPropExpr r.expr
  match p.eval3 (Ctx.make prec) rc.env with
  | .yes => pure ()
  | .no => throwError "composition: comparison is false on the current enclosure"
  | .unk => requestRetry "composition: comparison not separated"
  let chk := mkApp3 (mkConst ``PropExpr.check) (ctxExpr prec) r.expr rc.envExpr
  let h ← certify chk (max 500 (propositionWork p))
  mkAppM ``Lynth.Interval.Composition.propCheck_sound #[(ctxValid prec),h,rc.holds,r.proof]

/-- Keep numerical retry requests local to one atomic goal. They survive
speculative backend fallbacks, but cannot mask an unsupported sibling goal. -/
def solveAtomicCore (g : MVarId) (ty : Lean.Expr) : M SolveResult := do
  let casts := subterms ty |>.filter (fun e => e.isAppOfArity ``Rat.cast 3 && e.appArg!.isMVar)
  for cast in casts do
    let x := cast.appArg!
    for anchor in anchorsFor x ty do
      try
        let tol ← minTol ty
        let r ← enclose anchor (← liftM <| initialBoxes (← read).precision) (tol/16)
        let (some l,some u) := (r.interval.lo,r.interval.hi) | continue
        for q in shortRats ((l.toRat+u.toRat)/2) (tol/1024) do
          let saved ← liftM (saveState : TacticM Tactic.SavedState)
          let facts ← get
          if ← isDefEq x (toExpr q) then
            try
              let pf ← prove (← instantiateMVars ty) tol #[r]
              g.assign pf
              return .solved
            catch ex =>
              if ex.isInterrupt then throw ex
          liftM saved.restore
          set facts
      catch ex =>
        if ex.isInterrupt then throw ex
  try
    let pf ← prove ty (← minTol ty)
    g.assign pf
    return .solved
  catch ex =>
    if ex.isInterrupt then throw ex
    if let some reason := (← getThe RetryInfo).reason? then return .retry reason
    return .unsupported ex.toMessageData

def solveAtomic (g : MVarId) (ty : Lean.Expr) : M SolveResult := do
  let previous ← getThe RetryInfo
  modifyThe RetryInfo fun _ => {}
  try solveAtomicCore g ty
  finally modifyThe RetryInfo fun _ => previous

partial def solve (g : MVarId) (fuel : Nat := 16) : M SolveResult := g.withContext do
  let scope := (← getLCtx).foldl (fun acc decl => acc.push decl.fvarId) #[]
  withReader (fun cfg => {cfg with scope := scope}) do
    if ← g.isAssigned then return .solved
    if fuel == 0 then return .unsupported "composition: goal recursion budget exhausted"
    let ty := (← instantiateMVars (← g.getType)).headBeta
    if ty.isForall then
      let (_,child) ← g.intro1
      return ← solve child (fuel-1)
    for pf in ← get do
      if ← isDefEq ty (← inferType pf) then g.assign pf; return .solved
    let atomic ←
      if (← isProp ty) && !ty.isAppOf ``And then solveAtomic g ty
      else pure (.unsupported m!"composition: unsupported goal {ty}")
    if atomic matches .solved then return .solved
    let ty ← whnf ty
    let .const name _ := ty.getAppFn | return atomic
    let ctors ←
      if name == ``And then pure [``And.intro] else
      if name == ``Subtype then pure [``Subtype.mk] else
      if name == ``PSum then pure [``PSum.inl,``PSum.inr] else return atomic
    let mut retry? : Option MessageData := match atomic with
      | .retry reason => some reason
      | _ => none
    let mut unsupported := m!"composition: unsupported goal {ty}"
    for ctor in ctors do
      let saved ← liftM (saveState : TacticM Tactic.SavedState)
      let facts ← get
      try
        let children ← g.apply (← mkConstWithFreshMVarLevels ctor)
        let mut proofs := []; let mut data := []
        for child in children do
          if ← isProp (← child.getType) then proofs := child::proofs else data := data++[child]
        let mut ok := true
        let mut ctorRetry? : Option MessageData := none
        for child in proofs++data do
          match ← solve child (fuel-1) with
          | .solved => pure ()
          | .unsupported reason =>
            unsupported := reason
            ctorRetry? := none
            ok := false
            break
          | .retry reason =>
            ctorRetry? := some reason
            ok := false
            -- Later fields may need a witness or convergence fact produced by
            -- this proof, so defer them until this field can be solved.
            break
        if ok then return .solved
        if let some reason := ctorRetry? then retry? := some reason
      catch ex =>
        if ex.isInterrupt then throw ex
        unsupported := ex.toMessageData
      liftM saved.restore
      set facts
    if let some reason := retry? then return .retry reason
    return .unsupported unsupported

/-- Search diagnostics expose whether a failure was structural or numerical.
Unsupported goals leave after their first attempt; only explicit numerical
failures advance the precision schedule. -/
def search (ty : Lean.Expr) : TacticM SearchResult := do
  let saved ← saveState
  unless ← hasAggregateOrAlias ty do
    saved.restore
    return { reason? := some "composition: unsupported goal without integral or summation content" }
  let mut tol : ℚ := 1
  for T in tolerances ty do
    unless T.hasLooseBVars || T.hasFVar || T.hasMVar do
      tol := min tol (← tolLower T)
  let ratio := if tol > 0 then max 1 (1/tol) else 1
  let hint := max 64 (ratio.num.natAbs.log2 + 32 - ratio.den.log2)
  let maxPrec := lynth.interval.maxPrec.get (← getOptions)
  let schedule := precSchedule maxPrec
  let start := min hint (schedule.getLast?.getD 64)
  let mut attempts := 0
  let mut reason? := none
  for prec in schedule do
    if prec < start then continue
    attempts := attempts + 1
    try
      let g ← mkFreshExprSyntheticOpaqueMVar ty
      let outcome ← (((solve g.mvarId!).run {precision := prec}).run' #[]).run' {}
      match outcome with
      | .solved => return { proof? := some (← instantiateMVars g), attempts }
      | .unsupported reason =>
        saved.restore
        return { attempts, reason? := some reason }
      | .retry reason => reason? := some reason
    catch ex =>
      saved.restore
      if ex.isInterrupt then throw ex
      return { attempts, reason? := some ex.toMessageData }
    saved.restore
  return { attempts, retryable := true, reason? }

def run? (ty : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let result ← search ty
  if let some reason := result.reason? then
    if result.retryable then trace[lynth.interval] "composition precision exhausted: {reason}"
    else trace[lynth.interval] "composition unsupported: {reason}"
  return result.proof?

end Lynth.Interval.Goals.Composition
