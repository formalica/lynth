import Lynth.Interval.Goals.Approx
import Lynth.Interval.Series.Cert

/-!
# Infinite-series goals

* `{x : ℚ // Summable f ∧ |tsum f - ↑x| < tol}`
* `A ⊕' B` (e.g. `SeriesSummabilityResult f tol`): left branch first, then right
* `¬ Summable f`

`f : ℕ → ℝ` (a lambda or a user definition).  The body `f k` is reified with
`k` as the innermost natural variable; the certificate is `seriesCheck` /
`divergeCheck` (`Lynth/Interval/Series/Cert.lean`).  The number of explicitly
summed terms `N` and the witness are found natively.
See `docs/interval/08-series.md`.
-/

namespace Lynth.Interval.Series

theorem subtype_of_check {f : ℕ → ℝ} {tol : ℝ} {c : Ctx} (hc : c.Valid) {body tolE : Expr .real}
    {N : ℕ} {q : ℚ} (hf : ∀ k, f k = body.denote (({} : SEnv).push .nat k))
    (htol : tol = tolE.denote {}) (h : seriesCheck c body N q tolE = true) :
    Summable f ∧ |tsum f - q| < tol := by
  obtain rfl : f = fun k => body.denote (({} : SEnv).push .nat k) := funext hf
  subst htol
  exact seriesCheck_sound hc h

theorem not_summable_of_check {f : ℕ → ℝ} {c : Ctx} (hc : c.Valid) {body : Expr .real} {N : ℕ}
    (hf : ∀ k, f k = body.denote (({} : SEnv).push .nat k)) (h : divergeCheck c body N = true) :
    ¬ Summable f := by
  obtain rfl : f = fun k => body.denote (({} : SEnv).push .nat k) := funext hf
  exact divergeCheck_sound hc h

end Lynth.Interval.Series

namespace Lynth.Interval.Goals

open Lean Meta Elab Tactic Reify

/-- the function argument of `Summable f` / `tsum f` (`f : ℕ → ℝ`) -/
def seqArg? (e : Lean.Expr) (head : Name) : MetaM (Option Lean.Expr) := do
  unless e.getAppFn.isConstOf head do return none
  let fty ← mkArrow (mkConst ``Nat) (mkConst ``Real)
  for a in e.getAppArgs do
    if ← isDefEq (← inferType a) fty then return some a
  return none

/-- reify the series body: `(bodyE, ∀ k, f k = bodyE.denote ({}.push .nat k))` -/
def reifyBody (f : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  withLocalDeclD `k (mkConst ``Nat) fun k => do
    let t := (mkApp f k).headBeta
    let rc : RCtx := ({} : RCtx).push k .nat
    let r ← reify rc t
    unless r.ty == .real do throwError "lynth interval: series body is not real"
    return (r.expr, ← mkLambdaFVars #[k] r.proof)

/-- candidate numbers of explicitly summed terms -/
def seriesNs : List Nat := [8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]

/-- `{x : ℚ // Summable f ∧ |tsum f - ↑x| < tol}` -/
def proveSeriesSubtype? (goalTy : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let_expr Subtype α p := goalTy | return none
  unless (← whnfR α).isConstOf ``Rat do return none
  let .lam n _ pbody _ ← whnfR p | return none
  let found ← withLocalDeclD n α fun x => do
    let P := pbody.instantiate1 x
    let_expr And S I := P | return none
    let some f ← seqArg? S ``Summable | return none
    let_expr LT.lt _ _ _ tol := I | return none
    if tol.hasFVar then return none
    return some (f, tol)
  let some (f, tol) := found | return none
  let (bodyE, hbody) ← reifyBody f
  let rt ← reify {} tol
  unless rt.ty == .real do return none
  let body ← evalExprVal .real bodyE
  let tolV ← evalExprVal .real rt.expr
  let tl ← tolLower tol
  let maxPrec := lynth.interval.maxPrec.get (← getOptions)
  for prec in precSchedule maxPrec do
    let c := Ctx.make prec
    for N in seriesNs do
      let some S := Series.seriesEncl c body N | continue
      let (some lo, some hi) := (S.lo, S.hi) | continue
      let w := hi.toRat - lo.toRat
      if w ≥ tl then continue
      let m := (lo.toRat + hi.toRat) / 2
      for q in shortRats m (tl / 2 - w / 2) do
        unless Series.seriesCheck c body N q tolV do continue
        trace[lynth.interval] "series: N = {N}, prec = {prec}, q = {q}"
        let chk := mkAppN (mkConst ``Series.seriesCheck)
          #[mkApp (mkConst ``Ctx.make) (mkNatLit prec), bodyE, mkNatLit N, toExpr q, rt.expr]
        let hchk ← certify chk (checkCost prec (N * 20))
        let hc := mkApp (mkConst ``Ctx.make_valid) (mkNatLit prec)
        let pf := mkAppN (mkConst ``Series.subtype_of_check)
          #[f, tol, mkApp (mkConst ``Ctx.make) (mkNatLit prec), hc, bodyE, rt.expr, mkNatLit N,
            toExpr q, hbody, rt.proof, hchk]
        return some (mkApp4 (mkConst ``Subtype.mk [1]) α p (toExpr q) pf)
  return none

/-- `¬ Summable f` -/
def proveNotSummable? (P : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let_expr Not S := P | return none
  let some f ← seqArg? S ``Summable | return none
  let (bodyE, hbody) ← reifyBody f
  let body ← evalExprVal .real bodyE
  let c := Ctx.make 64
  for N in [1, 2, 4, 8, 16, 32, 64] do
    unless Series.divergeCheck c body N do continue
    let chk := mkAppN (mkConst ``Series.divergeCheck)
      #[mkApp (mkConst ``Ctx.make) (mkNatLit 64), bodyE, mkNatLit N]
    let hchk ← certify chk 100
    return some (mkAppN (mkConst ``Series.not_summable_of_check)
      #[f, mkApp (mkConst ``Ctx.make) (mkNatLit 64), mkApp (mkConst ``Ctx.make_valid) (mkNatLit 64),
        bodyE, mkNatLit N, hbody, hchk])
  return none

/-- series goals, including `A ⊕' B` alternatives -/
partial def proveSeries? (goalTy : Lean.Expr) : TacticM (Option Lean.Expr) := do
  if let some pf ← proveNotSummable? goalTy then return some pf
  if let some pf ← proveSeriesSubtype? goalTy then return some pf
  let ty ← whnf goalTy
  if let some pf ← proveSeriesSubtype? ty then return some pf
  let_expr PSum A B := ty | return none
  let s ← saveState
  try
    if let some pf ← proveSeries? A then
      return some (mkApp3 (mkConst ``PSum.inl [← getLevel' A, ← getLevel' B]) A B pf)
  catch e => trace[lynth.interval] "series (left): {e.toMessageData}"
  s.restore
  if let some pf ← proveSeries? B then
    return some (mkApp3 (mkConst ``PSum.inr [← getLevel' A, ← getLevel' B]) A B pf)
  return none
where
  getLevel' (T : Lean.Expr) : MetaM Level := do
    let u ← getLevel T
    return u.dec.getD u

end Lynth.Interval.Goals
