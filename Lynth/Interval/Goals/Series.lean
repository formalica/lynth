module

public meta import Lynth.Analysis.SpecialFunctions
public meta import Lynth.Analysis.SpecialFunctionsDefs
public meta import Lynth.Interval.Check.AiryProof
public meta import Lynth.Interval.Check.EtaProof
public meta import Lynth.Interval.Fns.EulerGamma.Proof.PowerSeries
public meta import Lynth.Interval.Fns.Gamma
public meta import Lynth.Interval.Integral.Cert
public meta import Lynth.Interval.Integral.Engine
public meta import Lynth.Interval.Integral.Legendre
public meta import Lynth.Interval.Integral.Math.IntegralBounds
public meta import Lynth.Interval.Integral.Math.LegendreEval
public meta import Lynth.Interval.Integral.Math.Tails
public meta import Lynth.Interval.Integral.Memo
public meta import Lynth.Interval.Integral.Panel
public meta import Lynth.Interval.Integral.Reify
public meta import Lynth.Interval.Integral.Search
public meta import Lynth.Interval.Reify.Registry

public meta import Lynth.Interval.Integral.Math.FixedTrig
public meta import Lynth.Interval.Integral.Math.FixedExp
public meta import Lynth.Interval.Integral.Math.FixedPoint
public meta import Lynth.Interval.Core.Asy
public meta import Lynth.Interval.Core.Env
public meta import Lynth.Interval.Fns.Elem
public meta import Lynth.Interval.Fns.Exp
public meta import Lynth.Interval.Fns.Log
public meta import Lynth.Interval.Num.CBox
public meta import Lynth.Interval.Num.NIval
public meta import Lynth.Interval.Num.ZIval
public meta import Lynth.Interval.Series.Arctan
public meta import Lynth.Interval.Series.Atanh
public meta import Lynth.Interval.Series.Tail

public meta import Lynth.Interval.Check.Trust
public meta import Lynth.Interval.Core.Const
public meta import Lynth.Interval.Core.Ctx
public meta import Lynth.Interval.Core.Expr
public meta import Lynth.Interval.Core.ExprAsy
public meta import Lynth.Interval.Core.Ty
public meta import Lynth.Interval.Num.Dy
public meta import Lynth.Interval.Num.Ival
public meta import Lynth.Interval.Reify.Reify
public meta import Lynth.Interval.Series.Cert
public meta import Lynth.Interval.Vendor.Dyadic
public meta import Lynth.Options

public import Lynth.Interval.Goals.Approx
public import Lynth.Interval.Goals.Closed
public import Lynth.Interval.Goals.Support
public import Lynth.Interval.Reify.Reify

public meta import Lean.Elab.Tactic.Basic
public import Lynth.Interval.Goals.ComplexSeries
public import Batteries.Classes.RatCast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Lynth.Interval.Core.Ctx
public import Lynth.Interval.Core.Env
public import Lynth.Interval.Core.Expr
public import Lynth.Interval.Core.Ty
public import Lynth.Interval.Series.Cert
meta import all Lynth.Interval.Goals.Approx
import all Lynth.Interval.Goals.Approx
meta import all Lynth.Interval.Goals.ComplexSeries
import all Lynth.Interval.Goals.ComplexSeries
meta import all Lynth.Interval.Goals.Support
import all Lynth.Interval.Goals.Support
meta import all Lynth.Interval.Series.Cert
import all Lynth.Interval.Series.Cert

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

meta section

namespace Lynth.Interval.Series

public theorem subtype_of_check {f : ℕ → ℝ} {tol : ℝ} {c : Ctx} (hc : c.Valid) {body tolE : Expr .real}
    {N : ℕ} {q : ℚ} (hf : ∀ k, f k = body.denote (({} : SEnv).push .nat k))
    (htol : tol = tolE.denote {}) (h : seriesCheck c body N q tolE = true) :
    Summable f ∧ |tsum f - q| < tol := by
  obtain rfl : f = fun k => body.denote (({} : SEnv).push .nat k) := funext hf
  subst htol
  exact seriesCheck_sound hc h

public theorem not_summable_of_check {f : ℕ → ℝ} {c : Ctx} (hc : c.Valid) {body : Expr .real} {N : ℕ}
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
    let_expr LT.lt _ _ lhs tol := I | return none
    unless lhs.getAppFn.isConstOf ``abs do return none
    let diff := lhs.getAppArgs.back!
    unless diff.isAppOf ``HSub.hSub do return none
    let args := diff.getAppArgs
    unless isCastOf x args.back! do return none
    let some valueFn ← seqArg? args[args.size-2]! ``tsum | return none
    unless ← isDefEq f valueFn do return none
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
    -- A missing tail rule cannot be repaired by trying every prefix and
    -- precision. Check the largest prefix, allowing finite singular regions.
    unless summableShape (body.asy c (seriesNs.getLast?.getD 8)) do
      let rounding ← withLocalDeclD `k (mkConst ``Nat) fun k =>
        tailNeedsPrecision (mkApp f k).headBeta k prec
      unless rounding do return none
      continue
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

/-- An unsupported summand leaves the goal available to the compositional
enclosure handler, including summands containing integrals. -/
private def trySeriesSubtype? (goalTy : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let saved ← saveState
  try
    if let some proof ← proveSeriesSubtype? goalTy then return some proof
  catch ex =>
    if ex.isInterrupt then throw ex
  saved.restore
  return none

/-- series goals, including `A ⊕' B` alternatives -/
public partial def proveSeries? (goalTy : Lean.Expr) : TacticM (Option Lean.Expr) := do
  if let some pf ← proveNotSummable? goalTy then return some pf
  if let some pf ← trySeriesSubtype? goalTy then return some pf
  if let some pf ← proveComplexSeries? goalTy then return some pf
  let ty ← whnf goalTy
  if ty != goalTy then
    if let some pf ← trySeriesSubtype? ty then return some pf
    if let some pf ← proveComplexSeries? ty then return some pf
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
