import Lynth.Interval.Goals.Closed

/-!
# Rational witnesses `{x : ℚ // P x}` and `{p : ℚ × ℚ // P p}`

Witness guessing (untrusted, native): anchors `A - ↑x`, `↑x - A` (and for pairs
`… - ↑p.1`, `… - ↑p.2`, or `E - (↑p.1 + ↑p.2 * I)` for complex `E`) are
evaluated and short rationals near their midpoints are tried; each candidate
`P q` is then proved as a closed proposition.
See `docs/interval/05-point-goals.md §2`.
-/

namespace Lynth.Interval.Goals

open Lean Meta Elab Tactic Reify

unsafe def evalExprUnsafe (t : Ty) (e : Lean.Expr) : MetaM (Expr t) :=
  evalExpr (Expr t) (mkApp (mkConst ``Expr) (toExpr t)) e

/-- runtime value of a reified expression term -/
@[implemented_by evalExprUnsafe] opaque evalExprVal (t : Ty) (e : Lean.Expr) : MetaM (Expr t)

/-- shortest decimals (by digit count) inside `[m - r, m + r]` -/
def shortRats (m r : ℚ) : List ℚ := Id.run do
  let mut out : List ℚ := []
  for d in [0:60] do
    let s : ℚ := (10 : ℚ) ^ d
    let q : ℚ := (Int.floor (m * s + 1/2) : ℚ) / s
    if |q - m| ≤ r then
      out := out ++ [q]
      if out.length ≥ 2 then return out
  return out ++ [m]

/-- candidate rational values for a real anchor -/
def realCandidates (A : Expr .real) (tolHint : ℚ) : CoreM (List ℚ) := do
  let maxPrec := lynth.interval.maxPrec.get (← getOptions)
  for prec in precSchedule maxPrec do
    let I : Ival := A.eval (Ctx.make prec) {}
    match I.lo, I.hi with
    | some lo, some hi =>
      let m := (lo.toRat + hi.toRat) / 2
      let w := hi.toRat - lo.toRat
      if w < tolHint / 4 then
        return shortRats m (tolHint / 4 - w / 2)
    | _, _ => pure ()
  return []

/-- a lower bound of a (closed) tolerance term -/
def tolLower (T : Lean.Expr) : TacticM ℚ := do
  try
    let r ← reify {} T
    let v ← evalExprVal .real r.expr
    let I : Ival := v.eval (Ctx.make 64) {}
    match I.lo with
    | some l => if 0 < l.toRat then return l.toRat else return 1 / 10 ^ 30
    | none => return 1 / 10 ^ 30
  catch _ => return 1 / 10 ^ 30

/-- `b` is a cast `((x : ℚ) : ℝ)` of the given term -/
def isCastOf (x b : Lean.Expr) : Bool :=
  b.isAppOfArity ``Rat.cast 3 && b.appArg! == x

/-- collect subterms of `e` -/
partial def subterms (e : Lean.Expr) : Array Lean.Expr :=
  let rec go (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
    let acc := acc.push e
    match e with
    | .app f a => go a (go f acc)
    | .lam _ t b _ => go b (go t acc)
    | .forallE _ t b _ => go b (go t acc)
    | .mdata _ b => go b acc
    | _ => acc
  go e #[]

/-- anchor terms for the variable `x` (e.g. `x`, `p.1`): `A` in `A - ↑x` or `↑x - A` -/
def anchorsFor (x : Lean.Expr) (P : Lean.Expr) : Array Lean.Expr := Id.run do
  let mut out := #[]
  for e in subterms P do
    match e.getAppFnArgs with
    | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      if isCastOf x b && !a.hasLooseBVars && !a.hasFVar then out := out.push a
      else if isCastOf x a && !b.hasLooseBVars && !b.hasFVar then out := out.push b
    | _ => pure ()
  return out

/-- tolerance candidates: right sides of `<`/`≤` atoms -/
def tolerances (P : Lean.Expr) : Array Lean.Expr := Id.run do
  let mut out := #[]
  for e in subterms P do
    match e.getAppFnArgs with
    | (``LT.lt, #[_, _, _, rhs]) => if !rhs.hasFVar then out := out.push rhs
    | (``LE.le, #[_, _, _, rhs]) => if !rhs.hasFVar then out := out.push rhs
    | _ => pure ()
  return out


/-- minimal tolerance over all candidate tolerance terms -/
def minTol (P : Lean.Expr) : TacticM ℚ := do
  let mut best : ℚ := 1
  for T in tolerances P do
    let t ← tolLower T
    if t < best then best := t
  return best

/-- evaluate a closed real anchor term and propose rationals -/
def candidatesOf (A : Lean.Expr) (tol : ℚ) : TacticM (List ℚ) := do
  try
    let r ← reify {} A
    let v ← evalExprVal .real r.expr
    realCandidates v tol
  catch _ => return []

/-- `{x : ℚ // P x}` -/
def proveRatSubtype? (goalTy : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let_expr Subtype α p := goalTy | return none
  unless (← whnfR α).isConstOf ``Rat do return none
  let p ← whnfR p
  let .lam n _ body _ := p | return none
  withLocalDeclD n α fun x => do
    let P := body.instantiate1 x
    let anchors := anchorsFor x P
    if anchors.isEmpty then return none
    let tol ← minTol P
    for A in anchors do
      for q in ← candidatesOf A tol do
        let qE := toExpr q
        let Pq := body.instantiate1 qE
        try
          if let some pf ← proveClosed? Pq then
            return some (mkApp4 (mkConst ``Subtype.mk [1]) α p qE pf)
        catch e => trace[lynth.interval] "candidate {q}: {e.toMessageData}"
    return none

end Lynth.Interval.Goals
