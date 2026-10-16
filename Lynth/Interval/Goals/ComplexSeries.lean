import Lynth.Interval.Goals.Approx
import Lynth.Interval.Series.ComplexCert

/-!
# Complex infinite-series goals.

`{p : Rat × Rat // Summable f ∧ ‖tsum f - ↑p‖ < tol}` with `f : ℕ → ℂ`,
and `¬ Summable f`.  Bodies are reified to `Expr .cplx` and dispatched to
the per-family certificates in `ComplexCert.lean`.  Bridges
(`body.denote = family-form`) are closed by the denotation kit via `simp`;
real side conditions over literal values by `norm_num`.
-/

namespace Lynth.Interval.Series

/-- assembly for family 1 -/
theorem tele1_subtype_of_check {f : ℕ → ℂ} {tol : ℝ} {c : Ctx} (hc : c.Valid)
    {c0 w1 : ℚ} {q1 q2 : ℚ} {tolE : Expr .real}
    (htol : tol = tolE.denote {})
    (hbridge : ∀ k : ℕ, f k
      = ((c0 : ℝ) : ℂ) / ((((w1 : ℝ) : ℂ) + ((k : ℕ) : ℂ))
        * ((((w1 : ℝ) : ℂ) + ((k : ℕ) : ℂ)) + 1)))
    (hw : (1 : ℝ) ≤ ((w1 : ℚ) : ℝ))
    (h : tele1Check c c0 w1 q1 q2 tolE = true) :
    Summable f ∧
      ‖tsum f - ((((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I))‖ < tol := by
  subst htol
  exact tele1_sound hc hbridge hw h

/-- assembly for family 2 -/
theorem tele2_subtype_of_check {f : ℕ → ℂ} {tol : ℝ} {c : Ctx} (hc : c.Valid)
    {c0 b0 : ℚ} {q1 q2 : ℚ} {tolE : Expr .real}
    (htol : tol = tolE.denote {})
    (hbridge : ∀ k : ℕ, f k
      = ((c0 : ℝ) : ℂ) / (((2 * ((k : ℕ) : ℂ)) + ((b0 : ℝ) : ℂ))
        * ((((2 * ((k : ℕ) : ℂ)) + ((b0 : ℝ) : ℂ))) + 2)))
    (hw : (1 : ℝ) ≤ ((b0 : ℚ) : ℝ))
    (h : tele2Check c c0 b0 q1 q2 tolE = true) :
    Summable f ∧
      ‖tsum f - ((((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I))‖ < tol := by
  subst htol
  exact tele2_sound hc hbridge hw h

/-- assembly for factorial family -/
theorem fact_subtype_of_check {f : ℕ → ℂ} {tol : ℝ} {c : Ctx} (hc : c.Valid)
    {body : Expr .cplx} {N : ℕ} {q1 q2 : ℚ} {tolE : Expr .real}
    (hf : ∀ k, f k = body.denote (({} : SEnv).push .nat k))
    (htol : tol = tolE.denote {})
    (hbridge : ∀ k : ℕ, f k = ((((1 : ℚ)) : ℝ) : ℂ) / ((((Nat.factorial (k + 1) : ℕ)) : ℂ)))
    (h : factCheck c body N q1 q2 tolE = true) :
    Summable f ∧
      ‖tsum f - ((((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I))‖ < tol := by
  subst htol
  exact fact_sound (c := c) hc (f := f) (body := body) hf hbridge h

/-- assembly for selfpow family -/
theorem self_subtype_of_check {f : ℕ → ℂ} {tol : ℝ} {c : Ctx} (hc : c.Valid)
    {body : Expr .cplx} {N : ℕ} {q1 q2 : ℚ} {tolE : Expr .real}
    (hf : ∀ k, f k = body.denote (({} : SEnv).push .nat k))
    (htol : tol = tolE.denote {})
    (hbridge : ∀ k : ℕ, f k = ((((1 : ℚ)) : ℝ) : ℂ) / (((((k + 1 : ℕ)) : ℂ) ^ (k + 1))))
    (h : selfCheck c body N q1 q2 tolE = true) :
    Summable f ∧
      ‖tsum f - ((((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I))‖ < tol := by
  subst htol
  exact self_sound (c := c) hc (f := f) (body := body) hf hbridge h

/-- assembly for mersenne family -/
theorem mers_subtype_of_check {f : ℕ → ℂ} {tol : ℝ} {c : Ctx} (hc : c.Valid)
    {body : Expr .cplx} {N : ℕ} {q1 q2 : ℚ} {tolE : Expr .real}
    (hf : ∀ k, f k = body.denote (({} : SEnv).push .nat k))
    (htol : tol = tolE.denote {})
    (hbridge : ∀ k : ℕ, f k = ((((1 : ℚ)) : ℝ) : ℂ) / (((((2 : ℚ)) : ℝ) : ℂ) ^ (k + 1) - 1))
    (h : mersCheck c body N q1 q2 tolE = true) :
    Summable f ∧
      ‖tsum f - ((((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I))‖ < tol := by
  subst htol
  exact mers_sound (c := c) hc (f := f) (body := body) hf hbridge h

/-- assembly for fib family -/
theorem fib_subtype_of_check {f : ℕ → ℂ} {tol : ℝ} {c : Ctx} (hc : c.Valid)
    {body : Expr .cplx} {N : ℕ} {q1 q2 : ℚ} {tolE : Expr .real} (hN : 1 ≤ N)
    (hf : ∀ k, f k = body.denote (({} : SEnv).push .nat k))
    (htol : tol = tolE.denote {})
    (hbridge : ∀ k : ℕ, f k = ((((1 : ℚ)) : ℝ) : ℂ) / ((((Nat.fib (k + 1) : ℕ)) : ℂ)))
    (h : fibCheck c body N q1 q2 tolE = true) :
    Summable f ∧
      ‖tsum f - ((((q1 : ℂ)) + ((q2 : ℂ)) * Complex.I))‖ < tol := by
  subst htol
  exact fib_sound (c := c) hc hN (f := f) (body := body) hf hbridge h

end Lynth.Interval.Series

namespace Lynth.Interval.Goals

open Lean Meta Elab Tactic Reify Series Term

/-- the function argument of `Summable f` / `tsum f` (`f : ℕ → ℂ`) -/
def seqArgC? (e : Lean.Expr) (head : Name) : MetaM (Option Lean.Expr) := do
  unless e.getAppFn.isConstOf head do return none
  let fty ← mkArrow (mkConst ``Nat) (mkConst ``Complex)
  for a in e.getAppArgs do
    if ← isDefEq (← inferType a) fty then return some a
  return none

/-- reify the complex series body -/
def reifyBodyC (f : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  withLocalDeclD `k (mkConst ``Nat) fun k => do
    let t := (mkApp f k).headBeta
    let rc : RCtx := ({} : RCtx).push k .nat
    let r ← reify rc t
    unless r.ty == .cplx do throwError "lynth interval: complex series body is not complex"
    return (r.expr, ← mkLambdaFVars #[k] r.proof)

/-- run `norm_num` on a goal; success iff fully closed -/
def runNormNum? (mvar : MVarId) : TacticM Bool := do
  let s ← saveState
  try
    let gs ← Tactic.run mvar (evalTactic (← `(tactic| norm_num)))
    unless gs.isEmpty do
      s.restore
      return false
    return true
  catch _ =>
    s.restore
    return false

/-- `((q : ℚ) : ℝ)` with explicit instance -/
def mkRatReal (qE : Lean.Expr) : MetaM Lean.Expr :=
  mkAppOptM ``Rat.cast #[some (mkConst ``Real), none, some qE]

/-- `(((q : ℚ) : ℝ) : ℂ)` -/
def mkRatCplx (qE : Lean.Expr) : MetaM Lean.Expr := do
  let r ← mkRatReal qE
  mkAppM ``Complex.ofReal #[r]

/-- `((k : ℕ) : ℂ)` -/
def mkNatCplx (k : Lean.Expr) : MetaM Lean.Expr :=
  mkAppOptM ``Nat.cast #[some (mkConst ``Complex), none, some k]

/-- `(1 : ℂ)` via closed-syntax elaboration (matches OfNat form) -/
def mkOneCplx : TacticM Lean.Expr := do
  let stx : Term ← `(OfNat.ofNat 1)
  Term.elabTerm stx (mkConst ``Complex)

/-- `(2 : ℂ)` via closed-syntax elaboration (matches OfNat form) -/
def mkTwoCplx : TacticM Lean.Expr := do
  let stx : Term ← `(OfNat.ofNat 2)
  Term.elabTerm stx (mkConst ``Complex)

/-- binary H-op from pinned `ℂ` args -/
def mkHBin (nm : Name) (a b : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM nm #[a, b]

/-- RHS term for family 2: `c0 / (((2*k) + b0) * (((2*k) + b0) + 2))` -/
def mkTele2Rhs (c0E b0E : Lean.Expr) (k : Lean.Expr) : TacticM Lean.Expr := do
  let c0v ← mkRatCplx c0E
  let b0v ← mkRatCplx b0E
  let kc ← mkNatCplx k
  let twoC ← mkTwoCplx
  let dk ← mkHBin ``HMul.hMul twoC kc
  let t1 ← mkHBin ``HAdd.hAdd dk b0v
  let t2 ← mkHBin ``HAdd.hAdd t1 twoC
  let t3 ← mkHBin ``HMul.hMul t1 t2
  mkHBin ``HDiv.hDiv c0v t3

/-- RHS term for family 1: `c0 / ((w0 + k) * ((w0 + k) + 1))` -/
def mkTele1Rhs (c0E w1E : Lean.Expr) (k : Lean.Expr) : TacticM Lean.Expr := do
  let c0v ← mkRatCplx c0E
  let w0v ← mkRatCplx w1E
  let kc ← mkNatCplx k
  let oneC ← mkOneCplx
  let t1 ← mkHBin ``HAdd.hAdd w0v kc
  let t2 ← mkHBin ``HAdd.hAdd t1 oneC
  let t3 ← mkHBin ``HMul.hMul t1 t2
  mkHBin ``HDiv.hDiv c0v t3

/-- RHS term for factorial family: `1 / ((k+1)!)` (with `(((1:ℚ)):ℝ):ℂ` numerator) -/
def mkFactRhs (k : Lean.Expr) : TacticM Lean.Expr := do
  let oneQ : Lean.Expr := toExpr (1 : ℚ)
  let c0v ← mkRatCplx oneQ
  let oneN : Lean.Expr := toExpr (1 : ℕ)
  let kp1 ← mkAppM ``Nat.add #[k, oneN]
  let fac ← mkAppM ``Nat.factorial #[kp1]
  let facC ← mkAppOptM ``Nat.cast #[some (mkConst ``Complex), none, some fac]
  mkHBin ``HDiv.hDiv c0v facC

/-- RHS term for selfpow family: `1 / (((k+1):ℂ) ^ (k+1))` -/
def mkSelfRhs (k : Lean.Expr) : TacticM Lean.Expr := do
  let oneQ : Lean.Expr := toExpr (1 : ℚ)
  let c0v ← mkRatCplx oneQ
  let oneN : Lean.Expr := toExpr (1 : ℕ)
  let kp1 ← mkAppM ``Nat.add #[k, oneN]
  let base ← mkAppOptM ``Nat.cast #[some (mkConst ``Complex), none, some kp1]
  let pw ← mkAppM ``HPow.hPow #[base, kp1]
  mkHBin ``HDiv.hDiv c0v pw

/-- RHS term for mersenne family: `1 / (2^(k+1) - 1)` -/
def mkMersRhs (k : Lean.Expr) : TacticM Lean.Expr := do
  let oneQ : Lean.Expr := toExpr (1 : ℚ)
  let twoQ : Lean.Expr := toExpr (2 : ℚ)
  let c0v ← mkRatCplx oneQ
  let b2v ← mkRatCplx twoQ
  let oneN : Lean.Expr := toExpr (1 : ℕ)
  let kp1 ← mkAppM ``Nat.add #[k, oneN]
  let pw ← mkAppM ``HPow.hPow #[b2v, kp1]
  let oneC ← mkOneCplx
  let den ← mkHBin ``HSub.hSub pw oneC
  mkHBin ``HDiv.hDiv c0v den

/-- RHS term for fib family: `1 / (fib (k+1))` -/
def mkFibRhs (k : Lean.Expr) : TacticM Lean.Expr := do
  let oneQ : Lean.Expr := toExpr (1 : ℚ)
  let c0v ← mkRatCplx oneQ
  let oneN : Lean.Expr := toExpr (1 : ℕ)
  let kp1 ← mkAppM ``Nat.add #[k, oneN]
  let fb ← mkAppM ``Nat.fib #[kp1]
  let fbC ← mkAppOptM ``Nat.cast #[some (mkConst ``Complex), none, some fb]
  mkHBin ``HDiv.hDiv c0v fbC

/-- `(-1 : ℂ)` via closed-syntax elaboration -/
def mkNegOneCplx : TacticM Lean.Expr := do
  let stx : Term ← `((-1 : ℂ))
  Term.elabTerm stx (mkConst ``Complex)

/-- RHS term for alternating-harmonic divergence: `(-1)^k/(k+1)` -/
def mkAltHarmRhs (k : Lean.Expr) : TacticM Lean.Expr := do
  let negOne ← mkNegOneCplx
  let num ← mkAppM ``HPow.hPow #[negOne, k]
  let kc ← mkNatCplx k
  let oneN : Lean.Expr := toExpr (1 : ℕ)
  let oneNC ← mkAppOptM ``Nat.cast #[some (mkConst ``Complex), none, some oneN]
  let den ← mkHBin ``HAdd.hAdd kc oneNC
  mkHBin ``HDiv.hDiv num den

/-- RHS term for constant-one divergence: `1` -/
def mkConstOneRhs : TacticM Lean.Expr := mkOneCplx

/-- simple cast-only bridge: unfold `f`, then `push_cast`/`simp`/`ring`;
for division-free-cast equalities (factorial/fib/...) with no side conditions -/
def runBridgeSimple? (mvar : MVarId) (f : Lean.Expr) (k : Lean.Expr)
    (mkClosed : Lean.Expr → TacticM Lean.Expr) : TacticM (Option Lean.Expr) := do
  let s ← saveState
  try
    match f.getAppFn.constName? with
    | some n =>
      let idStx : Ident := mkIdent n
      let tSimp ← `(tactic| simp only [$idStx:ident]; try push_cast; try simp only [Rat.cast_one, Complex.ofReal_one, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_natCast, Rat.cast_add, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]; try ring)
      let tPush ← `(tactic| simp only [$idStx:ident]; try push_cast; try ring)
      let tRing ← `(tactic| simp only [$idStx:ident]; try ring; skip)
      for (nm, tac) in [("simp", tSimp), ("push", tPush), ("ring", tRing)] do
        s.restore
        let gs ←
          try Tactic.run mvar (evalTactic tac)
          catch e =>
            continue
        unless gs.isEmpty do
          continue
        let hopen ← instantiateMVars (Expr.mvar mvar)
        return some (← mkClosed hopen)
      s.restore
      return none
    | none => s.restore; return none
  catch _ =>
    s.restore
    return none

/-- numerator of a single-division form, via application projection -/
def getNum? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let (fn, args) := e.getAppFnArgs
  unless fn == ``HDiv.hDiv do return none
  if args.size != 6 then return none
  return some args[4]!

/-- denominator of a single-division form, via application projection -/
def getDen? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let (fn, args) := e.getAppFnArgs
  unless fn == ``HDiv.hDiv do return none
  if args.size != 6 then return none
  return some args[5]!

/-- prove `DEN ≠ 0` for a tele1-shaped denominator (product of two
`w+k`-like factors) by the real-part argument. Generic in `DEN`
(no naming beyond the stable `k`). Returns the proof. -/
def proveDenNePf? (neTy : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let s ← saveState
  try
    let m ← mkFreshExprSyntheticOpaqueMVar neTy
    let gs ← Tactic.run m.mvarId! (evalTactic (← `(tactic| apply mul_ne_zero <;> intro h <;> have hr := congrArg Complex.re h <;> simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re, Complex.one_re, Complex.zero_re, Complex.I_re, mul_zero, mul_one, zero_mul, one_mul] at hr <;> try norm_num at hr <;> linarith)))
    unless gs.isEmpty do
      s.restore
      return none
    return some (← instantiateMVars m)
  catch _ =>
    s.restore
    return none

/-- prove `∀ k, f k = family` by unfolding `f`, establishing denominator
nonvanishing (asserted into context), then `field_simp` + cast
normalization. Avoids `ring_nf`, whose automatic side-condition discharge
produces kernel-rejected proofs here. -/
def runBridgeFam? (mvar : MVarId) (f : Lean.Expr) (k : Lean.Expr)
    (mkClosed : Lean.Expr → TacticM Lean.Expr) : TacticM (Option Lean.Expr) := do
  let s ← saveState
  try
    match f.getAppFn.constName? with
    | some n =>
      let idStx : Ident := mkIdent n
      let gs ← Tactic.run mvar
        (evalTactic (← `(tactic| simp only [$idStx:ident])))
      let [g1] := gs | s.restore; return none
      let gt ← g1.getType
      let_expr Eq _ lhs rhs := gt | s.restore; return none
      let some num1 ← getNum? lhs | s.restore; return none
      let some den1 ← getDen? lhs | s.restore; return none
      let some num2 ← getNum? rhs | s.restore; return none
      let some den2 ← getDen? rhs | s.restore; return none
      let zeroC ← Term.elabTerm (← `(OfNat.ofNat 0)) (mkConst ``Complex)
      let neTy1 ← mkAppM ``Ne #[den1, zeroC]
      let neTy2 ← mkAppM ``Ne #[den2, zeroC]
      let some h1 ← proveDenNePf? neTy1 | s.restore; return none
      let some h2 ← proveDenNePf? neTy2 | s.restore; return none
      -- cross-multiplied equation (division-free) + ring variants
      let crossL ← mkAppM ``HMul.hMul #[num1, den2]
      let crossR ← mkAppM ``HMul.hMul #[num2, den1]
      let crossTy ← mkAppM ``Eq #[crossL, crossR]
      let tRing ← `(tactic| ring; skip)
      let tPushRing ← `(tactic| push_cast; ring)
      let tSimpRing ← `(tactic| simp only [Rat.cast_one, Complex.ofReal_one, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_natCast, Rat.cast_add, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]; ring)
      let crossTacs := [("ring", tRing), ("pushcast-ring", tPushRing),
        ("simpcast-ring", tSimpRing)]
      let mut hcrossOpt : Option Lean.Expr := none
      for (nm, tac) in crossTacs do
        s.restore
        let mc ← mkFreshExprSyntheticOpaqueMVar crossTy
        let gsc ←
          try Tactic.run mc.mvarId! (evalTactic tac)
          catch _ => continue
        unless gsc.isEmpty do continue
        let hc ← instantiateMVars mc
        let hcClosed ← mkLambdaFVars #[k] hc
        try
          hcrossOpt := some hc
          break
        catch e =>
          continue
      let some hcross := hcrossOpt | s.restore; return none
      let hIff ← mkAppOptM ``Series.div_eq_div_iff_C #[some num1, some den1, some num2, some den2, some h1, some h2]
      let hpf ← mkAppM ``Iff.mpr #[hIff, hcross]
      g1.assign hpf
      let hopen ← instantiateMVars (Expr.mvar g1)
      return some (← mkClosed hopen)
    | none => s.restore; return none
  catch _ =>
    s.restore
    return none


/-- `{p : Rat × Rat // Summable f ∧ ‖tsum f - ↑p‖ < tol}` via family 1 -/
def proveComplexTele1? (goalTy : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let_expr Subtype α p := goalTy | return none
  let α ← whnfR α
  let some (a1, a2) ← prodArgs? α | return none
  unless (← whnfR a1).isConstOf ``Rat do return none
  unless (← whnfR a2).isConstOf ``Rat do return none
  let p ← whnfR p
  let .lam n _ pbody _ ← pure p | return none
  let found ← withLocalDeclD n α fun x => do
    let P := pbody.instantiate1 x
    let_expr And S I := P | return none
    let some f ← seqArgC? S ``Summable | return none
    let_expr LT.lt _ _ _ tol := I | return none
    if tol.hasFVar then return none
    return some (f, tol)
  let some (f, tol) := found | return none
  let (bodyE, _) ← reifyBodyC f
  let rt ← reify {} tol
  unless rt.ty == .real do return none
  let body ← evalExprVal .cplx bodyE
  let tolV ← evalExprVal .real rt.expr
  let tl ← tolLower tol
  let maxPrec := lynth.interval.maxPrec.get (← getOptions)
  for prec in precSchedule maxPrec do
    let c := Ctx.make prec
    let some (c0, w1) := Series.matchTele1 body | continue
    trace[lynth.interval] "cx tele1: matched c0={c0}, w1={w1}"
    let c0E := toExpr c0
    let w1E := toExpr w1
    let res ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      try
        let fk := mkApp f k
        let rhs ← mkTele1Rhs c0E w1E k
        let eq ← mkAppM ``Eq #[fk, rhs]
        let mvar ← mkFreshExprSyntheticOpaqueMVar eq
        runBridgeFam? mvar.mvarId! f k (fun hopen => mkLambdaFVars #[k] hopen)
      catch e =>
        return (none : Option Lean.Expr)
    let some hbridge := res | continue
    let oneR ← Term.elabTerm (← `(OfNat.ofNat 1)) (mkConst ``Real)
    let w1R ← mkRatReal w1E
    let hwTy ← mkAppM ``LE.le #[oneR, w1R]
    let hmvar ← mkFreshExprSyntheticOpaqueMVar hwTy
    unless ← runNormNum? hmvar.mvarId! do
      continue
    let hw ← instantiateMVars hmvar
    let B := Series.tele1Box c c0 w1
    let (some lo1, some hi1, some lo2, some hi2) :=
      (B.re.lo, B.re.hi, B.im.lo, B.im.hi) | continue
    let m1 := (lo1.toRat + hi1.toRat) / 2
    let w1w := hi1.toRat - lo1.toRat
    let m2 := (lo2.toRat + hi2.toRat) / 2
    let w2w := hi2.toRat - lo2.toRat
    if w1w ≥ tl / 2 || w2w ≥ tl / 2 then continue
    for q1 in shortRats m1 (tl / 2 - w1w / 2) do
      for q2 in shortRats m2 (tl / 2 - w2w / 2) do
        unless Series.tele1Check c c0 w1 q1 q2 tolV do continue
        trace[lynth.interval] "complex series (tele1): prec = {prec}, q = ({q1}, {q2})"
        let chk := mkAppN (mkConst ``Series.tele1Check)
          #[mkApp (mkConst ``Ctx.make) (mkNatLit prec), c0E, w1E,
            toExpr q1, toExpr q2, rt.expr]
        let hchk ← certify chk (checkCost prec 40)
        let hc := mkApp (mkConst ``Ctx.make_valid) (mkNatLit prec)
        let pairE ← mkAppM ``Prod.mk #[toExpr q1, toExpr q2]
        let pf := mkAppN (mkConst ``Series.tele1_subtype_of_check)
          #[f, tol, mkApp (mkConst ``Ctx.make) (mkNatLit prec), hc,
            c0E, w1E, toExpr q1, toExpr q2, rt.expr,
            rt.proof, hbridge, hw, hchk]
        return some (mkApp4 (mkConst ``Subtype.mk [1]) α p pairE pf)
  return none

/-- complex series goals (more families to come) -/
def proveComplexTele2n? (goalTy : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let_expr Subtype α p := goalTy | return none
  let α ← whnfR α
  let some (a1, a2) ← prodArgs? α | return none
  unless (← whnfR a1).isConstOf ``Rat do return none
  unless (← whnfR a2).isConstOf ``Rat do return none
  let p ← whnfR p
  let .lam n _ pbody _ ← pure p | return none
  let found ← withLocalDeclD n α fun x => do
    let P := pbody.instantiate1 x
    let_expr And S I := P | return none
    let some f ← seqArgC? S ``Summable | return none
    let_expr LT.lt _ _ _ tol := I | return none
    if tol.hasFVar then return none
    return some (f, tol)
  let some (f, tol) := found | return none
  let (bodyE, _) ← reifyBodyC f
  let rt ← reify {} tol
  unless rt.ty == .real do return none
  let body ← evalExprVal .cplx bodyE
  let tolV ← evalExprVal .real rt.expr
  let tl ← tolLower tol
  let maxPrec := lynth.interval.maxPrec.get (← getOptions)
  for prec in precSchedule maxPrec do
    let c := Ctx.make prec
    let some (c0, b0) := Series.matchTele2n body | continue
    trace[lynth.interval] "cx tele2: matched c0={c0}, b0={b0}"
    let c0E := toExpr c0
    let b0E := toExpr b0
    let res ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      try
        let fk := mkApp f k
        let rhs ← mkTele2Rhs c0E b0E k
        let eq ← mkAppM ``Eq #[fk, rhs]
        let mvar ← mkFreshExprSyntheticOpaqueMVar eq
        runBridgeFam? mvar.mvarId! f k (fun hopen => mkLambdaFVars #[k] hopen)
      catch e =>
        return (none : Option Lean.Expr)
    let some hbridge := res | continue
    let oneR ← Term.elabTerm (← `(OfNat.ofNat 1)) (mkConst ``Real)
    let b0R ← mkRatReal b0E
    let hwTy ← mkAppM ``LE.le #[oneR, b0R]
    let hmvar ← mkFreshExprSyntheticOpaqueMVar hwTy
    unless ← runNormNum? hmvar.mvarId! do
      continue
    let hw ← instantiateMVars hmvar
    let B := Series.tele2Box c c0 b0
    let (some lo1, some hi1, some lo2, some hi2) :=
      (B.re.lo, B.re.hi, B.im.lo, B.im.hi) | continue
    let m1 := (lo1.toRat + hi1.toRat) / 2
    let ww := hi1.toRat - lo1.toRat
    let m2 := (lo2.toRat + hi2.toRat) / 2
    let ww2 := hi2.toRat - lo2.toRat
    if ww ≥ tl / 2 || ww2 ≥ tl / 2 then continue
    for q1 in shortRats m1 (tl / 2 - ww / 2) do
      for q2 in shortRats m2 (tl / 2 - ww2 / 2) do
        unless Series.tele2Check c c0 b0 q1 q2 tolV do continue
        trace[lynth.interval] "complex series (tele2): prec = {prec}, q = ({q1}, {q2})"
        let chk := mkAppN (mkConst ``Series.tele2Check)
          #[mkApp (mkConst ``Ctx.make) (mkNatLit prec), c0E, b0E,
            toExpr q1, toExpr q2, rt.expr]
        let hchk ← certify chk (checkCost prec 40)
        let hc := mkApp (mkConst ``Ctx.make_valid) (mkNatLit prec)
        let pairE ← mkAppM ``Prod.mk #[toExpr q1, toExpr q2]
        let pf := mkAppN (mkConst ``Series.tele2_subtype_of_check)
          #[f, tol, mkApp (mkConst ``Ctx.make) (mkNatLit prec), hc,
            c0E, b0E, toExpr q1, toExpr q2, rt.expr,
            rt.proof, hbridge, hw, hchk]
        return some (mkApp4 (mkConst ``Subtype.mk [1]) α p pairE pf)
  return none

/-- `{p : Rat × Rat // Summable f ∧ ‖tsum f - ↑p‖ < tol}` via factorial family -/
def proveComplexFact? (goalTy : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let_expr Subtype α p := goalTy | return none
  let α ← whnfR α
  let some (a1, a2) ← prodArgs? α | return none
  unless (← whnfR a1).isConstOf ``Rat do return none
  unless (← whnfR a2).isConstOf ``Rat do return none
  let p ← whnfR p
  let .lam n _ pbody _ ← pure p | return none
  let found ← withLocalDeclD n α fun x => do
    let P := pbody.instantiate1 x
    let_expr And S I := P | return none
    let some f ← seqArgC? S ``Summable | return none
    let_expr LT.lt _ _ _ tol := I | return none
    if tol.hasFVar then return none
    return some (f, tol)
  let some (f, tol) := found | return none
  let (bodyE, hbody) ← reifyBodyC f
  let rt ← reify {} tol
  unless rt.ty == .real do return none
  let body ← evalExprVal .cplx bodyE
  let tolV ← evalExprVal .real rt.expr
  let tl ← tolLower tol
  let maxPrec := lynth.interval.maxPrec.get (← getOptions)
  for prec in precSchedule maxPrec do
    let c := Ctx.make prec
    let some c0 := Series.matchFact body | continue
    unless c0 == 1 do continue
    trace[lynth.interval] "cx fact: matched c0={c0}"
    let res ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      try
        let fk := mkApp f k
        let rhs ← mkFactRhs k
        let eq ← mkAppM ``Eq #[fk, rhs]
        let mvar ← mkFreshExprSyntheticOpaqueMVar eq
        runBridgeSimple? mvar.mvarId! f k (fun hopen => mkLambdaFVars #[k] hopen)
      catch e =>
        return (none : Option Lean.Expr)
    let some hbridge := res | continue
    for N in [8, 12, 16, 24, 32] do
      let B := Series.factEncl c body N
      let (some lo1, some hi1, some lo2, some hi2) :=
        (B.re.lo, B.re.hi, B.im.lo, B.im.hi) | continue
      let m1 := (lo1.toRat + hi1.toRat) / 2
      let ww := hi1.toRat - lo1.toRat
      let m2 := (lo2.toRat + hi2.toRat) / 2
      let ww2 := hi2.toRat - lo2.toRat
      if ww ≥ tl / 2 || ww2 ≥ tl / 2 then continue
      for q1 in shortRats m1 (tl / 2 - ww / 2) do
        for q2 in shortRats m2 (tl / 2 - ww2 / 2) do
          unless Series.factCheck c body N q1 q2 tolV do continue
          trace[lynth.interval] "complex series (fact): prec = {prec}, N = {N}, q = ({q1}, {q2})"
          let chk := mkAppN (mkConst ``Series.factCheck)
            #[mkApp (mkConst ``Ctx.make) (mkNatLit prec), bodyE, mkNatLit N,
              toExpr q1, toExpr q2, rt.expr]
          let hchk ← certify chk (checkCost prec (N * 20))
          let hc := mkApp (mkConst ``Ctx.make_valid) (mkNatLit prec)
          let pairE ← mkAppM ``Prod.mk #[toExpr q1, toExpr q2]
          let pf := mkAppN (mkConst ``Series.fact_subtype_of_check)
            #[f, tol, mkApp (mkConst ``Ctx.make) (mkNatLit prec), hc,
              bodyE, mkNatLit N, toExpr q1, toExpr q2, rt.expr,
              hbody, rt.proof, hbridge, hchk]
          return some (mkApp4 (mkConst ``Subtype.mk [1]) α p pairE pf)
  return none

/-- complex series goals (more families to come) -/

def proveComplexSelf? (goalTy : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let_expr Subtype α p := goalTy | return none
  let α ← whnfR α
  let some (a1, a2) ← prodArgs? α | return none
  unless (← whnfR a1).isConstOf ``Rat do return none
  unless (← whnfR a2).isConstOf ``Rat do return none
  let p ← whnfR p
  let .lam n _ pbody _ ← pure p | return none
  let found ← withLocalDeclD n α fun x => do
    let P := pbody.instantiate1 x
    let_expr And S I := P | return none
    let some f ← seqArgC? S ``Summable | return none
    let_expr LT.lt _ _ _ tol := I | return none
    if tol.hasFVar then return none
    return some (f, tol)
  let some (f, tol) := found | return none
  let (bodyE, hbody) ← reifyBodyC f
  let rt ← reify {} tol
  unless rt.ty == .real do return none
  let body ← evalExprVal .cplx bodyE
  let tolV ← evalExprVal .real rt.expr
  let tl ← tolLower tol
  let maxPrec := lynth.interval.maxPrec.get (← getOptions)
  for prec in precSchedule maxPrec do
    let c := Ctx.make prec
    let some c0 := Series.matchSelf body | continue
    unless c0 == 1 do continue
    trace[lynth.interval] "cx self: matched c0={c0}"
    let res ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      try
        let fk := mkApp f k
        let rhs ← mkSelfRhs k
        let eq ← mkAppM ``Eq #[fk, rhs]
        let mvar ← mkFreshExprSyntheticOpaqueMVar eq
        runBridgeSimple? mvar.mvarId! f k (fun hopen => mkLambdaFVars #[k] hopen)
      catch e =>
        return (none : Option Lean.Expr)
    let some hbridge := res | continue
    for N in [8, 12, 16, 24, 32] do
      let B := Series.selfEncl c body N
      let (some lo1, some hi1, some lo2, some hi2) :=
        (B.re.lo, B.re.hi, B.im.lo, B.im.hi) | continue
      let m1 := (lo1.toRat + hi1.toRat) / 2
      let ww := hi1.toRat - lo1.toRat
      let m2 := (lo2.toRat + hi2.toRat) / 2
      let ww2 := hi2.toRat - lo2.toRat
      if ww ≥ tl / 2 || ww2 ≥ tl / 2 then continue
      for q1 in shortRats m1 (tl / 2 - ww / 2) do
        for q2 in shortRats m2 (tl / 2 - ww2 / 2) do
          unless Series.selfCheck c body N q1 q2 tolV do continue
          let chk := mkAppN (mkConst ``Series.selfCheck)
            #[mkApp (mkConst ``Ctx.make) (mkNatLit prec), bodyE, mkNatLit N,
              toExpr q1, toExpr q2, rt.expr]
          let hchk ← certify chk (checkCost prec (N * 20))
          let hc := mkApp (mkConst ``Ctx.make_valid) (mkNatLit prec)
          let pairE ← mkAppM ``Prod.mk #[toExpr q1, toExpr q2]
          let pf := mkAppN (mkConst ``Series.self_subtype_of_check)
            #[f, tol, mkApp (mkConst ``Ctx.make) (mkNatLit prec), hc,
              bodyE, mkNatLit N, toExpr q1, toExpr q2, rt.expr,
              hbody, rt.proof, hbridge, hchk]
          return some (mkApp4 (mkConst ``Subtype.mk [1]) α p pairE pf)
  return none

/-- complex series goals (more families to come) -/


def proveComplexMers? (goalTy : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let_expr Subtype α p := goalTy | return none
  let α ← whnfR α
  let some (a1, a2) ← prodArgs? α | return none
  unless (← whnfR a1).isConstOf ``Rat do return none
  unless (← whnfR a2).isConstOf ``Rat do return none
  let p ← whnfR p
  let .lam n _ pbody _ ← pure p | return none
  let found ← withLocalDeclD n α fun x => do
    let P := pbody.instantiate1 x
    let_expr And S I := P | return none
    let some f ← seqArgC? S ``Summable | return none
    let_expr LT.lt _ _ _ tol := I | return none
    if tol.hasFVar then return none
    return some (f, tol)
  let some (f, tol) := found | return none
  let (bodyE, hbody) ← reifyBodyC f
  let rt ← reify {} tol
  unless rt.ty == .real do return none
  let body ← evalExprVal .cplx bodyE
  let tolV ← evalExprVal .real rt.expr
  let tl ← tolLower tol
  let maxPrec := lynth.interval.maxPrec.get (← getOptions)
  for prec in precSchedule maxPrec do
    let c := Ctx.make prec
    let some c0 := Series.matchMers body | continue
    unless c0 == 1 do continue
    trace[lynth.interval] "cx mers: matched c0={c0}"
    let res ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      try
        let fk := mkApp f k
        let rhs ← mkMersRhs k
        let eq ← mkAppM ``Eq #[fk, rhs]
        let mvar ← mkFreshExprSyntheticOpaqueMVar eq
        runBridgeSimple? mvar.mvarId! f k (fun hopen => mkLambdaFVars #[k] hopen)
      catch e =>
        return (none : Option Lean.Expr)
    let some hbridge := res | continue
    for N in [8, 12, 16, 24, 32] do
      let B := Series.mersEncl c body N
      let (some lo1, some hi1, some lo2, some hi2) :=
        (B.re.lo, B.re.hi, B.im.lo, B.im.hi) | continue
      let m1 := (lo1.toRat + hi1.toRat) / 2
      let ww := hi1.toRat - lo1.toRat
      let m2 := (lo2.toRat + hi2.toRat) / 2
      let ww2 := hi2.toRat - lo2.toRat
      if ww ≥ tl / 2 || ww2 ≥ tl / 2 then continue
      for q1 in shortRats m1 (tl / 2 - ww / 2) do
        for q2 in shortRats m2 (tl / 2 - ww2 / 2) do
          unless Series.mersCheck c body N q1 q2 tolV do continue
          let chk := mkAppN (mkConst ``Series.mersCheck)
            #[mkApp (mkConst ``Ctx.make) (mkNatLit prec), bodyE, mkNatLit N,
              toExpr q1, toExpr q2, rt.expr]
          let hchk ← certify chk (checkCost prec (N * 20))
          let hc := mkApp (mkConst ``Ctx.make_valid) (mkNatLit prec)
          let pairE ← mkAppM ``Prod.mk #[toExpr q1, toExpr q2]
          let pf := mkAppN (mkConst ``Series.mers_subtype_of_check)
            #[f, tol, mkApp (mkConst ``Ctx.make) (mkNatLit prec), hc,
              bodyE, mkNatLit N, toExpr q1, toExpr q2, rt.expr,
              hbody, rt.proof, hbridge, hchk]
          return some (mkApp4 (mkConst ``Subtype.mk [1]) α p pairE pf)
  return none

/-- complex series goals (more families to come) -/


def proveComplexFib? (goalTy : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let_expr Subtype α p := goalTy | return none
  let α ← whnfR α
  let some (a1, a2) ← prodArgs? α | return none
  unless (← whnfR a1).isConstOf ``Rat do return none
  unless (← whnfR a2).isConstOf ``Rat do return none
  let p ← whnfR p
  let .lam n _ pbody _ ← pure p | return none
  let found ← withLocalDeclD n α fun x => do
    let P := pbody.instantiate1 x
    let_expr And S I := P | return none
    let some f ← seqArgC? S ``Summable | return none
    let_expr LT.lt _ _ _ tol := I | return none
    if tol.hasFVar then return none
    return some (f, tol)
  let some (f, tol) := found | return none
  let (bodyE, hbody) ← reifyBodyC f
  let rt ← reify {} tol
  unless rt.ty == .real do return none
  let body ← evalExprVal .cplx bodyE
  let tolV ← evalExprVal .real rt.expr
  let tl ← tolLower tol
  let maxPrec := lynth.interval.maxPrec.get (← getOptions)
  for prec in precSchedule maxPrec do
    let c := Ctx.make prec
    let some c0 := Series.matchFib body | continue
    unless c0 == 1 do continue
    trace[lynth.interval] "cx fib: matched c0={c0}"
    let res ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      try
        let fk := mkApp f k
        let rhs ← mkFibRhs k
        let eq ← mkAppM ``Eq #[fk, rhs]
        let mvar ← mkFreshExprSyntheticOpaqueMVar eq
        runBridgeSimple? mvar.mvarId! f k (fun hopen => mkLambdaFVars #[k] hopen)
      catch e =>
        return (none : Option Lean.Expr)
    let some hbridge := res | continue
    for N in [8, 12, 16, 24, 32] do
      let oneN : Lean.Expr := toExpr (1 : ℕ)
      let hNTy ← mkAppM ``LE.le #[oneN, toExpr N]
      let hNmvar ← mkFreshExprSyntheticOpaqueMVar hNTy
      unless ← runNormNum? hNmvar.mvarId! do continue
      let hN ← instantiateMVars hNmvar
      let B := Series.fibEncl c body N
      let (some lo1, some hi1, some lo2, some hi2) :=
        (B.re.lo, B.re.hi, B.im.lo, B.im.hi) | continue
      let m1 := (lo1.toRat + hi1.toRat) / 2
      let ww := hi1.toRat - lo1.toRat
      let m2 := (lo2.toRat + hi2.toRat) / 2
      let ww2 := hi2.toRat - lo2.toRat
      if ww ≥ tl / 2 || ww2 ≥ tl / 2 then continue
      for q1 in shortRats m1 (tl / 2 - ww / 2) do
        for q2 in shortRats m2 (tl / 2 - ww2 / 2) do
          unless Series.fibCheck c body N q1 q2 tolV do continue
          let chk := mkAppN (mkConst ``Series.fibCheck)
            #[mkApp (mkConst ``Ctx.make) (mkNatLit prec), bodyE, mkNatLit N,
              toExpr q1, toExpr q2, rt.expr]
          let hchk ← certify chk (checkCost prec (N * 20))
          let hc := mkApp (mkConst ``Ctx.make_valid) (mkNatLit prec)
          let pairE ← mkAppM ``Prod.mk #[toExpr q1, toExpr q2]
          let pf := mkAppN (mkConst ``Series.fib_subtype_of_check)
            #[f, tol, mkApp (mkConst ``Ctx.make) (mkNatLit prec), hc,
              bodyE, mkNatLit N, toExpr q1, toExpr q2, rt.expr,
              hN, hbody, rt.proof, hbridge, hchk]
          return some (mkApp4 (mkConst ``Subtype.mk [1]) α p pairE pf)
  return none

/-- `¬ Summable f` via alternating-harmonic lower bound -/
def proveComplexAltHarm? (P : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let_expr Not S := P | return none
  let some f ← seqArgC? S ``Summable | return none
  let (bodyE, _) ←
    try reifyBodyC f
    catch _ => return none
  let body ←
    try evalExprVal .cplx bodyE
    catch _ => return none
  let some () := Series.matchAltHarm body | return none
  trace[lynth.interval] "cx div-altharm: matched"
  let res ← withLocalDeclD `k (mkConst ``Nat) fun k => do
    try
      let fk := mkApp f k
      let rhs ← mkAltHarmRhs k
      let eq ← mkAppM ``Eq #[fk, rhs]
      let mvar ← mkFreshExprSyntheticOpaqueMVar eq
      runBridgeSimple? mvar.mvarId! f k (fun hopen => mkLambdaFVars #[k] hopen)
    catch _ => return (none : Option Lean.Expr)
  let some hbridge := res | return none
  return some (mkAppN (mkConst ``Series.altHarm_not_summable_sound) #[f, hbridge])

/-- `¬ Summable (fun _ => 1)` via positive lower bound -/
def proveComplexConstNotSumm? (P : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let_expr Not S := P | return none
  let some f ← seqArgC? S ``Summable | return none
  let (bodyE, _) ←
    try reifyBodyC f
    catch _ => return none
  let body ←
    try evalExprVal .cplx bodyE
    catch _ => return none
  let some () := Series.matchConstOne body | return none
  let res ← withLocalDeclD `k (mkConst ``Nat) fun k => do
    try
      let fk := mkApp f k
      let rhs ← mkConstOneRhs
      let eq ← mkAppM ``Eq #[fk, rhs]
      let mvar ← mkFreshExprSyntheticOpaqueMVar eq
      runBridgeSimple? mvar.mvarId! f k (fun hopen => mkLambdaFVars #[k] hopen)
    catch _ => return (none : Option Lean.Expr)
  let some hbridge := res | return none
  return some (mkAppN (mkConst ``Series.const_not_summable_sound) #[f, hbridge])

def proveComplexNotSummable? (P : Lean.Expr) : TacticM (Option Lean.Expr) := do
  if let some pf ← proveComplexAltHarm? P then return some pf
  if let some pf ← proveComplexConstNotSumm? P then return some pf
  return none

/-- complex series goals (more families to come) -/

def proveComplexSeries? (goalTy : Lean.Expr) : TacticM (Option Lean.Expr) := do
  if let some pf ← proveComplexNotSummable? goalTy then return some pf
  if let some pf ← proveComplexTele1? goalTy then return some pf
  if let some pf ← proveComplexTele2n? goalTy then return some pf
  if let some pf ← proveComplexFact? goalTy then return some pf
  if let some pf ← proveComplexSelf? goalTy then return some pf
  if let some pf ← proveComplexMers? goalTy then return some pf
  if let some pf ← proveComplexFib? goalTy then return some pf
  let ty ← whnf goalTy
  if let some pf ← proveComplexNotSummable? ty then return some pf
  if let some pf ← proveComplexTele1? ty then return some pf
  if let some pf ← proveComplexTele2n? ty then return some pf
  if let some pf ← proveComplexFact? ty then return some pf
  if let some pf ← proveComplexSelf? ty then return some pf
  if let some pf ← proveComplexMers? ty then return some pf
  if let some pf ← proveComplexFib? ty then return some pf
  return none

end Lynth.Interval.Goals
