import Lynth.Interval.Goals.Approx
import Mathlib.Basic.Real.Sign

/-!
# Discrete witnesses `{n : ℕ // …}`, `{s : ℤ // …}`

Nat/Int floors, ceilings, `round` and `Real.sign` of closed real expressions
(`docs/interval/05-point-goals.md §3`): guess the witness from enclosure
midpoints, then discharge the defining `…_eq_iff` obligations as closed
propositions (`proveClosed?`).  Yields on anything else.

Bounds are built from `Nat.cast`/`Int.cast`/`OfNat` with pinned `ℝ` target,
so they match the `…_eq_iff` conclusions syntactically.  Each guess needs
exactly one closed check (a conjunction), keeping kernel certificates small.
Goal equations may wrap the floor side in `Nat.cast`/`Int.cast` (e.g.
`↑⌊E⌋ = ↑s`); the cast is stripped for matching and re-applied by
congruence.

Cost discipline: guesses are attempted only when the current enclosure
forces them (both bounds round the same way); the `= 0` fallback is tried
first only when a cheap peek suggests `E < 1` (resp. `E ≤ 0`).  This keeps
expensive goals (e.g. Gamma) to one enclosure schedule plus one check.
-/

namespace Lynth.Interval.Goals

open Lean Meta Elab Tactic Reify

/-- run `decide` on a closed goal, if it closes -/
def proveByDecide (goal : Lean.Expr) : TacticM (Option Lean.Expr) := do
  try
    let m ← mkFreshExprSyntheticOpaqueMVar goal
    let gs ← Tactic.run m.mvarId! (evalTactic (← `(tactic| decide)))
    if gs.isEmpty then return some (← instantiateMVars m) else return none
  catch _ => return none

/-- `proveClosed?`, catching all failures -/
def tryClosed (P : Lean.Expr) : TacticM (Option Lean.Expr) := do
  try
    return ← proveClosed? P
  catch _ => return none

/-- run plain `simp` on a closed goal (cast normalizations), if it closes -/
def proveBySimp (goal : Lean.Expr) : TacticM (Option Lean.Expr) := do
  try
    let m ← mkFreshExprSyntheticOpaqueMVar goal
    let gs ← Tactic.run m.mvarId! (evalTactic (← `(tactic| simp)))
    if gs.isEmpty then return some (← instantiateMVars m) else return none
  catch _ => return none

/-- `(n : ℝ)` OfNat literal -/
def mkOfNatR (n : Nat) : MetaM Lean.Expr :=
  mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real), some (toExpr n), none]

/-- `((n : ℕ) : ℝ)` with pinned target -/
def mkNatCastR (n : Nat) : MetaM Lean.Expr :=
  mkAppOptM ``Nat.cast #[some (mkConst ``Real), none, some (toExpr n)]

/-- `((z : ℤ) : ℝ)` with pinned target -/
def mkIntCastR (z : Int) : MetaM Lean.Expr :=
  mkAppOptM ``Int.cast #[some (mkConst ``Real), none, some (toExpr z)]

/-- application with the type parameter pinned to `ℝ` (position 0).
Remaining binders filled positionally (`none` = infer). -/
def mkAppMR (c : Lean.Name) (xs : Array (Option Lean.Expr)) : MetaM Lean.Expr :=
  mkAppOptM c (#[some (mkConst ``Real)] ++ xs)

/-- rebuild the cast function (`ℤ → ℝ` or `ℕ → ℝ`) from a cast application -/
def castFnOf (e : Lean.Expr) : Option Lean.Expr :=
  if e.getAppFn.isConstOf ``Int.cast || e.getAppFn.isConstOf ``Nat.cast then
    let args := e.getAppArgs
    if 0 < args.size then some (mkAppN e.getAppFn args.pop)
    else none
  else none

/-- `congrArg castFn pf`, fully positional.
`congrArg : ∀ {α β} {a₁ a₂} (f : α → β), a₁ = a₂ → f a₁ = f a₂`. -/
def mkCongrCast (castFn pf : Lean.Expr) : MetaM Lean.Expr :=
  mkAppOptM ``congrArg #[none, none, none, none, some castFn, some pf]

/-- strip one `Nat.cast`/`Int.cast` layer, if present (total) -/
def stripCast (e : Lean.Expr) : Lean.Expr :=
  if e.getAppFn.isConstOf ``Int.cast || e.getAppFn.isConstOf ``Nat.cast then
    e.getAppArgs.back?.getD e
  else e

/-- midpoint at the cheapest precision, if the enclosure is finite there -/
def peekMid (E : Lean.Expr) : TacticM (Option ℚ) := do
  try
    let r ← reify {} E
    let v ← evalExprVal .real r.expr
    let maxPrec := lynth.interval.maxPrec.get (← getOptions)
    match precSchedule maxPrec with
    | [] => return none
    | prec :: _ =>
      let I : Ival := v.eval (Ctx.make prec) {}
      match I.lo, I.hi with
      | some lo, some hi => return some ((lo.toRat + hi.toRat) / 2)
      | _, _ => return none
  catch _ => return none

/-- evaluate enclosures lazily: guess + check per precision, stop on success.
`go` sees both bounds so it can skip precisions that force nothing. -/
def loopPrecs (E : Lean.Expr)
    (go : ℚ → ℚ → TacticM (Option (Lean.Expr × Lean.Expr))) :
    TacticM (Option (Lean.Expr × Lean.Expr)) := do
  let r ← try reify {} E catch _ => return none
  let v ← try evalExprVal .real r.expr catch _ => return none
  let maxPrec := lynth.interval.maxPrec.get (← getOptions)
  for prec in precSchedule maxPrec do
    let I : Ival := v.eval (Ctx.make prec) {}
    match I.lo, I.hi with
    | some lo, some hi =>
      if let some a ← go lo.toRat hi.toRat then return some a
    | _, _ => pure ()
  return none

/-- `⌊E⌋₊ = 0` via `E < 1` -/
def natFloorZero (E : Lean.Expr) : TacticM (Option (Lean.Expr × Lean.Expr)) := do
  if let some hlt ← tryClosed (← mkAppM ``LT.lt #[E, ← mkOfNatR 1]) then
    let q := toExpr (0 : Nat)
    return some (q, ← mkAppM ``Iff.mpr
      #[← mkAppMR ``Nat.floor_eq_zero #[none, none, none, some E, none], hlt])
  return none

/-- forced nonzero guesses: only when both bounds floor together -/
def natFloorLoop (E : Lean.Expr) : TacticM (Option (Lean.Expr × Lean.Expr)) :=
  loopPrecs E fun lo hi => do
    if ⌊lo⌋ != ⌊hi⌋ then return none
    let g : Nat := Int.toNat ⌊(lo + hi) / 2⌋
    let gE := toExpr g
    let gR ← mkNatCastR g
    let oneR ← mkOfNatR 1
    let gp1R ← mkAppM ``HAdd.hAdd #[gR, oneR]
    let both : Lean.Expr := mkApp (mkApp (mkConst ``And) (← mkAppM ``LE.le #[gR, E]))
      (← mkAppM ``LT.lt #[E, gp1R])
    if let some hconj ← tryClosed both then
      let hn ← match ← proveByDecide (← mkAppM ``Ne #[gE, toExpr (0 : Nat)]) with
        | some h => pure h
        | none => return none
      let iffPf ← mkAppMR ``Nat.floor_eq_iff'
        #[none, none, none, some E, some gE, none, some hn]
      let pf ← mkAppM ``Iff.mpr #[iffPf, hconj]
      return some (gE, pf)
    return none

/-- `{n // n = ⌊E⌋₊}` or flipped: returns `(candidate, ⌊E⌋₊ = candidate)` -/
def natFloorWit (E : Lean.Expr) : TacticM (Option (Lean.Expr × Lean.Expr)) := do
  let pm ← peekMid E
  -- zero first only when the cheap enclosure suggests `E < 1`
  if pm.any (fun q => decide (q < 1)) then
    if let some r ← natFloorZero E then return some r
  if let some r ← natFloorLoop E then return some r
  -- enclosure says `E ≥ 1`: the zero case is impossible, don't pay for it
  if pm.all (fun q => decide (1 ≤ q)) then return none
  natFloorZero E

/-- `⌈E⌉₊ = 0` via `E ≤ 0` -/
def natCeilZero (E : Lean.Expr) : TacticM (Option (Lean.Expr × Lean.Expr)) := do
  if let some hle ← tryClosed (← mkAppM ``LE.le #[E, ← mkOfNatR 0]) then
    let q := toExpr (0 : Nat)
    return some (q, ← mkAppM ``Iff.mpr
      #[← mkAppMR ``Nat.ceil_eq_zero #[none, none, none, some E], hle])
  return none

/-- `{n // n = ⌈E⌉₊}` or flipped -/
def natCeilWit (E : Lean.Expr) : TacticM (Option (Lean.Expr × Lean.Expr)) := do
  let pm ← peekMid E
  if pm.any (fun q => decide (q ≤ 0)) then
    if let some r ← natCeilZero E then return some r
  let r ← loopPrecs E fun lo hi => do
    if ⌈lo⌉₊ != ⌈hi⌉₊ then return none
    let g : Nat := ⌈(lo + hi) / 2⌉₊
    if g = 0 then return none
    let gE := toExpr g
    let hne ← match ← proveByDecide (← mkAppM ``Ne #[gE, toExpr (0 : Nat)]) with
      | some h => pure h
      | none => return none
    let gm1R ← mkNatCastR (g - 1)
    let gR ← mkNatCastR g
    let c1 ← mkAppM ``LT.lt #[gm1R, E]
    let c2 ← mkAppM ``LE.le #[E, gR]
    let both : Lean.Expr := mkApp (mkApp (mkConst ``And) c1) c2
    if let some hconj ← tryClosed both then
      let iffPf ← mkAppMR ``Nat.ceil_eq_iff
        #[none, none, none, some E, some gE, some hne]
      let pf ← mkAppM ``Iff.mpr #[iffPf, hconj]
      return some (gE, pf)
    return none
  if let some r := r then return some r
  if pm.all (fun q => decide (0 < q)) then return none
  natCeilZero E

/-- `{n : ℤ // n = ⌊E⌋}` or flipped -/
def intFloorWit (E : Lean.Expr) : TacticM (Option (Lean.Expr × Lean.Expr)) :=
  loopPrecs E fun lo hi => do
    if ⌊lo⌋ != ⌊hi⌋ then return none
    let z : Int := ⌊(lo + hi) / 2⌋
    let zE := toExpr z
    let zR ← mkIntCastR z
    let oneR ← mkOfNatR 1
    let zp1R ← mkAppM ``HAdd.hAdd #[zR, oneR]
    let c1 ← mkAppM ``LE.le #[zR, E]
    let c2 ← mkAppM ``LT.lt #[E, zp1R]
    let both : Lean.Expr := mkApp (mkApp (mkConst ``And) c1) c2
    if let some hconj ← tryClosed both then
      let iffPf ← mkAppMR ``Int.floor_eq_iff #[none, none, none, some zE, some E]
      let pf ← mkAppM ``Iff.mpr #[iffPf, hconj]
      return some (zE, pf)
    return none

/-- `{n : ℤ // n = ⌈E⌉}` or flipped -/
def intCeilWit (E : Lean.Expr) : TacticM (Option (Lean.Expr × Lean.Expr)) :=
  loopPrecs E fun lo hi => do
    if ⌈lo⌉ != ⌈hi⌉ then return none
    let z : Int := ⌈(lo + hi) / 2⌉
    let zE := toExpr z
    let zR ← mkIntCastR z
    let oneR ← mkOfNatR 1
    let zm1R ← mkAppM ``HSub.hSub #[zR, oneR]
    let c1 ← mkAppM ``LT.lt #[zm1R, E]
    let c2 ← mkAppM ``LE.le #[E, zR]
    let both : Lean.Expr := mkApp (mkApp (mkConst ``And) c1) c2
    if let some hconj ← tryClosed both then
      let iffPf ← mkAppMR ``Int.ceil_eq_iff #[none, none, none, some zE, some E]
      let pf ← mkAppM ``Iff.mpr #[iffPf, hconj]
      return some (zE, pf)
    return none

/-- `{s : ℤ // round E = s}` or flipped.
`round_eq_iff : round x = n ↔ x ∈ Ico (↑n - 1/2) (↑n + 1/2)`;
`Set.mem_Ico : ∀ {a b x}, x ∈ Ico a b ↔ a ≤ x ∧ x < b` (binders α, inst, a, b, x). -/
def intRoundWit (E : Lean.Expr) : TacticM (Option (Lean.Expr × Lean.Expr)) := do
  let halfR ← mkAppM ``HDiv.hDiv #[← mkOfNatR 1, ← mkOfNatR 2]
  loopPrecs E fun lo hi => do
    if round lo != round hi then return none
    let z : Int := round ((lo + hi) / 2)
    let zE := toExpr z
    let zR ← mkIntCastR z
    let loR ← mkAppM ``HSub.hSub #[zR, halfR]
    let hiR ← mkAppM ``HAdd.hAdd #[zR, halfR]
    let c1 ← mkAppM ``LE.le #[loR, E]
    let c2 ← mkAppM ``LT.lt #[E, hiR]
    let bothIco : Lean.Expr := mkApp (mkApp (mkConst ``And) c1) c2
    if let some hconj ← tryClosed bothIco then
      let icoPf ← mkAppOptM ``Set.mem_Ico
        #[some (mkConst ``Real), none, some loR, some hiR, some E]
      let memPf ← mkAppM ``Iff.mpr #[icoPf, hconj]
      return some (zE, ← mkAppM ``Iff.mpr
        #[← mkAppMR ``round_eq_iff #[none, none, none, none, some E, some zE], memPf])
    return none

/-- cast bridge: `hs : sign E = r` (lemma's `r`) to `sign E = ↑q` -/
def castBridge (hs : Lean.Expr) (q : Int) : TacticM (Option Lean.Expr) := do
  let hsTy ← inferType hs
  let r := hsTy.getAppArgs.back?.getD hsTy
  let qr ← mkIntCastR q
  let goal ← mkAppM ``Eq #[r, qr]
  if let some hcast ← proveBySimp goal then
    return some (← mkAppM ``Eq.trans #[hs, hcast])
  if let some hcast ← tryClosed goal then
    return some (← mkAppM ``Eq.trans #[hs, hcast])
  return none

/-- `{s : ℤ // Real.sign E = ↑s}` or flipped (exact `±1` only) -/
def intSignWit (E : Lean.Expr) : TacticM (Option (Lean.Expr × Lean.Expr)) := do
  let maxPrec := lynth.interval.maxPrec.get (← getOptions)
  let r ← try reify {} E catch _ => return none
  let v ← try evalExprVal .real r.expr catch _ => return none
  for prec in precSchedule maxPrec do
    let I : Ival := v.eval (Ctx.make prec) {}
    match I.lo, I.hi with
    | some a, _ =>
      if Dy.isPos a then
        if let some h ← tryClosed (← mkAppM ``LT.lt #[← mkOfNatR 0, E]) then
          let hs ← mkAppM ``Real.sign_of_pos #[h]
          if let some pf ← castBridge hs 1 then
            return some (toExpr (1 : Int), pf)
        else pure ()
      else pure ()
    | _, _ => pure ()
    match I.lo, I.hi with
    | _, some b =>
      if Dy.isNeg b then
        if let some h ← tryClosed (← mkAppM ``LT.lt #[E, ← mkOfNatR 0]) then
          let hs ← mkAppM ``Real.sign_of_neg #[h]
          if let some pf ← castBridge hs (-1) then
            return some (toExpr (-1 : Int), pf)
        else pure ()
      else pure ()
    | _, _ => pure ()
  return none

/-- head constants handled by the discrete workers -/
def isFloorHead (f : Lean.Expr) : Bool :=
  f.isConstOf ``Nat.floor || f.isConstOf ``Nat.ceil ||
    f.isConstOf ``Int.floor || f.isConstOf ``Int.ceil ||
    f.isConstOf ``round || f.isConstOf ``Real.sign

/-- dispatch on `{n : Nat…}` / `{s : ℤ…}` witness goals -/
def proveDiscreteSubtype? (goalTy : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let_expr Subtype α p := goalTy | return none
  unless (α.isConstOf ``Nat || α.isConstOf ``Int) do return none
  let p ← whnfR p
  let .lam n _ body _ := p | return none
  withLocalDeclD n α fun x => do
    let P := body.instantiate1 x
    let_expr Eq _ lhs rhs := P | return none
    -- strip one cast layer per side, then match (bare var | floor app).
    -- `flip = true` iff the variable is on the left.
    let lstr := stripCast lhs
    let rstr := stripCast rhs
    let (E, flip, fhead) ←
      if lstr == x then
        if isFloorHead rstr.getAppFn then pure (rstr.appArg!, true, rstr.getAppFn)
        else return none
      else if rstr == x then
        if isFloorHead lstr.getAppFn then pure (lstr.appArg!, false, lstr.getAppFn)
        else return none
      else return none
    if E.hasFVar || E.hasMVar then return none
    let worker : Lean.Expr → TacticM (Option (Lean.Expr × Lean.Expr)) :=
      match fhead with
      | f =>
        if f.isConstOf ``Nat.floor then natFloorWit
        else if f.isConstOf ``Nat.ceil then natCeilWit
        else if f.isConstOf ``Int.floor then intFloorWit
        else if f.isConstOf ``Int.ceil then intCeilWit
        else if f.isConstOf ``round then intRoundWit
        else if f.isConstOf ``Real.sign then fun _ => intSignWit E
        else fun _ => return none
    let some (qE, pfFloor) ← worker E | return none
    -- pfFloor : `F = q` with `F` the stripped floor side.  If the goal wraps
    -- the floor side in a cast (`↑F`), lift by congruence; then orient.
    let floorSide := if flip then rhs else lhs
    let pfW : Lean.Expr ← match castFnOf floorSide with
      | some cf => mkCongrCast cf pfFloor
      | none => pure pfFloor
    let pf : Lean.Expr ← if flip then mkAppM ``Eq.symm #[pfW] else pure pfW
    return some (mkApp4 (mkConst ``Subtype.mk [1]) α p qE pf)

end Lynth.Interval.Goals
