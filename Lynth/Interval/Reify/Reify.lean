module

public meta import Lean
public meta import Lynth.Interval.Core.Ty
meta import all Lynth.Interval.Reify.Registry
import all Lynth.Interval.Reify.Registry
meta import all Lynth.Interval.Reify.ExactAttr
import all Lynth.Interval.Reify.ExactAttr
meta import all Lynth.Interval.Fns.Arith
import all Lynth.Interval.Fns.Arith
meta import Mathlib.Tactic.NormNum.Core
meta import Mathlib.Tactic.NormNum.Basic
meta import Mathlib.Tactic.NormNum.DivMod
meta import Mathlib.Tactic.NormNum.Pow
meta import Mathlib.Tactic.NormNum.Inv
meta import Mathlib.Tactic.NormNum.OfScientific
meta import Mathlib.Analysis.Complex.Basic
meta import Qq

/-!
# Reifier: Lean terms → typed `Expr` with denotation proofs

`reify rc e` returns `(t, eE, h)` with `eE : Expr t` and `h : e = eE.denote ρ`
(`ρ = rc.senv`).  Steps (first success wins, `docs/interval/03 §8`):
variables, exact numerals (norm_num), finite sums, registry patterns,
unfolding of user definitions, atoms.
-/

meta section

namespace Lynth.Interval.Reify

open Lean Meta Qq

/-- a variable of the reified expression -/
structure RVar where
  term : Lean.Expr
  ty : Ty
  /-- position among the variables of the same type, 0 = outermost -/
  level : Nat

structure RCtx where
  vars : Array RVar := #[]
  /-- the `SEnv` term the denotations refer to -/
  senv : Lean.Expr := mkAppN (mkConst ``SEnv.mk)
    #[mkApp (mkConst ``List.nil [0]) (mkConst ``Nat),
      mkApp (mkConst ``List.nil [0]) (mkConst ``Int),
      mkApp (mkConst ``List.nil [0]) (mkConst ``Real),
      mkApp (mkConst ``List.nil [0]) (mkConst ``Complex),
      mkApp (mkConst ``List.nil [0]) (mkConst ``Rat)]
  /-- allow unknown subterms to become variables -/
  atoms : Bool := false
  /-- unfolding budget -/
  depth : Nat := 16

structure Reified where
  ty : Ty
  expr : Lean.Expr
  /-- `orig = Expr.denote expr senv` -/
  proof : Lean.Expr
deriving Inhabited

def RCtx.count (rc : RCtx) (t : Ty) : Nat := (rc.vars.filter (·.ty == t)).size

/-- push a variable (innermost) -/
def RCtx.push (rc : RCtx) (term : Lean.Expr) (t : Ty) : RCtx :=
  { rc with
    vars := rc.vars.push { term, ty := t, level := rc.count t }
    senv := mkApp3 (mkConst ``SEnv.push) rc.senv (toExpr t) term }

def mkDenote (t : Ty) (e senv : Lean.Expr) : Lean.Expr :=
  mkApp3 (mkConst ``Expr.denote) (toExpr t) e senv

/-- `e = (Expr.var t i).denote ρ` holds by `rfl` -/
def mkVarReified (rc : RCtx) (t : Ty) (e : Lean.Expr) (idx : Nat) : MetaM Reified := do
  let ex := mkApp2 (mkConst ``Expr.var) (toExpr t) (mkNatLit idx)
  let ty ← mkEq e (mkDenote t ex rc.senv)
  let pf ← mkExpectedTypeHint (← mkEqRefl e) ty
  return ⟨t, ex, pf⟩

/-! ### Exact numerals -/

/-- `e = e'` from two norm_num results with the same raw normal form -/
def normNumEq? {u : Level} {α : Q(Type u)} (e e' : Q($α)) : MetaM (Option Lean.Expr) := do
  try
    let r1 ← Mathlib.Meta.NormNum.derive e
    let r2 ← Mathlib.Meta.NormNum.derive e'
    let ⟨raw1, p1⟩ := r1.toRawEq
    let ⟨raw2, p2⟩ := r2.toRawEq
    unless ← isDefEq raw1 raw2 do return none
    return some (← mkEqTrans p1 (← mkEqSymm p2))
  catch _ => return none

/-- rational value of a closed numeral expression (via norm_num) -/
def ratValue? {u : Level} {α : Q(Type u)} (e : Q($α)) : MetaM (Option ℚ) := do
  try
    let r ← Mathlib.Meta.NormNum.derive e
    return r.toRat
  catch _ => return none

/-- heads that are never worth sending to norm_num -/
def isTranscendentalHead (e : Lean.Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => (`Real).isPrefixOf n || (`Complex).isPrefixOf n && n != ``Complex.ofReal
  | _ => false

/-- head constants of `lynth_exact` left-hand sides, minus generic heads -/
def exactTriggers : MetaM (Array Name) := do
  let some ext ← getSimpExtension? `lynth_exact | return #[]
  let thms ← ext.getTheorems
  let generic := [``Finset.sum, ``Finset.prod, ``Polynomial.eval, ``HAdd.hAdd, ``HMul.hMul,
    ``HSub.hSub, ``HDiv.hDiv, ``Neg.neg, ``HPow.hPow, ``Nat.cast, ``Int.cast, ``Rat.cast]
  let mut out := #[]
  for tree in [thms.post, thms.pre] do
    for (k, _) in tree.root.toList do
      if let .const n _ := k then
        unless generic.contains n || out.contains n do out := out.push n
  return out

/-- `Finset.range n` with a numeral `n > 64` (never unrolled by the exact path) -/
def hasBigRange (e : Lean.Expr) : Bool :=
  (e.find? fun s => s.isAppOfArity ``Finset.range 1 && (s.appArg!.nat?.any (· > 64))).isSome

/-- `norm_num [lynth_exact]` on a closed term mentioning a trigger -/
def simpExact? (e : Lean.Expr) : MetaM (Option Simp.Result) := do
  let some ext ← getSimpExtension? `lynth_exact | return none
  let triggers ← exactTriggers
  unless (e.find? fun s => match s with | .const n _ => triggers.contains n | _ => false).isSome do
    return none
  if hasBigRange e then return none
  try
    let ctx ← Simp.mkContext {} (simpTheorems := #[← getSimpTheorems, ← ext.getTheorems])
      (congrTheorems := ← getSimpCongrTheorems)
    return some (← Mathlib.Meta.NormNum.deriveSimp ctx #[← Simp.getSimprocs] true e)
  catch _ => return none

/-- `(q, e = mk q)`: plain norm_num first, then the `lynth_exact` simp set -/
def ratEq? {u : Level} {α : Q(Type u)} (e : Q($α)) (mk : ℚ → Option Q($α)) :
    MetaM (Option (ℚ × Lean.Expr)) := do
  if let some q ← ratValue? e then
    if let some c := mk q then
      if let some pf ← normNumEq? e c then return some (q, pf)
  let some r ← simpExact? e | return none
  let e' : Q($α) := r.expr
  let some q ← ratValue? e' | return none
  let some c := mk q | return none
  let some pf ← normNumEq? e' c | return none
  return some (q, ← mkEqTrans (← r.getProof) pf)

def exact? (t : Ty) (e : Lean.Expr) (senv : Lean.Expr) : MetaM (Option Reified) := do
  if e.hasFVar || e.hasMVar || isTranscendentalHead e || hasBigRange e then return none
  match t with
  | .real =>
    let some (q, pf) ← ratEq? (α := q(ℝ)) e (fun q => let qE : Q(ℚ) := toExpr q; some q(($qE : ℝ)))
      | return none
    return some ⟨.real, mkApp (mkConst ``Expr.lit) (toExpr q), pf⟩
  | .nat =>
    let some (q, pf) ← ratEq? (α := q(ℕ)) e
        (fun q => if q.den == 1 && q.num ≥ 0 then some (mkNatLit q.num.toNat) else none)
      | return none
    return some ⟨.nat, mkApp (mkConst ``Expr.natLit) (mkNatLit q.num.toNat), pf⟩
  | .int =>
    let some (q, pf) ← ratEq? (α := q(ℤ)) e
        (fun q => if q.den == 1 then some (toExpr q.num) else none)
      | return none
    return some ⟨.int, mkApp (mkConst ``Expr.intLit) (toExpr q.num), pf⟩
  | .cplx => return none
  | .rat =>
    let some (q, pf) ← ratEq? (α := q(ℚ)) e (fun q => some (toExpr q))
      | return none
    return some ⟨.rat, mkApp (mkConst ``Expr.rlit) (toExpr q), pf⟩
  | .list _ => return none

/-! ### Unfolding -/

/-- library modules whose definitions are *not* unfolded -/
def isLibraryDecl (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    (`Mathlib).isPrefixOf m || (`Init).isPrefixOf m || (`Lean).isPrefixOf m ||
      (`Std).isPrefixOf m || (`Batteries).isPrefixOf m || (`Lynth).isPrefixOf m

/-- delta-unfold a user definition at the head -/
def unfoldHead? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let .const n _ := e.getAppFn | return none
  if isLibraryDecl (← getEnv) n then return none
  let some e' ← delta? e (fun m => m == n) | return none
  return some e'.headBeta

/-- names referenced without imports (resolved at tactic-run time, so the
reifier stays decoupled from `Fns`/`Mathlib` leaves) -/
def nInsertInsert : Name := .str (.str .anonymous "Insert") "insert"
def nMultisetInsert : Name := .str (.str .anonymous "Multiset") "insert"
def nSingletonSingleton : Name := .str (.str .anonymous "Singleton") "singleton"
def nMultisetSingleton : Name := .str (.str .anonymous "Multiset") "singleton"
def nMultisetEmpty : Name := .str (.str .anonymous "Multiset") "empty"
def nEmptyCollection : Name := .str (.str .anonymous "EmptyCollection") "emptyCollection"
def nMultisetOfList : Name := .str (.str .anonymous "Multiset") "ofList"
def nQuotMk : Name := .str (.str .anonymous "Quot") "mk"
def nComplexHGFun : Name := .str (.str .anonymous "Complex") "HGFun"
def nFnsHGFunL : Name :=
  .str (.str (.str (.str .anonymous "Lynth") "Interval") "Fns") "HGFunL"

/-- element type of a `Multiset _` term -/
def msElemTy? (ms : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let ty ← whnfR (← inferType ms)
  if ty.getAppFn.isConstOf ``Multiset then
    let args := ty.getAppArgs
    if 0 < args.size then return some args[0]! else return none
  else return none

/-- multiset literal term → (list term, `ms = ↑list`); supports `∅`,
`insert`/`singleton` spines and list coercions (fuel-bounded). Equalities
are kernel-checked `rfl`s, so unsupported shapes fail loudly. -/
def msToList? : Nat → Lean.Expr → MetaM (Option (Lean.Expr × Lean.Expr))
  | 0, _ => return none
  | fuel + 1, ms => do
    let f := ms.getAppFn
    let args := ms.getAppArgs
    -- insert spine (raw or instance-projected heads)
    if f.isConstOf nInsertInsert || f.isConstOf nMultisetInsert then
      if args.size < 2 then return none
      let x := args[args.size - 2]!
      let s := args[args.size - 1]!
      let some (ns, _) ← msToList? fuel s | return none
      let nl ← mkAppM ``List.cons #[x, ns]
      let some α ← msElemTy? ms | return none
      let coe := mkAppN (mkConst nMultisetOfList) #[α, nl]
      let pf ← mkExpectedTypeHint (← mkEqRefl ms) (← mkEq ms coe)
      return some (nl, pf)
    else if f.isConstOf nSingletonSingleton || f.isConstOf nMultisetSingleton then
      if args.size < 1 then return none
      let x := args[args.size - 1]!
      let α ← inferType x
      let nil ← mkAppOptM ``List.nil #[some α]
      let nl ← mkAppM ``List.cons #[x, nil]
      let some α ← msElemTy? ms | return none
      let coe := mkAppN (mkConst nMultisetOfList) #[α, nl]
      let pf ← mkExpectedTypeHint (← mkEqRefl ms) (← mkEq ms coe)
      return some (nl, pf)
    else
      let ms' ← whnfD ms
      let f' := ms'.getAppFn
      let args' := ms'.getAppArgs
      -- empty
      if f'.isConstOf nMultisetEmpty || f'.isConstOf nEmptyCollection then
        let some α ← msElemTy? ms | return none
        let nil ← mkAppOptM ``List.nil #[some α]
        let coe := mkAppN (mkConst nMultisetOfList) #[α, nil]
        let pf ← mkExpectedTypeHint (← mkEqRefl ms) (← mkEq ms coe)
        return some (nil, pf)
      -- list coercion / quotient constructor: take the list directly
      else if f'.isConstOf nMultisetOfList || f'.isConstOf nQuotMk then
        if args'.size < 1 then return none
        let nl := args'[args'.size - 1]!
        let some α ← msElemTy? ms | return none
        let coe := mkAppN (mkConst nMultisetOfList) #[α, nl]
        let pf ← mkExpectedTypeHint (← mkEqRefl ms) (← mkEq ms coe)
        return some (nl, pf)
      else return none

/-! ### Main reifier -/

partial def reify (rc : RCtx) (e : Lean.Expr) : MetaM Reified := do
  let e ← instantiateMVars e
  let some t ← tyOfType? (← inferType e)
    | throwError "lynth interval: unsupported type of {e}"
  -- 1. variables
  for v in rc.vars do
    if v.ty == t && v.term == e then
      return ← mkVarReified rc t e (rc.count t - 1 - v.level)
  -- 2. exact numerals
  if let some r ← exact? t e rc.senv then
    return { r with proof := ← mkExpectedTypeHint r.proof (← mkEq e (mkDenote t r.expr rc.senv)) }
  -- 2b. list literals (closed spines, elementwise)
  if let some r ← reifyListLit? rc t e then return r
  -- 2c. complex literals (normalize + delegate to `ofRealC`)
  if let some r ← reifyCplxLit? rc t e then return r
  -- 2d. multiset `HGFun` (normalize args to `HGFunL` lists)
  if let some r ← reifyMultisetHGFun? rc t e then return r
  -- 3. finite sums
  if let some r ← reifySum? rc t e then return r
  -- 4. registry (single unified table)
  for cand in ← candidatesNary e do
    if let some r ← tryNary rc t cand e then return r
  if let some r ← reifyRatCast? rc t e then return r
  -- 5. unfold user definitions
  if rc.depth > 0 then
    if let some e' ← unfoldHead? e then
      let r ← reify { rc with depth := rc.depth - 1 } e'
      return { r with proof := ← mkExpectedTypeHint r.proof (← mkEq e (mkDenote t r.expr rc.senv)) }
  -- 6. atoms
  if rc.atoms then
    throwError "lynth interval: atom {e} (atoms must be registered as variables by the caller)"
  throwError "lynth interval: no registry entry for {e}"
where
  /-- `∑ k ∈ Finset.range n, f k` -/
  reifySum? (rc : RCtx) (t : Ty) (e : Lean.Expr) : MetaM (Option Reified) := do
    let_expr Finset.sum ι _ _ s f := e | return none
    unless (← whnfR ι).isConstOf ``Nat do return none
    let_expr Finset.range n := s | return none
    let rn ← reify rc n
    unless rn.ty == .nat do return none
    withLocalDeclD `k (mkConst ``Nat) fun k => do
      let body := (mkApp f k).headBeta
      let rc' := rc.push k .nat
      let rb ← reify rc' body
      unless rb.ty == t do throwError "lynth interval: sum body type mismatch"
      let hf ← mkLambdaFVars #[k] rb.proof
      let pf := mkAppN (mkConst ``Expr.sum_eq) #[toExpr t, rn.expr, rb.expr, rc.senv, n, f, rn.proof, hf]
      let ex := mkApp3 (mkConst ``Expr.sum) (toExpr t) rn.expr rb.expr
      let pf ← mkExpectedTypeHint pf (← mkEq e (mkDenote t ex rc.senv))
      return some ⟨t, ex, pf⟩
  /-- closed `List.cons`/`List.nil` spine at element type `t`, elementwise -/
  reifyListLit? (rc : RCtx) (t : Ty) (e : Lean.Expr) : MetaM (Option Reified) := do
    let te ← match t with | .list te => pure te | _ => return none
    let e ← instantiateMVars e
    if e.hasFVar || e.hasMVar then return none
    let rc' : RCtx := { senv := rc.senv }
    let rec go (fuel : Nat) (e : Lean.Expr) :
        MetaM (Option (Lean.Expr × Lean.Expr)) :=
      match fuel with
      | 0 => return none
      | fuel + 1 => do
        let e ← instantiateMVars e
        match e.getAppFn with
        | .const ``List.nil _ =>
          let ex ← mkAppOptM ``ExprList.nil #[some (toExpr te)]
          return some (ex, ← mkEqRefl e)
        | .const ``List.cons _ =>
          let args := e.getAppArgs
          if args.size < 3 then return none
          let r ← reify rc' args[1]!
          unless r.ty == te do return none
          let some (exs, pfs) ← go fuel args[2]! | return none
          let ex ← mkAppOptM ``ExprList.cons #[some (toExpr te), some r.expr, some exs]
          let α ← inferType args[1]!
          let consF := mkApp (mkConst ``List.cons [0]) α
          let pf ← mkAppM ``congrArg₂ #[consF, r.proof, pfs]
          return some (ex, pf)
        | _ => return none
    let some (exs, pfTail) ← go 64 e | return none
    let ex ← mkAppOptM ``Expr.clist #[some (toExpr te), some exs]
    let pf ← mkExpectedTypeHint pfTail (← mkEq e (mkDenote (.list te) ex rc.senv))
    return some ⟨.list te, ex, pf⟩
  /-- `Complex.HGFun` over multiset literals: normalize both parameter
  multisets to lists and delegate to the `HGFunL` entry. The bridge
  `HGFun a b z = HGFunL na nb z` is definitional (checked on the spot). -/
  reifyMultisetHGFun? (rc : RCtx) (t : Ty) (e : Lean.Expr) : MetaM (Option Reified) := do
    unless t == .cplx do return none
    let fn := e.getAppFn
    unless fn.isConstOf nComplexHGFun do return none
    let args := e.getAppArgs
    if args.size < 3 then return none
    let a := args[args.size - 3]!
    let b := args[args.size - 2]!
    let z := args[args.size - 1]!
    let some (na, _) ← msToList? 64 a | return none
    let some (nb, _) ← msToList? 64 b | return none
    let eL := mkAppN (mkConst nFnsHGFunL) #[na, nb, z]
    let r ← reify rc eL
    unless r.ty == .cplx do return none
    let heq ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e eL)
    return some ⟨.cplx, r.expr, ← mkEqTrans heq r.proof⟩
  /-- complex literals: normalize `q : ℂ` to `Complex.ofReal ↑q` and
  delegate to the `ofRealC` entry -/
  reifyCplxLit? (rc : RCtx) (t : Ty) (e : Lean.Expr) : MetaM (Option Reified) := do
    unless t == .cplx do return none
    if e.hasFVar || e.hasMVar || isTranscendentalHead e || hasBigRange e then return none
    let some (q, pf) ← ratEq? (α := q(ℂ)) e
        (fun q => let qE : Q(ℚ) := toExpr q; some q(($qE : ℂ)))
      | return none
    let qE : Q(ℚ) := toExpr q
    let X : Q(ℝ) := q(($qE : ℝ))
    let e' : Lean.Expr := mkApp (mkConst ``Complex.ofReal) X
    let pf2 : Lean.Expr := q((Complex.ofReal_ratCast $qE).symm)
    let hnorm ← mkEqTrans pf pf2
    let rc' : RCtx := { senv := rc.senv }
    for cand in ← candidatesNary e' do
      if let some r ← tryNary rc' .cplx cand e' then
        return some ⟨.cplx, r.expr, ← mkEqTrans hnorm r.proof⟩
    return none
  /-- try one registry entry (unified `CFn`/`Fn` table) -/
  tryNary (rc : RCtx) (t : Ty) (ent : NaryEntry) (e : Lean.Expr) : MetaM (Option Reified) := do
    unless ent.res == t do return none
    let s ← saveState
    let (mvars, _, body) ← lambdaMetaTelescope ent.pattern
    unless ← withTransparency .instances (isDefEq body e) do
      s.restore; return none
    let args ← mvars.mapM instantiateMVars
    if args.any (·.hasMVar) then s.restore; return none
    try
      let n := ent.tys.size
      let f := ent.cfn
      let ρ := rc.senv
      let tysE := toExpr ent.tys.toList
      let rE := toExpr ent.res
      -- reified head per position; rat positions take closed ℚ directly to `rlit`
      let mut exs : Array Lean.Expr := #[]
      let mut vs : Array Lean.Expr := #[]
      let mut comps : Array Lean.Expr := #[]
      for i in [0:n] do
        let c := ent.tys[i]!
        let a := args[i]!
        match c with
        | .rat =>
          if a.hasFVar || a.hasMVar then
            throwError ("lynth interval: rat argument {i} of `{ent.decl}` must be " ++
              "a closed rational literal or chain")
          let litE := mkApp (mkConst ``Expr.rlit) a
          exs := exs.push litE
          vs := vs.push a
          comps := comps.push (← mkEqRefl (mkDenote .rat litE ρ))
        | _ =>
          let r ← reify rc a
          unless r.ty == c do throw (Exception.error .missing "type mismatch")
          exs := exs.push r.expr
          vs := vs.push a
          comps := comps.push r.proof
      -- `CArg` / `CVal` chains (right-nested) and the `Agree` conjunction
      let mut xsE := mkConst ``CArg.nil
      let mut vsE := mkConst ``CVal.nil
      let mut hagE := mkConst ``True.intro
      for j in List.range n |>.reverse do
        let cE := toExpr ent.tys[j]!
        xsE ← mkAppOptM ``CArg.cons #[some cE, none, some exs[j]!, some xsE]
        vsE ← mkAppOptM ``CVal.cons #[some cE, none, some vs[j]!, some vsE]
        hagE := ← mkAppM ``And.intro #[comps[j]!, hagE]
      let denE := mkAppN (mkConst ``Expr.CArg.denoteArgs) #[ρ, tysE, xsE]
      let hdsE ← mkEqRefl denE
      let hgE ← mkEqRefl e
      -- `rat` results cannot appear here (no node form for them); they flow
      -- through `reifyRatCast?` below instead.
      if ent.res == .rat then
        s.restore; return none
      let ex ← mkAppOptM ``Expr.call #[none, none, some f, some xsE]
      let pf := mkAppN (mkConst ``Expr.call_eq)
        #[tysE, rE, f, xsE, ρ, vsE, denE, e, hdsE, hagE, hgE]
      check pf
      return some ⟨t, ex, pf⟩
    catch e =>
      trace[lynth.interval] "nary `{ent.decl}` failed: {e.toMessageData}"
      s.restore; return none
  /-- `↑q : ℝ` for closed `q : ℚ` (covers rat-result custom calls, which plain
  `exact?` cannot evaluate): reified as `Expr.lit q`, sound by `rfl`. -/
  reifyRatCast? (rc : RCtx) (t : Ty) (e : Lean.Expr) : MetaM (Option Reified) := do
    unless t == .real do return none
    unless e.getAppFn.isConstOf ``Rat.cast do return none
    let q := e.appArg!
    let q ← instantiateMVars q
    if q.hasFVar || q.hasMVar then
      throwError "lynth interval: cast argument must be a closed rational literal or chain"
    let ex := mkApp (mkConst ``Expr.lit) q
    let pf ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e (mkDenote t ex rc.senv))
    return some ⟨t, ex, pf⟩

/-! ### Propositions -/

structure RProp where
  expr : Lean.Expr
  /-- `P = PropExpr.denote expr senv` -/
  proof : Lean.Expr
deriving Inhabited

partial def reifyProp (rc : RCtx) (P : Lean.Expr) : MetaM RProp := do
  let P ← instantiateMVars P
  let ρ := rc.senv
  match_expr P with
  | And p q =>
    let rp ← reifyProp rc p; let rq ← reifyProp rc q
    return ⟨mkApp2 (mkConst ``PropExpr.and) rp.expr rq.expr,
      mkAppN (mkConst ``PropExpr.and_eq) #[rp.expr, rq.expr, ρ, p, q, rp.proof, rq.proof]⟩
  | Or p q =>
    let rp ← reifyProp rc p; let rq ← reifyProp rc q
    return ⟨mkApp2 (mkConst ``PropExpr.or) rp.expr rq.expr,
      mkAppN (mkConst ``PropExpr.or_eq) #[rp.expr, rq.expr, ρ, p, q, rp.proof, rq.proof]⟩
  | Not p =>
    let rp ← reifyProp rc p
    return ⟨mkApp (mkConst ``PropExpr.not) rp.expr,
      mkAppN (mkConst ``PropExpr.not_eq) #[rp.expr, ρ, p, rp.proof]⟩
  | True => return ⟨mkConst ``PropExpr.tt, mkApp (mkConst ``PropExpr.tt_eq) ρ⟩
  | False => return ⟨mkConst ``PropExpr.ff, mkApp (mkConst ``PropExpr.ff_eq) ρ⟩
  | LT.lt α _ a b => cmp α ``PropExpr.lt ``PropExpr.lt_eq a b P
  | LE.le α _ a b => cmp α ``PropExpr.le ``PropExpr.le_eq a b P
  | GT.gt α _ a b => do
    let r ← cmp α ``PropExpr.lt ``PropExpr.lt_eq b a P
    return { r with proof := ← mkExpectedTypeHint r.proof (← mkEq P (mkApp2 (mkConst ``PropExpr.denote) r.expr ρ)) }
  | GE.ge α _ a b => do
    let r ← cmp α ``PropExpr.le ``PropExpr.le_eq b a P
    return { r with proof := ← mkExpectedTypeHint r.proof (← mkEq P (mkApp2 (mkConst ``PropExpr.denote) r.expr ρ)) }
  | _ =>
    if P.isArrow then
      let p := P.bindingDomain!
      let q := P.bindingBody!
      let rp ← reifyProp rc p; let rq ← reifyProp rc q
      return ⟨mkApp2 (mkConst ``PropExpr.imp) rp.expr rq.expr,
        mkAppN (mkConst ``PropExpr.imp_eq) #[rp.expr, rq.expr, ρ, p, q, rp.proof, rq.proof]⟩
    -- unfold user definitions
    if let some P' ← unfoldHead? P then
      let r ← reifyProp rc P'
      return { r with proof := ← mkExpectedTypeHint r.proof (← mkEq P (mkApp2 (mkConst ``PropExpr.denote) r.expr ρ)) }
    throwError "lynth interval: unsupported proposition {P}"
where
  cmp (α : Lean.Expr) (ctor lem : Name) (a b P : Lean.Expr) : MetaM RProp := do
    unless (← whnfR α).isConstOf ``Real do throwError "lynth interval: comparison over {α}"
    let ra ← reify rc a; let rb ← reify rc b
    let ex := mkApp2 (mkConst ctor) ra.expr rb.expr
    let pf := mkAppN (mkConst lem) #[ra.expr, rb.expr, rc.senv, a, b, ra.proof, rb.proof]
    let pf ← mkExpectedTypeHint pf (← mkEq P (mkApp2 (mkConst ``PropExpr.denote) ex rc.senv))
    return ⟨ex, pf⟩

end Lynth.Interval.Reify
