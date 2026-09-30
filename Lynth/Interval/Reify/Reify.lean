import Lynth.Interval.Reify.Registry
import Lynth.Interval.Fns.Arith
import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Analysis.Complex.Basic
import Qq

/-!
# Reifier: Lean terms → typed `Expr` with denotation proofs

`reify rc e` returns `(t, eE, h)` with `eE : Expr t` and `h : e = eE.denote ρ`
(`ρ = rc.senv`).  Steps (first success wins, `docs/interval/03 §8`):
variables, exact numerals (norm_num), finite sums, registry patterns,
unfolding of user definitions, atoms.
-/

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
  senv : Lean.Expr := mkApp3 (mkConst ``SEnv.mk) (mkApp (mkConst ``List.nil [0]) (mkConst ``Nat))
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Real)) (mkApp (mkConst ``List.nil [0]) (mkConst ``Complex))
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

/-- the Lean type of `Ty.Val t` -/
def tyVal : Ty → Lean.Expr
  | .nat => mkConst ``Nat
  | .real => mkConst ``Real
  | .cplx => mkConst ``Complex

def tyOfType? (ty : Lean.Expr) : MetaM (Option Ty) := do
  let ty ← whnfR ty
  if ty.isConstOf ``Nat then return some .nat
  if ty.isConstOf ``Real then return some .real
  if ty.isConstOf ``Complex then return some .cplx
  return none

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

def exact? (t : Ty) (e : Lean.Expr) (senv : Lean.Expr) : MetaM (Option Reified) := do
  if e.hasFVar || e.hasMVar || isTranscendentalHead e then return none
  match t with
  | .real =>
    let some q ← ratValue? (α := q(ℝ)) e | return none
    let qE : Q(ℚ) := toExpr q
    let castE : Q(ℝ) := q(($qE : ℝ))
    let some pf ← normNumEq? (α := q(ℝ)) e castE | return none
    let ex := mkApp (mkConst ``Expr.lit) qE
    return some ⟨.real, ex, pf⟩
  | .nat =>
    let some q ← ratValue? (α := q(ℕ)) e | return none
    unless q.den == 1 && q.num ≥ 0 do return none
    let n := q.num.toNat
    let nE := mkNatLit n
    let some pf ← normNumEq? (α := q(ℕ)) e nE | return none
    return some ⟨.nat, mkApp (mkConst ``Expr.natLit) nE, pf⟩
  | .cplx =>
    let some q ← ratValue? (α := q(ℂ)) e | return none
    let qE : Q(ℚ) := toExpr q
    let castC : Q(ℂ) := q(($qE : ℂ))
    let some pf ← normNumEq? (α := q(ℂ)) e castC | return none
    -- `(q : ℂ) = ((q : ℝ) : ℂ)`
    let pf2 : Lean.Expr := q((Complex.ofReal_ratCast $qE).symm)
    let pf ← mkEqTrans pf pf2
    let lit := mkApp (mkConst ``Expr.lit) qE
    let ex := mkApp4 (mkConst ``Expr.c1) (toExpr Ty.real) (toExpr Ty.cplx) (mkConst ``Fns.ofRealC) lit
    let X : Q(ℝ) := q(($qE : ℝ))
    let pf := mkAppN (mkConst ``Expr.c1_eq)
      #[toExpr Ty.real, toExpr Ty.cplx, mkConst ``Fns.ofRealC, lit, senv, X, e, ← mkEqRefl X, pf]
    return some ⟨.cplx, ex, pf⟩

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
  -- 3. finite sums
  if let some r ← reifySum? rc t e then return r
  -- 4. registry
  for cand in ← candidates e do
    if let some r ← tryEntry rc t cand e then return r
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
  /-- try one registry entry -/
  tryEntry (rc : RCtx) (t : Ty) (ent : FnEntry) (e : Lean.Expr) : MetaM (Option Reified) := do
    unless ent.resTy == t do return none
    let s ← saveState
    let (mvars, _, body) ← lambdaMetaTelescope ent.pattern
    unless ← withTransparency .instances (isDefEq body e) do
      s.restore; return none
    let args ← mvars.mapM instantiateMVars
    if args.any (·.hasMVar) then s.restore; return none
    try
      let rs ← args.mapM (reify rc)
      for i in [0:rs.size] do
        unless rs[i]!.ty == ent.argTys[i]! do throw (Exception.error .missing "type mismatch")
      let f := mkConst ent.decl
      let ρ := rc.senv
      let hY ← mkEqRefl e
      match ent.arity with
      | 0 =>
        let ex := mkApp2 (mkConst ``Expr.c0) (toExpr t) f
        let pf := mkAppN (mkConst ``Expr.c0_eq) #[toExpr t, f, ρ, e, hY]
        return some ⟨t, ex, pf⟩
      | 1 =>
        let a := ent.argTys[0]!
        let ex := mkApp4 (mkConst ``Expr.c1) (toExpr a) (toExpr t) f rs[0]!.expr
        let pf := mkAppN (mkConst ``Expr.c1_eq)
          #[toExpr a, toExpr t, f, rs[0]!.expr, ρ, args[0]!, e, rs[0]!.proof, hY]
        return some ⟨t, ex, pf⟩
      | _ =>
        let a := ent.argTys[0]!
        let b := ent.argTys[1]!
        let ex := mkAppN (mkConst ``Expr.c2) #[toExpr a, toExpr b, toExpr t, f, rs[0]!.expr, rs[1]!.expr]
        let pf := mkAppN (mkConst ``Expr.c2_eq)
          #[toExpr a, toExpr b, toExpr t, f, rs[0]!.expr, rs[1]!.expr, ρ, args[0]!, args[1]!, e,
            rs[0]!.proof, rs[1]!.proof, hY]
        return some ⟨t, ex, pf⟩
    catch _ =>
      s.restore; return none

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
