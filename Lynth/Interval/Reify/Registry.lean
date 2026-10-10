import Lean
import Lynth.Interval.Core.Prop

/-!
# The function registry (`@[lynth_fn]`)

Every `Fn0/Fn1/Fn2` record tagged `@[lynth_fn]` becomes a reification rule.
The Lean term pattern is derived from the record's `graph` field
(`fun x₁ … y => y = P x₁ …`), so adding a function needs no other code.
See `docs/interval/03-expr-registry.md §7`.
-/

namespace Lynth.Interval.Reify

open Lean Meta

/-- One registered function. -/
structure FnEntry where
  /-- constant of type `Fn0 r` / `Fn1 a r` / `Fn2 a b r` -/
  decl : Name
  arity : Nat
  argTys : Array Ty
  resTy : Ty
  /-- `fun x₁ … xₙ => P`, the Lean term denoted by the function applied to `x₁ … xₙ` -/
  pattern : Lean.Expr
  keys : Array DiscrTree.Key
  prio : Nat := 1000
deriving Inhabited

instance : BEq FnEntry := ⟨fun a b => a.decl == b.decl⟩

initialize fnExt : SimpleScopedEnvExtension FnEntry (DiscrTree FnEntry) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun d e => d.insertKeyValue e.keys e
  }

/-- read a `Ty` constructor constant -/
def tyOfExpr? (e : Lean.Expr) : MetaM (Option Ty) := do
  let e ← whnfD e
  match e with
  | .const ``Ty.nat _ => return some .nat
  | .const ``Ty.int _ => return some .int
  | .const ``Ty.real _ => return some .real
  | .const ``Ty.cplx _ => return some .cplx
  | _ => return none

def tyToExpr : Ty → Lean.Expr
  | .nat => mkConst ``Ty.nat
  | .int => mkConst ``Ty.int
  | .real => mkConst ``Ty.real
  | .cplx => mkConst ``Ty.cplx

instance : ToExpr Ty where
  toExpr := tyToExpr
  toTypeExpr := mkConst ``Ty

/-- Compute the registry entry of a declaration. -/
def mkFnEntry (decl : Name) (prio : Nat) : MetaM FnEntry := do
  let info ← getConstInfo decl
  let ty ← whnfR info.type
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  let (arity, graphName) ← match fn with
    | .const ``Fn0 _ => pure (0, ``Fn0.graph)
    | .const ``Fn1 _ => pure (1, ``Fn1.graph)
    | .const ``Fn2 _ => pure (2, ``Fn2.graph)
    | _ => throwError "@[lynth_fn]: `{decl}` must have type Fn0/Fn1/Fn2, got {ty}"
  let mut tys : Array Ty := #[]
  for a in args do
    match ← tyOfExpr? a with
    | some t => tys := tys.push t
    | none => throwError "@[lynth_fn]: cannot read Ty argument {a} of `{decl}`"
  let argTys := tys.extract 0 arity
  let resTy := tys[arity]!
  -- the graph `fun x₁ … y => y = P`
  let graph ← whnfD (mkAppN (mkConst graphName) (args.push (mkConst decl (info.levelParams.map mkLevelParam))))
  let pattern ← lambdaTelescope graph fun xs body => do
    unless xs.size == arity + 1 do
      throwError "@[lynth_fn]: graph of `{decl}` must take {arity + 1} arguments, got {graph}"
    let body ← whnfR body
    let some (_, lhs, rhs) := body.eq?
      | throwError "@[lynth_fn]: graph of `{decl}` must be `fun … y => y = P`, got {body}"
    unless lhs == xs[arity]! do
      throwError "@[lynth_fn]: graph of `{decl}` must be `fun … y => y = P` (lhs must be y)"
    if rhs.containsFVar xs[arity]!.fvarId! then
      throwError "@[lynth_fn]: pattern of `{decl}` mentions the result variable"
    mkLambdaFVars (xs.extract 0 arity) rhs
  let keys ← withReducible do
    let (_, _, body) ← lambdaMetaTelescope pattern
    DiscrTree.mkPath body
  return { decl, arity, argTys, resTy, pattern, keys, prio }

syntax (name := lynthFnAttr) "lynth_fn" (ppSpace num)? : attr

initialize registerBuiltinAttribute {
  name := `lynthFnAttr
  descr := "register an interval-arithmetic function record for `lynth`"
  add := fun decl stx kind => do
    let prio := match stx with
      | `(attr| lynth_fn $n:num) => n.getNat
      | _ => 1000
    let entry ← MetaM.run' (mkFnEntry decl prio)
    fnExt.add entry kind
}

/-- read a `CTy` constructor constant -/
def ctyOfExpr? (e : Lean.Expr) : MetaM (Option CTy) := do
  let e ← whnfD e
  match e with
  | .const ``CTy.nat _ => return some .nat
  | .const ``CTy.int _ => return some .int
  | .const ``CTy.rat _ => return some .rat
  | .const ``CTy.real _ => return some .real
  | _ => return none

/-- read a closed `List CTy` term (fuel-bounded; arities are tiny) -/
def ctyListOfExpr? (e : Lean.Expr) : MetaM (Option (Array CTy)) := do
  let mut out : Array CTy := #[]
  let mut cur ← whnfD e
  for _ in [0:64] do
    match cur.getAppFn with
    | .const ``List.nil _ => return some out
    | .const ``List.cons _ =>
      let args := cur.getAppArgs
      unless 2 ≤ args.size do return none
      let head := args[args.size - 2]!
      let tail := args[args.size - 1]!
      let some t ← ctyOfExpr? head | return none
      out := out.push t
      cur ← whnfD tail
    | _ => return none
  return none

/-- the Lean type expected at one `CTy` position of a curried function -/
def ctyValConst : CTy → Name
  | .nat => ``Nat
  | .int => ``Int
  | .rat => ``Rat
  | .real => ``Real

/-- One registered n-ary custom function (`CFn tys r`). -/
structure NaryEntry where
  /-- constant of type `CFn tys r` -/
  decl : Name
  tys : Array CTy
  res : CTy
  /-- the curried Lean function `F : curriedType tys r` (for patterns) -/
  fn : Lean.Expr
  /-- `F` applied to argument metavariables -/
  pattern : Lean.Expr
  keys : Array DiscrTree.Key
  prio : Nat := 1000
  deriving Inhabited

instance : BEq NaryEntry := ⟨fun a b => a.decl == b.decl⟩

initialize naryExt : SimpleScopedEnvExtension NaryEntry (DiscrTree NaryEntry) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun d e => d.insertKeyValue e.keys e
  }

/-- the `F` argument of a `CFn.manual` / `CFn.ofFn` / `CFn.mk` application.
For `CFn.mk` literals, `F` is read from `graph` (`CFn.graphOf tys r F`)
first, so entries can keep a computable `fn` placeholder while the real
(noncomputable) mirror lives only in `Prop` fields — the `Fn.lean` pattern.
Falls back to the `fn` field for hand-written graphs. -/
def cfnFunOf? (v : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let graphFun? (g : Lean.Expr) : Option Lean.Expr :=
    let gfn := g.getAppFn
    let gargs := g.getAppArgs
    if gfn.isConstOf ``CFn.graphOf && 2 < gargs.size then some gargs[2]! else none
  let go (v : Lean.Expr) : MetaM (Option Lean.Expr) := do
    let fn := v.getAppFn
    let args := v.getAppArgs
    if fn.isConstOf ``CFn.manual || fn.isConstOf ``CFn.ofFn then
      if 2 < args.size then return some args[2]! else return none
    else if fn.isConstOf ``CFn.mk then
      -- `mk` takes explicit `tys r` then fields `name fn graph …`
      if 4 < args.size then
        if let some f := graphFun? args[4]! then return some f
      if 3 < args.size then return some args[3]! else return none
    else return none
  if let some f ← go v then return some f
  go (← whnfD v)

/-- Compute the registry entry of a `CFn` declaration. -/
def mkNaryEntry (decl : Name) (prio : Nat) : MetaM NaryEntry := do
  let info ← getConstInfo decl
  let ty ← whnfR info.type
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  unless fn.isConstOf ``CFn && args.size == 2 do
    throwError "@[lynth_cfn]: `{decl}` must have type `CFn tys r`, got {ty}"
  let some tys ← ctyListOfExpr? args[0]!
    | throwError "@[lynth_cfn]: cannot read `tys` argument of `{decl}`"
  let some res ← ctyOfExpr? args[1]!
    | throwError "@[lynth_cfn]: cannot read `r` argument of `{decl}`"
  let some v := info.value?
    | throwError "@[lynth_cfn]: `{decl}` must be a definition (need its `F`)"
  let some F ← cfnFunOf? v
    | throwError ("@[lynth_cfn]: `{decl}` must unfold to `CFn.manual`, `CFn.ofFn` " ++
      "or a `CFn.mk` record literal (need its Lean function)")
  -- arity / domain check against `curriedType tys res`
  let fty ← inferType F
  let (pis, _, _) ← forallMetaTelescope fty
  unless pis.size == tys.size do
    throwError "@[lynth_cfn]: `{decl}` function takes {pis.size} arguments, `tys` has {tys.size}"
  for i in [0:tys.size] do
    let d ← inferType pis[i]!
    let d ← whnfR d
    let want := ctyValConst tys[i]!
    unless d.isConstOf want do
      throwError "@[lynth_cfn]: `{decl}` argument {i} has type {d}, expected {want}"
  let mvars ← tys.mapM fun t => mkFreshExprMVar (mkConst (ctyValConst t))
  let pattern ← mkLambdaFVars mvars (mkAppN F mvars)
  let keys ← withReducible do
    let (_, _, body) ← lambdaMetaTelescope pattern
    DiscrTree.mkPath body
  return { decl, tys, res, fn := F, pattern, keys, prio }

syntax (name := lynthCfnAttr) "lynth_cfn" (ppSpace num)? : attr

initialize registerBuiltinAttribute {
  name := `lynthCfnAttr
  descr := "register an n-ary custom-function `CFn` record for `lynth`"
  add := fun decl stx kind => do
    let prio := match stx with
      | `(attr| lynth_cfn $n:num) => n.getNat
      | _ => 1000
    let entry ← MetaM.run' (mkNaryEntry decl prio)
    naryExt.add entry kind
}

/-- candidate registry entries for a term, highest priority first -/
def candidates (e : Lean.Expr) : MetaM (Array FnEntry) := do
  let d := fnExt.getState (← getEnv)
  let cs ← withReducible <| d.getMatch e
  return cs.qsort (fun a b => a.prio > b.prio)

/-- candidate n-ary entries for a term, highest priority first -/
def candidatesNary (e : Lean.Expr) : MetaM (Array NaryEntry) := do
  let d := naryExt.getState (← getEnv)
  let cs ← withReducible <| d.getMatch e
  return cs.qsort (fun a b => a.prio > b.prio)

end Lynth.Interval.Reify
