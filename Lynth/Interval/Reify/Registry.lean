import Lean
import Lynth.Interval.Core.Prop

/-! # The unified function registry (`@[lynth_cfn]`)

Every `CFn tys r` definition — or `Fn0`/`Fn1`/`Fn2` record (lifted to a
`CFn` via `CFn.ofFn0`/`ofFn1`/`ofFn2`) — tagged `@[lynth_cfn]` becomes a
reification rule. Patterns derive from the Lean function (`CFn` records)
or the `graph` RHS (`Fn` records); call nodes always go through `Expr.call`.
See `docs/interval/03-expr-registry.md §7`.
-/

namespace Lynth.Interval.Reify

open Lean Meta

/-- read a `Ty` constructor constant (or `Ty.list` application) -/
def tyOfExpr? (e : Lean.Expr) : MetaM (Option Ty) := go 8 e
where
  go : Nat → Lean.Expr → MetaM (Option Ty)
    | 0, _ => return none
    | fuel + 1, e => do
      let e ← whnfD e
      match e with
      | .const ``Ty.nat _ => return some .nat
      | .const ``Ty.int _ => return some .int
      | .const ``Ty.real _ => return some .real
      | .const ``Ty.cplx _ => return some .cplx
      | .const ``Ty.rat _ => return some .rat
      | _ =>
        if e.getAppFn.isConstOf ``Ty.list then
          let args := e.getAppArgs
          if 0 < args.size then
            let some t ← go fuel args[0]! | return none
            return some (.list t)
          else return none
        else return none

def tyToExpr : Ty → Lean.Expr
  | .nat => mkConst ``Ty.nat
  | .int => mkConst ``Ty.int
  | .real => mkConst ``Ty.real
  | .cplx => mkConst ``Ty.cplx
  | .rat => mkConst ``Ty.rat
  | .list t => mkApp (mkConst ``Ty.list) (tyToExpr t)

instance : ToExpr Ty where
  toExpr := tyToExpr
  toTypeExpr := mkConst ``Ty

/-- read a Lean type as a `Ty` (`List` applications recurse) -/
def tyOfType? (ty : Lean.Expr) : MetaM (Option Ty) := go 8 ty
where
  go : Nat → Lean.Expr → MetaM (Option Ty)
    | 0, _ => return none
    | fuel + 1, ty => do
      let ty ← whnfR ty
      if ty.isConstOf ``Nat then return some .nat
      if ty.isConstOf ``Int then return some .int
      if ty.isConstOf ``Real then return some .real
      if ty.isConstOf ``Complex then return some .cplx
      if ty.isConstOf ``Rat then return some .rat
      if ty.getAppFn.isConstOf ``List then
        let args := ty.getAppArgs
        if 0 < args.size then
          if let some t ← go fuel args[0]! then return some (.list t)
      return none

/-- the Lean type expected at one `Ty` position of a curried function -/
def tyValConst : Ty → Lean.Expr
  | .nat => mkConst ``Nat
  | .int => mkConst ``Int
  | .rat => mkConst ``Rat
  | .real => mkConst ``Real
  | .cplx => mkConst ``Complex
  | .list t => mkApp (mkConst ``List [Lean.levelZero]) (tyValConst t)

/-- One registered function (`CFn tys r`, or an `Fn0`/`Fn1`/`Fn2` record
lifted via `CFn.ofFn0`/`ofFn1`/`ofFn2`). -/
structure NaryEntry where
  /-- constant of type `CFn tys r` (or `Fn0`/`Fn1`/`Fn2`) -/
  decl : Name
  tys : Array Ty
  res : Ty
  /-- the `CFn tys r` value term for call nodes (`mkConst decl` for `CFn`
  decls, converter application for `Fn` decls) -/
  cfn : Lean.Expr
  /-- applicative pattern for `DiscrTree` matching -/
  pattern : Lean.Expr
  keys : Array DiscrTree.Key
  prio : Nat := 1000
  deriving Inhabited

/-- read a closed `List Ty` term (fuel-bounded; arities are tiny) -/
def tyListOfExpr? (e : Lean.Expr) : MetaM (Option (Array Ty)) := do
  let mut out : Array Ty := #[]
  let mut cur ← whnfD e
  for _ in [0:64] do
    match cur.getAppFn with
    | .const ``List.nil _ => return some out
    | .const ``List.cons _ =>
      let args := cur.getAppArgs
      unless 2 ≤ args.size do return none
      let head := args[args.size - 2]!
      let tail := args[args.size - 1]!
      let some t ← tyOfExpr? head | return none
      out := out.push t
      cur ← whnfD tail
    | _ => return none
  return none

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

/-- Compute the registry entry of a `CFn`/`Fn0`/`Fn1`/`Fn2` declaration. -/
def mkNaryEntry (decl : Name) (prio : Nat) : MetaM NaryEntry := do
  let info ← getConstInfo decl
  let ty ← whnfR info.type
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  if fn.isConstOf ``CFn && args.size == 2 then
    mkNaryEntryCFn decl prio info args
  else if fn.isConstOf ``Fn0 || fn.isConstOf ``Fn1 || fn.isConstOf ``Fn2 then
    mkNaryEntryFn decl prio info ty args
  else
    throwError "@[lynth_cfn]: `{decl}` must have type `CFn tys r` or `Fn0/Fn1/Fn2`, got {ty}"
where
  mkNaryEntryCFn (decl : Name) (prio : Nat) (info : ConstantInfo)
      (args : Array Lean.Expr) : MetaM NaryEntry := do
    let some tys ← tyListOfExpr? args[0]!
      | throwError "@[lynth_cfn]: cannot read `tys` argument of `{decl}`"
    let some res ← tyOfExpr? args[1]!
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
      let some dt ← tyOfType? d
        | throwError "@[lynth_cfn]: `{decl}` argument {i} has non-Ty type {d}"
      unless dt == tys[i]! do
        throwError "@[lynth_cfn]: `{decl}` argument {i} has type {d}, expected {(tyValConst tys[i]!)}"
    let mvars ← tys.mapM fun t => mkFreshExprMVar (tyValConst t)
    let pattern ← mkLambdaFVars mvars (mkAppN F mvars)
    let keys ← withReducible do
      let (_, _, body) ← lambdaMetaTelescope pattern
      DiscrTree.mkPath body
    return { decl, tys, res, cfn := mkConst decl, pattern, keys, prio }
  /-- `Fn0`/`Fn1`/`Fn2` records: pattern from the `graph` RHS
  (`fun x₁ … y => y = P`), call nodes via the `CFn.ofFn0/1/2` lift. -/
  mkNaryEntryFn (decl : Name) (prio : Nat) (info : ConstantInfo)
      (ty : Lean.Expr) (args : Array Lean.Expr) : MetaM NaryEntry := do
    let fn := ty.getAppFn
    let (arity, graphName, convName) ← match fn with
      | .const ``Fn0 _ => pure (0, ``Fn0.graph, ``CFn.ofFn0)
      | .const ``Fn1 _ => pure (1, ``Fn1.graph, ``CFn.ofFn1)
      | .const ``Fn2 _ => pure (2, ``Fn2.graph, ``CFn.ofFn2)
      | _ => throwError "@[lynth_cfn]: `{decl}` must have type `CFn tys r` or `Fn0/Fn1/Fn2`, got {ty}"
    let mut tys : Array Ty := #[]
    for a in args do
      match ← tyOfExpr? a with
      | some t => tys := tys.push t
      | none => throwError "@[lynth_cfn]: cannot read Ty argument {a} of `{decl}`"
    let argTys := tys.extract 0 arity
    let resTy := tys[arity]!
    -- the graph `fun x₁ … y => y = P`
    let graph ← whnfD (mkAppN (mkConst graphName) (args.push (mkConst decl (info.levelParams.map mkLevelParam))))
    let pattern ← lambdaTelescope graph fun xs body => do
      unless xs.size == arity + 1 do
        throwError "@[lynth_cfn]: graph of `{decl}` must take {arity + 1} arguments, got {graph}"
      let body ← whnfR body
      let some (_, lhs, rhs) := body.eq?
        | throwError "@[lynth_cfn]: graph of `{decl}` must be `fun … y => y = P`, got {body}"
      unless lhs == xs[arity]! do
        throwError "@[lynth_cfn]: graph of `{decl}` must be `fun … y => y = P` (lhs must be y)"
      if rhs.containsFVar xs[arity]!.fvarId! then
        throwError "@[lynth_cfn]: pattern of `{decl}` mentions the result variable"
      mkLambdaFVars (xs.extract 0 arity) rhs
    let keys ← withReducible do
      let (_, _, body) ← lambdaMetaTelescope pattern
      DiscrTree.mkPath body
    let declE := mkConst decl (info.levelParams.map mkLevelParam)
    let cfn ← match arity with
      | 0 => mkAppOptM convName #[none, some declE]
      | 1 => mkAppOptM convName #[none, none, some declE]
      | _ => mkAppOptM convName #[none, none, none, some declE]
    return { decl, tys := argTys, res := resTy, cfn, pattern, keys, prio }

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
def candidatesNary (e : Lean.Expr) : MetaM (Array NaryEntry) := do
  let d := naryExt.getState (← getEnv)
  let cs ← withReducible <| d.getMatch e
  return cs.qsort (fun a b => a.prio > b.prio)

end Lynth.Interval.Reify
