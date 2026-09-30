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
  | .const ``Ty.real _ => return some .real
  | .const ``Ty.cplx _ => return some .cplx
  | _ => return none

def tyToExpr : Ty → Lean.Expr
  | .nat => mkConst ``Ty.nat
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

/-- candidate registry entries for a term, highest priority first -/
def candidates (e : Lean.Expr) : MetaM (Array FnEntry) := do
  let d := fnExt.getState (← getEnv)
  let cs ← withReducible <| d.getMatch e
  return cs.qsort (fun a b => a.prio > b.prio)

end Lynth.Interval.Reify
