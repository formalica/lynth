/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Simp.Simproc
import Lynth.Grind.MatchDiscrOnly
import Lynth.Grind.ForallProp
import Lynth.Grind.Arith.Simproc
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.List
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core
import Lynth.Grind.Util
import Lean.Meta.Sym.Util
import Init.Grind.Norm
public import Init.Grind.Config
import Init.ByCases
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Grind.Attr
open Lean.Meta
public section
namespace Lean.Lynth.Grind

def registerNormTheorems (preDeclNames : Array Name) (postDeclNames : Array Name) : MetaM Unit := do
  let thms ← normExt.getTheorems
  unless thms.lemmaNames.isEmpty do
    throwError "`lynth_grind` normalization theorems have already been initialized"
  for declName in preDeclNames do
    addSimpTheorem normExt declName (post := false) (inv := false) .global (eval_prio default)
  for declName in postDeclNames do
    addSimpTheorem normExt declName (post := true) (inv := false) .global (eval_prio default)

-- TODO: should we make this extensible?
private def isBoolEqTarget (declName : Name) : Bool :=
  declName == ``Bool.and ||
  declName == ``Bool.or  ||
  declName == ``Bool.not ||
  declName == ``BEq.beq  ||
  declName == ``decide

def simpEq : Lean.Meta.Simp.Simproc := fun e => do
  let_expr f@Eq α lhs rhs ← e | return .continue
  match_expr α with
  | Bool =>
    let .const rhsName _ := rhs.getAppFn | return .continue
    if rhsName == ``true || rhsName == ``false then return .continue
    let .const lhsName _ := lhs.getAppFn | return .continue
    if lhsName == ``true || lhsName == ``false then
      -- Just apply comm
      let e' := mkApp3 f α rhs lhs
      return .visit { expr := e', proof? := mkApp2 (mkConst ``Lean.Grind.flip_bool_eq) lhs rhs }
    if isBoolEqTarget lhsName || isBoolEqTarget rhsName then
      -- Convert into `(lhs = true) = (rhs = true)`
      let tr := mkConst ``true
      let e' ← mkEq (mkApp3 f α lhs tr) (mkApp3 f α rhs tr)
      return .visit { expr := e', proof? := mkApp2 (mkConst ``Lean.Grind.bool_eq_to_prop) lhs rhs }
    return .continue
  | _ =>
    if lhs == rhs then
      let u := f.constLevels!
      return .done { expr := mkConst ``True, proof? := mkApp2 (mkConst ``eq_self u) α lhs }
    else if rhs == mkConst ``True then
      return .done { expr := lhs, proof? := mkApp (mkConst ``Lean.Grind.eq_true_eq) lhs }
    else if rhs == mkConst ``False then
      return .visit { expr := mkNot lhs, proof? := mkApp (mkConst ``Lean.Grind.eq_false_eq) lhs }
  return .continue


simproc_pattern% (@Eq _ _ _) => simpEq
def simpDIte : Lean.Meta.Simp.Simproc := fun e => do
 let_expr f@dite α c inst a b ← e | return .continue
 let .lam _ _ aBody _ := a | return .continue
 if aBody.hasLooseBVars then return .continue
 let .lam _ _ bBody _ := b | return .continue
 if bBody.hasLooseBVars then return .continue
 let us := f.constLevels!
 let expr := mkApp5 (mkConst ``ite us) α c inst aBody bBody
 return .visit { expr, proof? := some (mkApp5 (mkConst ``dite_eq_ite us) c α aBody bBody inst) }


simproc_pattern% (@dite _ _ _ _ _) => simpDIte
def pushNot : Lean.Meta.Simp.Simproc := fun e => do
 let_expr Not p ← e | return .continue
 match_expr p with
 | True => return .visit { expr := mkConst ``False, proof? := some <| mkConst ``Lean.Grind.not_true  }
 | False => return .visit { expr := mkConst ``True, proof? := some <| mkConst ``Lean.Grind.not_false  }
 | And q r => return .visit { expr := mkApp2 (mkConst ``Or) (mkNot q) (mkNot r), proof? := some <| mkApp2 (mkConst ``Lean.Grind.not_and) q r }
 | Or q r => return .visit { expr := mkApp2 (mkConst ``And) (mkNot q) (mkNot r), proof? := some <| mkApp2 (mkConst ``Lean.Grind.not_or) q r }
 | Not q => return .visit { expr := q, proof? := some <| mkApp (mkConst ``Lean.Grind.not_not) q }
 | f@Eq α a b =>
   if α.isProp then
     return .visit { expr := mkApp3 f α a (mkNot b), proof? := some <| mkApp2 (mkConst ``Lean.Grind.not_eq_prop) a b }
   else match_expr b with
     | Bool.true => return .visit { expr := mkApp3 f α a (mkConst ``Bool.false), proof? := some <| mkApp (mkConst ``Bool.not_eq_true) a }
     | Bool.false => return .visit { expr := mkApp3 f α a (mkConst ``Bool.true), proof? := some <| mkApp (mkConst ``Bool.not_eq_false) a }
     | _ => return .continue
 | f@ite α c inst a b => return .visit { expr := mkApp5 f α c inst (mkNot a) (mkNot b), proof? := some <| mkApp4 (mkConst ``Lean.Grind.not_ite) c inst a b }
 | Exists α p =>
   let expr := mkForall `a .default α (mkNot (mkApp p (mkBVar 0)))
   let u ← getLevel α
   return .visit { expr, proof? := mkApp2 (mkConst ``Lean.Grind.not_exists [u]) α p }
 | LE.le α _ a b =>
   match_expr α with
   | Int => return .visit { expr := mkIntLE (mkIntAdd b (mkIntLit 1)) a, proof? := some <| mkApp2 (mkConst ``Int.not_le_eq) a b }
   | Nat => return .visit { expr := mkNatLE (mkNatAdd b (mkNatLit 1)) a, proof? := some <| mkApp2 (mkConst ``Nat.not_le_eq) a b }
   | _ => return .continue
 | _ =>
  if let .forallE n α b info := e then
    if α.isProp && !b.hasLooseBVars then
      return .visit { expr := mkAnd α (mkNot b), proof? := some <| mkApp2 (mkConst ``Lean.Grind.not_implies) α b }
    else
      let p    := mkLambda n info α b
      let notP := mkLambda n info α (mkNot b)
      let u ← getLevel α
      let expr := mkApp2 (mkConst ``Exists [u]) α notP
      return .visit { expr, proof? := some <| mkApp2 (mkConst ``Lean.Grind.not_forall [u]) α p }
  else
    return .continue


simproc_pattern% (Not _) => pushNot
def simpOr : Lean.Meta.Simp.Simproc := fun e => do
  let_expr Or p q ← e | return .continue
  match_expr p with
  | True => return .visit { expr := p, proof? := some <| mkApp (mkConst ``true_or) q }
  | False => return .visit { expr := q, proof? := some <| mkApp (mkConst ``false_or) q }
  | Or p₁ p₂ => return .visit { expr := mkOr p₁ (mkOr p₂ q), proof? := some <| mkApp3 (mkConst ``Lean.Grind.or_assoc) p₁ p₂ q }
  | _ =>
  match_expr q with
  | Or q r =>
    if p.isForall then return .continue
    if q.isForall then return .visit { expr := mkOr q (mkOr p r), proof? := some <| mkApp3 (mkConst ``Lean.Grind.or_swap12) p q r }
    if r.isForall then return .visit { expr := mkOr r (mkOr q p), proof? := some <| mkApp3 (mkConst ``Lean.Grind.or_swap13) p q r }
    return .continue
  | True => return .visit { expr := q, proof? := some <| mkApp (mkConst ``or_true) p }
  | False => return .visit { expr := p, proof? := some <| mkApp (mkConst ``or_false) p }
  | _ => return .continue


simproc_pattern% (Or _ _) => simpOr
def reduceCtorEqCheap : Lean.Meta.Simp.Simproc := fun e => do
  let_expr Eq _ lhs rhs ← e | return .continue
  let some c₁ ← isConstructorApp? lhs | return .continue
  let some c₂ ← isConstructorApp? rhs | return .continue
  unless c₁.name != c₂.name do return .continue
  withLocalDeclD `h e fun h =>
    return .done { expr := mkConst ``False, proof? := (← withDefault <| mkEqFalse' (← mkLambdaFVars #[h] (← mkNoConfusion (mkConst ``False) h))) }


simproc_pattern% (_ = _) => reduceCtorEqCheap
def unfoldReducibleSimproc : Lean.Meta.Simp.DSimproc := fun e => do
  Sym.unfoldReducibleStep e

simproc_pattern% (_) => unfoldReducibleSimproc
/-- Returns the array of simprocs used by `lynth_grind`. -/

protected def getSimprocs : MetaM (Array Simprocs) := do
  let s ← Simp.getSEvalSimprocs
  /-
  We don't want to apply `List.reduceReplicate` as a normalization operation in
  `lynth_grind`. Consider the following example:
  ```
  example (ys : List α) : n = 0 → List.replicate n ys = [] := by
    grind only [List.replicate]
  ```
  The E-matching module generates the following instance for `List.replicate.eq_1`
  ```
  List.replicate 0 [] = []
  ```
  We don't want it to be simplified to `[] = []`.
  -/
  let s := s.erase ``List.reduceReplicate
  let s := s.erase ``reduceCtorEq
  let s ← s.add ``reduceCtorEqCheap (post := true)
  let s ← addSimpMatchDiscrsOnly s
  let s ← addPreMatchCondSimproc s
  let s ← Arith.addSimproc s
  let s ← addForallSimproc s
  let s ← s.add ``simpEq (post := true)
  let s ← s.add ``simpOr (post := true)
  let s ← s.add ``simpDIte (post := true)
  let s ← s.add ``pushNot (post := false)
  let s ← s.add ``unfoldReducibleSimproc (post := false)
  return #[s]

private def addDeclToUnfold (s : SimpTheorems) (declName : Name) : MetaM SimpTheorems := do
  if (← getEnv).contains declName then
    s.addDeclToUnfold declName
  else
    return s

def getNormTheorems : MetaM SimpTheorems := do
  -- NOTE: base set from CORE's `normExt` (not ours): our `builtin_initialize`d
  -- `SimpExtension` reads crash the IR interpreter under `lake env lean`
  -- (native objects never load), while core's — initialized natively in the
  -- toolchain — works. Bonus: identical normalization behavior to `grind`.
  let mut thms ← Lean.Meta.Grind.normExt.getTheorems
  thms ← addDeclToUnfold thms ``GE.ge
  thms ← addDeclToUnfold thms ``GT.gt
  thms ← addDeclToUnfold thms ``Nat.cast
  thms ← addDeclToUnfold thms ``Bool.xor
  thms ← addDeclToUnfold thms ``Ne
  return thms

/-- Returns the simplification context used by `lynth_grind`. -/
protected def getSimpContext (config : Lean.Grind.Config) : MetaM Simp.Context := do
  let thms ← getNormTheorems
  Simp.mkContext
    (config :=
      { arith := true
        zeta := config.zeta
        zetaDelta := config.zetaDelta
        -- Use `OfNat.ofNat` and `Neg.neg` for representing bitvec literals
        bitVecOfNat := false
        catchRuntime := false
        warnExponents := false
        -- `implicitDefEqProofs := true` a recurrent source of performance problems in the kernel
        implicitDefEqProofs := false })
    (simpTheorems := #[thms])
    (congrTheorems := (← getSimpCongrTheorems))

set_option compiler.ignoreBorrowAnnotation true in
@[export lean_grind_normalize]
def normalizeImp (e : Expr) (config : Lean.Grind.Config) : MetaM Expr := do
  let (r, _) ← Meta.simp e (← Lean.Lynth.Grind.getSimpContext config) (← Lean.Lynth.Grind.getSimprocs)
  return r.expr

end Lean.Lynth.Grind
