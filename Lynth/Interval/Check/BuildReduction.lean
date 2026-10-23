module

import Lean
import Init.Data.Array.Lemmas
import Init.Data.List.ToArray
import Init.Data.Range.Lemmas

/-!
Proof automation used only while building `ReductionLemmas`.

The module system hides the executable bodies of four core Array/Range
operations. Existing core theorems relate them to reducible operations. We
prove those replacements through the checker definitions once, here, and put
all intermediate equalities in the bodies of shared library theorems.

This file is a private meta import. It is never called by `lynth` in a consumer.
No computational declaration is modified or added.
-/

namespace Lynth.Interval.CheckReduction
meta section
open Lean Meta

private def opaqueOperations : List Name :=
  [``Array.all, ``Array.mapM, ``Array.zip, ``Std.Legacy.Range.forIn']

/-- Find computational definitions that require a core compatibility theorem. -/
private partial def needsRewrite (name : Name) : StateT (NameMap Bool) MetaM Bool := do
  if opaqueOperations.contains name then
    modify (·.insert name true)
    return true
  if let some result := (← get).find? name then return result
  modify (·.insert name false)
  let some (.defnInfo info) := (← getEnv).find? name | return false
  if ← isProp info.type then return false
  let mut result := false
  for dep in info.value.getUsedConstants do
    if ← needsRewrite dep then result := true
  modify (·.insert name result)
  return result

/-- Normalize a class projection in a proof rule, using the existing theorem. -/
private def addBridge (rules : SimpTheorems) (name : Name) : MetaM SimpTheorems := do
  let ci ← getConstInfo name
  let proof := mkConst name (ci.levelParams.map Level.param)
  let type ← forallTelescope ci.type fun xs result => do
    let some (_, lhs, rhs) := result.eq? | throwError "expected equality theorem"
    let lhs ← withTransparency .all (whnf lhs)
    mkForallFVars xs (← mkEq lhs rhs)
  let proof := mkApp2 (mkConst ``id [0]) type proof
  rules.add (.other name) ci.levelParams.toArray proof

private def rewriteContext (rules : SimpTheorems) : MetaM Simp.Context :=
  Simp.mkContext
    (config := {
      maxSteps := 200000
      iota := false
      zeta := false
      decide := false
      dsimp := false
      instances := true
      index := false })
    (simpTheorems := #[rules])

private partial def constantRefs (e : Lean.Expr) : Array Lean.Expr := Id.run do
  let mut pending := #[e]
  let mut seen : Std.HashSet Lean.Expr := {}
  let mut result := #[]
  while !pending.isEmpty do
    let e := pending.back!
    pending := pending.pop
    if seen.contains e then continue
    seen := seen.insert e
    match e with
    | .const .. => result := result.push e
    | .app f a => pending := pending.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => pending := pending.push t |>.push b
    | .letE _ t v b _ => pending := pending.push t |>.push v |>.push b
    | .mdata _ b | .proj _ _ b => pending := pending.push b
    | _ => pure ()
  return result

private structure ProofState where
  lctx : LocalContext
  instances : LocalInstances
  locals : Array Lean.Expr := #[]
  seen : Std.HashSet Lean.Expr := {}
  rules : SimpTheorems := {}

private def inContext {α : Type} (action : MetaM α) : StateT ProofState MetaM α := do
  let s ← get
  withLCtx s.lctx s.instances action

private def bindValue (name : Name) (type value : Lean.Expr) :
    StateT ProofState MetaM Lean.Expr := do
  let id ← mkFreshFVarId
  let freshValue := mkFVar id
  modify fun s => { s with
    lctx := s.lctx.mkLetDecl id name type value
    locals := s.locals.push freshValue }
  return freshValue

private def reduceClassProjections (value : Lean.Expr) : MetaM Lean.Expr :=
  transform value (pre := fun e => do
    let .const name _ := e.getAppFn | return .continue
    let some info ← getProjectionFnInfo? name | return .continue
    unless info.fromClass do return .continue
    let reduced ← withTransparency .instances (whnf e)
    if reduced == e then return .continue
    return .visit reduced)

/-- Build the intermediate values and equalities for a shared library theorem. -/
private partial def prepare (needed : NameMap Bool) (original : Lean.Expr) :
    StateT ProofState MetaM Unit := do
  let .const name levels := original | return
  unless needed.getD name false do return
  if (← get).seen.contains original then return
  modify fun s => { s with seen := s.seen.insert original }
  if name == ``Array.mapM then return
  let ci ← getConstInfo name
  let type := ci.type.instantiateLevelParams ci.levelParams levels
  let value? : Option Lean.Expr ← match ci with
    | .defnInfo info => do
      let value ← reduceClassProjections (info.value.instantiateLevelParams ci.levelParams levels)
      pure (some value)
    | _ => pure none
  if let some value := value? then
    for dep in constantRefs value do prepare needed dep
  let rules := (← get).rules
  let (value, proof) ← inContext do
    let ctx ← rewriteContext rules
    match value? with
    | some value =>
      let (result,_) ← simp value ctx
      return (result.expr, ← result.getProof)
    | none =>
      forallTelescope type fun xs _ => do
        let app := mkAppN original xs
        let (result,_) ← simp app ctx
        unless result.proof?.isSome do
          throwError "no kernel proof rewrite for {name}"
        let value ← mkLambdaFVars xs result.expr
        let mut proof ← result.getProof
        for x in xs.reverse do
          proof ← mkAppM ``funext #[← mkLambdaFVars #[x] proof]
        return (value,proof)
  let replacement ← bindValue `reducedValue type value
  let equality ← inContext <| mkEq original replacement
  let evidence ← bindValue `valueEquality equality proof
  let rules ← inContext <| rules.add (.fvar evidence.fvarId!) #[] evidence
  modify fun s => { s with rules }


/-- The equivalence is assembled at library build time, never during tactic use. -/
def derive (originalName theoremName : Name) (inContext : Bool := false) : MetaM Unit :=
    withAtLeastMaxRecDepth 10000 do
  let ci ← getConstInfo originalName
  unless ci.levelParams.isEmpty do throwError "expected a monomorphic checker"
  let original := mkConst originalName
  let (_, needed) ← (needsRewrite originalName).run {}
  let mut rules : SimpTheorems := {}
  for name in [``Array.all_eq_not_any_not, ``Array.mapM_eq_mapM_toList,
      ``List.zip_toArray] do
    rules ← rules.addConst name
  rules ← addBridge rules ``Std.Legacy.Range.forIn'_eq_forIn'_range'
  rules ← addBridge rules ``Std.Legacy.Range.forIn_eq_forIn_range'
  let (_, state) ← (prepare needed original).run {
    lctx := ← getLCtx, instances := ← getLocalInstances, rules }
  withLCtx state.lctx state.instances do
    let value := state.locals[state.locals.size - 2]!
    let evidence := state.locals.back!
    let values := state.locals.filter fun e =>
      (state.lctx.get! e.fvarId!).userName == `reducedValue
    let rhs ← mkLetFVars values value (generalizeNondepLet := false)
    let truth := mkConst ``Bool.true
    let (type, body) ← if !inContext then do
      unless !rhs.hasFVar do throwError "checker depends on an intermediate proof"
      let type ← forallTelescope ci.type fun xs _ => do
        mkForallFVars xs (← mkArrow (← mkEq (mkAppN rhs xs) truth)
          (← mkEq (mkAppN original xs) truth))
      let body ← forallTelescope ci.type fun xs _ => do
        withLocalDeclD `h (← mkEq (mkAppN value xs) truth) fun h => do
          let mut equality := evidence
          for x in xs do equality ← mkCongrFun equality x
          mkLambdaFVars (xs.push h) (← mkEqTrans equality h)
      pure (type, body)
    else do
      -- An eta function record has a soundness proof depending on its evaluator.
      -- Quantify the corresponding equality in the premise: the caller supplies
      -- `fun _ => rfl`, and this theorem supplies the actual equality privately.
      let proofParams := state.locals.filter fun e =>
        (state.lctx.get! e.fvarId!).userName == `valueEquality &&
          (rhs.find? (· == e)).isSome
      let quantifyProofs (body : Lean.Expr) : MetaM Lean.Expr := do
        let mut body := body
        for p in proofParams.reverse do
          let ty ← mkLetFVars values (← inferType p) (generalizeNondepLet := false)
          body := .forallE `compatibility ty (body.abstract #[p]) .default
        return body
      let contextType ← mkArrow ci.type (mkConst ``Bool)
      let type ← withLocalDeclD `k contextType fun k => do
        mkForallFVars #[k] (← mkArrow (← quantifyProofs (← mkEq (mkApp k rhs) truth))
          (← mkEq (mkApp k original) truth))
      unless !type.hasFVar do throwError "function record depends on an unbound proof"
      let body ← withLocalDeclD `k contextType fun k => do
        withLocalDeclD `h (← quantifyProofs (← mkEq (mkApp k rhs) truth)) fun h => do
          let equality ← mkCongrArg k evidence
          mkLambdaFVars #[k, h] (← mkEqTrans equality (mkAppN h proofParams))
      pure (type, body)
    let body ← mkLetFVars state.locals body (generalizeNondepLet := false)
    -- Export only the theorem header. Lean keeps the checked proof body private.
    withExporting (isExporting := true) do
      addDecl (.thmDecl { name := theoremName, levelParams := [], type, value := body })

end
end Lynth.Interval.CheckReduction
