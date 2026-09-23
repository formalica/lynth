/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lynth.Grind.Main
public import Lean.Meta.Tactic.TryThis
public import Lynth.Grind.Elab.Config
public import Lean.LibrarySuggestions.Basic
import Lynth.Grind.SimpUtil
import Lynth.Grind.Elab.Param
import Lynth.Grind.Finish
import Lynth.Grind.CollectParams
import Lynth.Grind.AttrSyntax
import Lean.Meta.Tactic.Grind.Parser
public section
namespace Lean.Lynth.Grind.Elab
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta

open Command Term in
open Lean.Parser.Command.GrindCnstr in
def elabGrindPattern : CommandElab := fun stx => do
  match stx with
  | `(grind_pattern $[[ $attr?:ident ]]? $thmName:ident => $terms,* $[$cnstrs?:grindPatternCnstrs]?) => go attr? thmName terms cnstrs? .global
  | `(scoped grind_pattern $[[ $attr?:ident ]]? $thmName:ident => $terms,* $[$cnstrs?:grindPatternCnstrs]?) => go attr? thmName terms cnstrs? .scoped
  | `(local grind_pattern $[[ $attr?:ident ]]? $thmName:ident => $terms,* $[$cnstrs?:grindPatternCnstrs]?) => go attr? thmName terms cnstrs? .local
  | _ => throwUnsupportedSyntax
where
  findLHS (xs : Array Expr) (lhs : Syntax) : TermElabM (LocalDecl × Nat) := do
    let lhsId := lhs.getId
    let mut i := 0
    for x in xs do
      let xDecl ← x.fvarId!.getDecl
      if xDecl.userName == lhsId then
        return (xDecl, xs.size - i - 1)
      i := i + 1
    throwErrorAt lhs "invalid constraint, `{lhsId}` is not local variable of the theorem"

  elabCnstrRHS (xs : Array Expr) (rhs : Syntax) (expectedType : Expr) : TermElabM Lean.Lynth.Grind.CnstrRHS := do
    /-
    **Note**: We need better sanity checking here.
    We must check whether the type of `rhs` is type correct with respect to
    an arbitrary instantiation of `xs`. That is, we should use meta-variables
    in the check. It is incorrect to use `xDecl.type`. For example, suppose the
    type of `xDecl` is `α → β` where `α` and `β` are variables in `xs` occurring before
    `xDecl`, and `rhsExpr` is `some : ?m → ?m`. The types `α → β =?= ?m → ?m` are
    not definitionally equal, but `?α → ?β =?= ?m → ?m` are.
    -/
    let rhsExpr ← Term.elabTerm rhs expectedType
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let rhsExpr ← instantiateMVars rhsExpr
    if rhsExpr.hasSyntheticSorry then
      throwErrorAt rhs "invalid constraint, rhs contains a synthetic `sorry`"
    let rhsExpr := rhsExpr.eta
    let { paramNames := levelNames, mvars, expr := rhs } ← abstractMVars rhsExpr
    let numMVars := mvars.size
    let rhs := rhs.abstract xs
    return { levelNames, numMVars, expr := rhs }

  elabProp (xs : Array Expr) (term : Syntax) : TermElabM Expr := do
    let e ← Term.elabTermAndSynthesize term (Expr.sort 0)
    let e ← instantiateMVars e
    if e.hasSyntheticSorry then
      throwErrorAt term "invalid proposition, it contains a synthetic `sorry`"
    if e.hasMVar then
      throwErrorAt term "invalid proposition, it contains metavariables{indentExpr e}"
    return e.abstract xs

  elabNotDefEq (xs : Array Expr) (lhs rhs : Syntax) : TermElabM Lean.Lynth.Grind.EMatchTheoremConstraint := do
    let (localDecl, lhsBVarIdx) ← findLHS xs lhs
    let rhs ← elabCnstrRHS xs rhs localDecl.type
    return .notDefEq lhsBVarIdx rhs

  elabDefEq (xs : Array Expr) (lhs rhs : Syntax) : TermElabM Lean.Lynth.Grind.EMatchTheoremConstraint := do
    let (localDecl, lhsBVarIdx) ← findLHS xs lhs
    let rhs ← elabCnstrRHS xs rhs localDecl.type
    return .defEq lhsBVarIdx rhs

  elabCnstrs (xs : Array Expr) (cnstrs? : Option (TSyntax ``Parser.Command.grindPatternCnstrs))
      : TermElabM (List (Lean.Lynth.Grind.EMatchTheoremConstraint)) := do
    let some cnstrs := cnstrs? | return []
    let cnstrs := cnstrs.raw[1].getArgs
    cnstrs.toList.mapM fun cnstr => do
      let kind := cnstr.getKind
      if kind == ``notDefEq then
        elabNotDefEq xs cnstr[0] cnstr[2]
      else if kind == ``defEq then
        elabDefEq xs cnstr[0] cnstr[2]
      else if kind == ``genLt then
        return .genLt cnstr[2].toNat
      else if kind == ``sizeLt then
        let (_, lhs) ← findLHS xs cnstr[1]
        return .sizeLt lhs cnstr[3].toNat
      else if kind == ``depthLt then
        let (_, lhs) ← findLHS xs cnstr[1]
        return .depthLt lhs cnstr[3].toNat
      else if kind == ``maxInsts then
        return .maxInsts cnstr[2].toNat
      else if kind == ``isValue then
        let (_, lhs) ← findLHS xs cnstr[1]
        return .isValue lhs false
      else if kind == ``isStrictValue then
        let (_, lhs) ← findLHS xs cnstr[1]
        return .isValue lhs true
      else if kind == ``notValue then
        let (_, lhs) ← findLHS xs cnstr[1]
        return .notValue lhs false
      else if kind == ``notStrictValue then
        let (_, lhs) ← findLHS xs cnstr[1]
        return .notValue lhs true
      else if kind == ``isGround then
        let (_, lhs) ← findLHS xs cnstr[1]
        return .isGround lhs
      else if kind == ``Parser.Command.GrindCnstr.check then
        return .check (← elabProp xs cnstr[1])
      else if kind == ``Parser.Command.GrindCnstr.guard then
        return .guard (← elabProp xs cnstr[1])
      else
        throwErrorAt cnstr "unexpected constraint"

  go (attrName? : Option (TSyntax `ident)) (thmName : TSyntax `ident) (terms : Syntax.TSepArray `term ",")
      (cnstrs? : Option (TSyntax ``Parser.Command.grindPatternCnstrs))
      (kind : AttributeKind) : CommandElabM Unit := liftTermElabM do
    let attrName := if let some attrName := attrName? then attrName.getId else `lynth_grind
    let some ext ← Lean.Lynth.Grind.getExtension? attrName | throwError "unknown `lynth_grind` attribute `{attrName}`"
    let declName ← realizeGlobalConstNoOverloadWithInfo thmName
    let info ← getConstVal declName
    forallTelescope info.type fun xs _ => do
      let patterns ← terms.getElems.mapM fun term => do
        let pattern ← Term.elabTerm term none
        synthesizeSyntheticMVarsUsingDefault
        let pattern ← instantiateMVars pattern
        let pattern ← Lean.Lynth.Grind.preprocessPattern pattern
        return pattern.abstract xs
      let cnstrs ← elabCnstrs xs cnstrs?
      ext.addEMatchTheorem declName xs.size patterns.toList .user kind cnstrs (minIndexable := false)

open Command in
def elabResetGrindAttrs : CommandElab := fun _ => liftTermElabM do
  -- Remark: we do not reset symbol priorities because we would have to then set
  -- `[grind symbol 0] Eq` after a `reset_grind_attr%` command.
  -- Lean.Lynth.Grind.resetSymbolPrioExt
  modifyEnv fun env => Lean.Lynth.Grind.lynthGrindExt.modifyState env fun ext => { ext with casesTypes := {}, inj := {}, ematch := {} }
  modifyEnv fun env => Lean.Lynth.Grind.homoExt.modifyState env fun _ => {}
  modifyEnv fun env => Lean.Lynth.Grind.homoPredExt.modifyState env fun _ => {}
  modifyEnv fun env => Lean.Lynth.Grind.homoSourceTypesExt.modifyState env fun _ => {}

open Command Term in
def elabInitGrindNorm : CommandElab := fun stx =>
  withExporting do  -- should generate public aux decls
  match stx with
  | `(init_grind_norm $pre:ident* | $post*) =>
    Command.liftTermElabM do
      let pre ← pre.mapM fun id => realizeGlobalConstNoOverloadWithInfo id
      let post ← post.mapM fun id => realizeGlobalConstNoOverloadWithInfo id
      -- Creates `Lean.Grind._simp_1` etc.. As we do not use this command in independent modules,
      -- there is no chance of name conflicts.
      withDeclNameForAuxNaming `Lean.Grind do
        Lean.Lynth.Grind.registerNormTheorems pre post
  | _ => throwUnsupportedSyntax

private def parseModifier (s : String) : CoreM Lean.Lynth.Grind.AttrKind := do
  let stx := Parser.runParserCategory (← getEnv) `Lean.Parser.Attr.grindMod s
  match stx with
  | .ok stx => Lean.Lynth.Grind.getAttrKindCore stx
  | _ => throwError "unexpected modifier {s}"

open LibrarySuggestions in
def elabGrindSuggestions
    (params : Lean.Lynth.Grind.Params) (suggestions : Array Suggestion := #[]) : MetaM Lean.Lynth.Grind.Params := do
  let mut params := params
  let mut added : Array Name := #[]
  for p in suggestions do
    let attr ← match p.flag with
    | some flag => parseModifier flag
    | none => pure <| .ematch (.default false)
    match attr with
    | .ematch kind =>
      try
        params ← addEMatchTheorem params (mkIdent p.name) p.name kind false (warn := false)
        added := added.push p.name
      catch _ => pure () -- Don't worry if library suggestions gave bad theorems.
    | _ =>
      -- We could actually support arbitrary grind modifiers,
      -- and call `processParam` rather than `addEMatchTheorem`,
      -- but this would require a larger refactor.
      -- Let's only do this if there is a prospect of a library suggestion engine supporting this.
      throwError "unexpected modifier {p.flag}"
  unless added.isEmpty do
    trace[grind.debug.suggestions] "{added}"
  return params

/-- Add all definitions from the current file. -/
def elabGrindLocals (params : Lean.Lynth.Grind.Params) : MetaM Lean.Lynth.Grind.Params := do
  let env ← getEnv
  let mut params := params
  let mut added : Array Name := #[]
  for c in ← env.getLocalConstantInfos (skipTheoremSubDecls := true) do
    let name := c.name
    -- Filter similar to LibrarySuggestions.isDeniedPremise (but inlined to avoid dependency)
    -- Skip internal details, but allow private names (which are accessible from current module)
    if name.isInternalDetail && !isPrivateName name then continue
    if c.kind != .defn then continue
    if (← isInstanceReducible name) then continue
    try
      params ← addEMatchTheorem params (mkIdent name) name (.default false) false (warn := false)
      added := added.push name
    catch _ => pure ()
  unless added.isEmpty do
    trace[grind.debug.locals] "{added}"
  return params

def mkGrindParams
    (config : Lean.Grind.Config) (only : Bool) (ps : TSyntaxArray ``Parser.Tactic.grindParam) (mvarId : MVarId)
    (extensions? : Option Lean.Lynth.Grind.ExtensionStateArray := none) :
    TermElabM Lean.Lynth.Grind.Params := do
  let params ← match extensions? with
    | some extensions => Lean.Lynth.Grind.mkParams config extensions
    | none => if only then Lean.Lynth.Grind.mkOnlyParams config else Lean.Lynth.Grind.mkDefaultParams config
  let mut params ← elabGrindParams params ps (lax := config.lax) (only := only)
  if config.suggestions then
    let lsConfig : LibrarySuggestions.Config := { caller := some "lynth_grind" }
    let lsConfig := match config.maxSuggestions with
      | some n => { lsConfig with maxSuggestions := n }
      | none => lsConfig
    params ← elabGrindSuggestions params (← LibrarySuggestions.select mvarId lsConfig)
  if config.locals then
    params ← elabGrindLocals params
  trace[grind.debug.inj] "{params.extensions[0]!.inj.getOrigins.map (·.pp)}"
  if params.anchorRefs?.isSome then
    /-
    **Note**: anchors are automatically computed in interactive mode where
    hygiene is turned on. So, we must disable hypotheses id cleanup since
    different ids will affect the anchor values.
    **TODO**: a more robust solution since users may use `lynth_grind +clean => finish?`
    -/
    params := { params with config.clean := false }
  return params

def checkTerminalAsSorry (mvarId : MVarId) : TacticM Bool := do
  if debug.terminalTacticsAsSorry.get (← getOptions) then
    mvarId.admit
    Lean.Elab.Tactic.replaceMainGoal []
    return true
  else
    return false

def grind
    (mvarId : MVarId) (config : Lean.Grind.Config)
    (only : Bool)
    (ps   :  TSyntaxArray ``Parser.Tactic.grindParam)
    (seq? : Option (TSyntax `Lean.Parser.Tactic.Grind.grindSeq))
    (extensions? : Option Lean.Lynth.Grind.ExtensionStateArray := none)
    : TacticM Unit := do
  if (← checkTerminalAsSorry mvarId) then return ()
  mvarId.withContext do
    let params ← mkGrindParams config only ps mvarId (extensions? := extensions?)
    let params := if Lean.Lynth.Grind.lynth_grind.unusedLemmaThreshold.get (← getOptions) > 0 then
      { params with config.markInstances := true }
    else params
    Lean.Lynth.Grind.withProtectedMCtx config mvarId fun mvarId' => do
      let finalize (result : Lean.Lynth.Grind.Result) : TacticM Unit := do
        if result.hasFailed then
          throwError "`lynth_grind` failed\n{← result.toMessageData}"
        Lean.Elab.Tactic.replaceMainGoal []
      if let some seq := seq? then
        let (result, _) ← Lean.Lynth.Grind.Elab.GrindTacticM.runAtGoal mvarId' params do
          Lean.Lynth.Grind.Elab.evalGrindTactic seq
          -- **Note**: We are returning only the first goal that could not be solved.
          let goal? := if let goal :: _ := (← get).goals then some goal else none
          let result ← Lean.Lynth.Grind.Elab.liftGrindM <| Lean.Lynth.Grind.mkResult params goal?
          if goal?.isNone then
            Lean.Lynth.Grind.Elab.liftGrindM <| Lean.Lynth.Grind.checkUnusedActivations mvarId' result.counters
          return result
        finalize result
      else
        let result ← Lean.Lynth.Grind.main mvarId' params
        finalize result

def evalGrindCore
    (ref : Syntax)
    (config : Lean.Grind.Config)
    (only : Option Syntax)
    (params? : Option (Syntax.TSepArray `Lean.Parser.Tactic.grindParam ","))
    (seq? : Option (TSyntax `Lean.Parser.Tactic.Grind.grindSeq))
    (extensions? : Option Lean.Lynth.Grind.ExtensionStateArray := none)
    : TacticM Unit := do
  let only := only.isSome
  let params := if let some params := params? then params.getElems else #[]
  if Lean.Lynth.Grind.lynth_grind.warning.get (← getOptions) then
    logWarningAt ref "The `lynth_grind` tactic is new and its behavior may change in the future. This project has used `set_option lynth_grind.warning true` to discourage its use."
  grind (← Lean.Elab.Tactic.getMainGoal) config only params seq? (extensions? := extensions?)

/-- Position for the `[..]` child syntax in the `lynth_grind` tactic. -/
def grindParamsPos := 3

/-- Position for the `only` child syntax in the `lynth_grind` tactic. -/
def grindOnlyPos := 2

def isGrindOnly (stx : TSyntax `tactic) : Bool :=
  stx.raw.getKind == ``Parser.Tactic.grind && !stx.raw[grindOnlyPos].isNone

def setGrindParams (stx : TSyntax `tactic) (params : Array Syntax) : TSyntax `tactic :=
  if params.isEmpty then
    ⟨stx.raw.setArg grindParamsPos (mkNullNode)⟩
  else
    let paramsStx := #[mkAtom "[", (mkAtom ",").mkSep params, mkAtom "]"]
    ⟨stx.raw.setArg grindParamsPos (mkNullNode paramsStx)⟩

def getGrindParams (stx : TSyntax `tactic) : Array Syntax :=
  stx.raw[grindParamsPos][1].getSepArgs

/-- Filter out `+suggestions` and `+locals` from the config syntax -/
def filterSuggestionsAndLocalsFromGrindConfig (config : TSyntax ``Lean.Parser.Tactic.optConfig) :
    TSyntax ``Lean.Parser.Tactic.optConfig :=
  -- optConfig structure: (Tactic.optConfig [configItem1, configItem2, ...])
  -- config.raw.getArgs returns #[null_node], so we need to filter the null node's children
  let nullNode := config.raw[0]!
  let configItems := nullNode.getArgs
  let filteredItems := configItems.filter fun configItem =>
    -- Keep all items except +suggestions and +locals
    -- Structure: configItem -> posConfigItem -> ["+", ident]
    match configItem[0]? with
    | some posConfigItem => match posConfigItem[1]? with
      | some ident =>
        let id := ident.getId.eraseMacroScopes
        !(posConfigItem.getKind == ``Lean.Parser.Tactic.posConfigItem && (id == `suggestions || id == `locals))
      | none => true
    | none => true
  ⟨config.raw.setArg 0 (nullNode.setArgs filteredItems)⟩

def elabGrindConfig' (config : TSyntax ``Lean.Parser.Tactic.optConfig) (interactive : Bool) : TacticM Lean.Grind.Config := do
  if interactive then
    elabGrindConfigInteractive config
  else
    elabGrindConfig config

def evalGrindTraceCore (stx : Syntax) (trace := true) (verbose := true) (useSorry := true) : TacticM (Array (TSyntax `tactic)) := Lean.Elab.Tactic.withMainContext do
  let `(tactic| lynth_grind? $configStx:optConfig $[only%$only]?  $[ [$params?:grindParam,*] ]?) := stx
    | throwUnsupportedSyntax
  let config ← elabGrindConfig configStx
  let config := { config with clean := false, trace, verbose, useSorry }
  let only := only.isSome
  let paramStxs := if let some params := params? then params.getElems else #[]
  -- Extract term parameters (non-ident params) to include in the suggestion.
  -- These are not tracked via E-matching, so we conservatively include them all.
  -- Plain ident params that resolve to global declarations are tracked via E-matching.
  -- But idents with local variable dot notation (e.g., `cs.getD_rightInvSeq` where `cs`
  -- is a local variable) must be preserved because they produce anchors that need
  -- the original term to be loaded during replay.
  -- Non-ident terms (like `show P by tac`) need to be preserved explicitly.
  -- Params that mark types for case-splitting (e.g., `[EqvGen]` where `EqvGen` is an
  -- inductive predicate, or `[cases T]`) must also be preserved: the marking is not
  -- representable in the generated script, and without it `cases` steps on facts of
  -- these types fail during replay.
  -- **TODO**: This syntactic filtering is a stopgap: it duplicates parameter-elaboration
  -- logic and silently depends on which side effects are representable in scripts.
  -- A more robust solution is to make the script self-contained, e.g., a script step that
  -- marks a type for case-splitting, and tracking which parameters were actually used.
  let keepIdentParam (mod? : Option (TSyntax ``Parser.Attr.grindMod)) (id : Ident) : TacticM Bool := do
    if let some (_, _ :: _) := (← resolveLocalName id.getId) then
      return true
    else if let some mod := mod? then
      return (← Lean.Lynth.Grind.getAttrKindCore mod) matches .cases _
    else
      let declName? ← try pure (some (← realizeGlobalConstNoOverload id)) catch _ => pure none
      if let some declName := declName? then
        Lean.Lynth.Grind.isCasesAttrCandidate declName false
      else
        return false
  let termParamStxs : Array Lean.Lynth.Grind.TParam ← paramStxs.filterM fun p => do
    match p with
    | `(Parser.Tactic.grindParam| $[$mod?:grindMod]? $id:ident) => keepIdentParam mod? id
    | `(Parser.Tactic.grindParam| ! $[$mod?:grindMod]? $id:ident) => keepIdentParam mod? id
    | `(Parser.Tactic.grindParam| - $_:ident) => return false
    | `(Parser.Tactic.grindParam| #$_:hexnum) => return false
    | _ => return true
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let params ← mkGrindParams config only paramStxs mvarId
  Lean.Lynth.Grind.withProtectedMCtx config mvarId fun mvarId' => do
    let (tacs, _) ← Lean.Lynth.Grind.Elab.GrindTacticM.runAtGoal mvarId' params do
      let finish ← Lean.Lynth.Grind.Action.mkFinish
      let goal :: _ ← Lean.Lynth.Grind.Elab.getGoals
        | -- Goal was closed during initialization
          let configStx' := filterSuggestionsAndLocalsFromGrindConfig configStx
          if termParamStxs.isEmpty then
            let tac ← `(tactic| lynth_grind $configStx':optConfig only)
            return #[tac]
          else
            let tac ← `(tactic| lynth_grind $configStx':optConfig only [$termParamStxs,*])
            return #[tac]
      Lean.Lynth.Grind.Elab.liftGrindM do
        -- **Note**: If we get failures when using the first suggestion, we should test is using `saved`
        -- let saved ← saveState
        match (← finish.run goal) with
        | .closed seq =>
          let configStx' := filterSuggestionsAndLocalsFromGrindConfig configStx
          let tacs ← Lean.Lynth.Grind.mkGrindOnlyTactics configStx' seq termParamStxs
          let seq := Lean.Lynth.Grind.Action.mkGrindSeq seq
          /-
          **Note**: The script must carry the preserved parameters (e.g., types marked for
          case-splitting). The tactic was verified with these parameters active, and `cases`
          steps may fail without them.
          -/
          let tac ← if termParamStxs.isEmpty then
            `(tactic| lynth_grind $configStx':optConfig => $seq:grindSeq)
          else
            `(tactic| lynth_grind $configStx':optConfig [$termParamStxs,*] => $seq:grindSeq)
          let tacs := tacs.push tac
          return tacs
        | .stuck gs =>
          let goal :: _ := gs | throwError "`lynth_grind?` failed, but resulting goal is not available"
          let result ← Lean.Lynth.Grind.mkResult params (some goal)
          throwError "`lynth_grind?` failed\n{← result.toMessageData}"
    return tacs

end Lean.Lynth.Grind.Elab
