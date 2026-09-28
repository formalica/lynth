import Lean
import Lynth.Procedure
import Lynth.Witness
import Lynth.Answer.Procedure
import Lynth.Meta.Solver

/-!
Meta solver-function procedure: synthesize total `I → Option O`
solvers from finite candidate lists plus decidable checks.

Generic over all puzzles: recognizes `Subtype` goals whose domain is
a solver function (`I → Option O`) and whose predicate unfolds to the
three-conjunct correctness shape (soundness + completeness +
none-iff), extracts the validity predicate `P`, and builds
`enumSolve Fintype.elems (fun i o => decide (P i o))` with correctness
via `Lynth.Meta.Solver` lemmas (core axioms only). Yields gracefully
on anything else; never mentions any puzzle by name.
-/
namespace Lynth.Meta.Procedure

open Lean Elab Tactic Meta

/-- Solver domain match: `I → Option O` (non-dependent Pi). -/
def matchSolverDom (dom : Expr) : MetaM (Option (Expr × Expr)) := do
  let d ← whnf dom
  match d with
  | .forallE _ i o _ =>
    if o.hasLooseBVars then pure none
    else
      let oR ← whnf o
      match oR with
      | .app (.const ``Option _) _ =>
        let args := oR.getAppArgs
        if args.size != 1 then pure none
        else pure (some (i, args[0]!))
      | _ => pure none
  | _ => pure none

/-- Split `A ∧ B ∧ C` (right-nested `And`). -/
def splitAnd3 (e : Expr) : Option (Expr × Expr × Expr) := do
  let (fn1, args1) := (e.getAppFn, e.getAppArgs)
  match fn1 with
  | .const ``And _ =>
    if args1.size != 2 then none
    else
      let bc := args1[1]!
      let (fn2, args2) := (bc.getAppFn, bc.getAppArgs)
      match fn2 with
      | .const ``And _ =>
        if args2.size != 2 then none
        else some (args1[0]!, args2[0]!, args2[1]!)
      | _ => none
  | _ => none

/-- Extract the validity predicate as a two-argument lambda from the
soundness conjunct `∀ g c, solver g = some c → P g c`. Returns
`(inputTy, outputTy, P)` with `P : ∀ input output, Prop`. -/
def extractValid (pred solverDom : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  withLocalDeclD `solver solverDom fun s => do
    let spec ← whnf (mkApp pred s)
    let spec3 := splitAnd3 spec
    match spec3 with
    | none =>
      pure none
    | some (soundC, _, _) =>
      forallTelescope soundC fun fvs body => do
        -- soundness `∀ g c, Eq → P`: the telescope peels the
        -- implication hypothesis too, so expect 3 entries
        -- `[g, c, eqProof]` with `body = P`
        if fvs.size != 3 then
          return none
        let eqTy ← inferType fvs[2]!
        let pBody := body
        if pBody.hasLooseBVars then
          pure none
        else
          let eqR ← whnf eqTy
          match eqR.getAppFn with
          | .const ``Eq _ =>
            let args := eqR.getAppArgs
            if args.size != 3 then
              pure none
            else
              let lhs := args[1]!
              let rhs := args[2]!
              match lhs.getAppFn, rhs.getAppFn with
              | .fvar sid, .const ``Option.some _ =>
                if sid != s.fvarId! then
                  pure none
                else
                  let inTy ← inferType fvs[0]!
                  let outTy ← inferType fvs[1]!
                  let plam ← mkLambdaFVars #[fvs[0]!, fvs[1]!] pBody
                  pure (some (inTy, outTy, plam))
              | _, _ =>
                pure none
          | _ =>
            pure none

/-- Max output enumeration size for the decide fast path (larger
outputs yield to the future SAT-backed path using `FinVal`/`Differ`). -/
def maxEnumCard : Nat := 20000

/-- `Fin` literal from a type: `Fin k` with `k` a kernel literal
(direct or `OfNat`-wrapped). -/
def finLitTy (ty : Expr) : MetaM (Option Nat) := do
  let tyR ← whnf ty
  match tyR.getAppFn with
  | .const ``Fin _ =>
    let args := tyR.getAppArgs
    if args.isEmpty then pure none
    else
      let w ← whnf args.back!
      match w with
      | .lit (.natVal n) => pure (some n)
      | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ =>
        pure (some n)
      | _ => pure none
  | _ => pure none

/-- Membership in a built candidate list, dispatched on the list's
head (`finRange` vs `enumFun`). Shape-generic, never puzzle-bound. -/
def memElems (elems x : Expr) : MetaM Expr := do
  match elems.getAppFn with
  | .const ``List.finRange _ => mkAppM ``List.mem_finRange #[x]
  | .const ``Lynth.Meta.Solver.enumFun _ => mkAppM ``Lynth.Meta.Solver.mem_enumFun #[x]
  | _ => throwError "memElems: unknown elems head"

/-- Build the computable candidate list for `outTy` with cardinality
guard. Handles `Fin k` and `Fin n → Fin k` with literal bounds;
everything else (symbolic bounds, nestings, huge cards) yields to the
future SAT-backed path. -/
def getElems (outTy : Expr) : MetaM (Option Expr) := do
  try
    let outTyR ← whnf outTy
    -- cardinality guard first (never builds huge lists)
    match ← Lynth.Answer.Procedure.estCard maxEnumCard outTyR with
    | none =>
      pure none
    | some k =>
      if k == 0 then
        pure none
      else
        -- `Fin k` base
        match ← finLitTy outTyR with
        | some kk =>
          pure (some (mkApp (mkConst ``List.finRange []) (mkNatLit kk)))
        | none =>
          -- one-level `Fin n → Fin k` with literals (`cod` is
          -- non-dependent, so no substitution is needed)
          match outTyR with
          | .forallE _ dom cod _ =>
            if cod.hasLooseBVars then pure none
            else
              match ← finLitTy dom with
              | none => pure none
              | some nn =>
                match ← finLitTy cod with
                | none => pure none
                | some kk =>
                  pure (some (mkAppN (mkConst ``Lynth.Meta.Solver.enumFun [])
                    #[mkNatLit nn, mkNatLit kk]))
          | _ => pure none
  catch _ =>
    pure none

/-- Build the Boolean check `fun i o => decide (P i o)`.
Fails (yield) when `P` is undecidable. -/
def buildCheck (P inTy outTy : Expr) : MetaM (Option Expr) := do
  try
    -- unfold aliases in binder types (`Graph`, `Coloring`, …) so
    -- `Decidable` synthesis sees function structure (TC does not
    -- unfold user defs on its own)
    let inTyR ← whnf inTy
    let outTyR ← whnf outTy
    withLocalDeclD `input inTyR fun i =>
    withLocalDeclD `output outTyR fun o => do
      let pApp := mkApp (mkApp P i) o
      let pAppR ← Core.betaReduce pApp
      -- unfold validity aliases (`ColoringValid`, …) so `Decidable`
      -- synthesis sees the finite structure
      let pAppU ← whnf pAppR
      let dec ← mkDecide pAppU
      mkLambdaFVars #[i, o] dec
  catch _ => pure none

/-- Unfolded validity application `P g c` (beta + whnf). -/
def unfoldedApp (P g c : Expr) : MetaM Expr := do
  let pApp := mkApp (mkApp P g) c
  let pAppR ← Core.betaReduce pApp
  whnf pAppR

/-- Extract `(prop, inst)` from `check g c` by beta-reduction: the
result is `decide prop` with `inst : Decidable prop` baked in, so
callers reuse it instead of synthesizing anew (fresh synthesis fails
over alias-typed free vars). -/
def checkDecideAt (check g c : Expr) : MetaM (Option (Expr × Expr)) := do
  try
    let appR ← Core.betaReduce (mkApp (mkApp check g) c)
    match appR with
    | .app (.app (.const ``Decidable.decide _) prop) inst =>
      pure (some (prop, inst))
    | _ => pure none
  catch _ => pure none

/-- `of_decide_eq_true` with `check`'s baked-in instance: proves the
unfolded `P` from `h : check g c = true` without ever synthesizing a
fresh `Decidable` over alias-typed goal vars (which always fails). -/
def ofCheckTrue (check g c h : Expr) : MetaM Expr := do
  let some (pU, instU) ← checkDecideAt check g c
    | throwError "check shape"
  let decEq := mkApp (mkApp (mkConst ``Decidable.decide []) pU) instU
  let decTy ← mkEq decEq (mkConst ``Bool.true [])
  let hd ← mkExpectedTypeHint h decTy
  pure (mkAppN (mkConst ``of_decide_eq_true []) #[pU, instU, hd])

/-- Synthesize the solver value + correctness proof for `pred`,
closing the current `Subtype` goal. Returns `true` on success.
/// Uses `enumSolve` over `elems`/`check` with `Solver` lemmas;
/// all `decide` instances are reused from `check` (never freshly
/// synthesized over alias-typed goal vars). -/
def synthesize (shape : Lynth.Witness.WitShape) (P : Expr)
    (_inTy outTy elems check : Expr) : TacticM Bool := do
  try
    let solverVal ← mkAppM ``Lynth.Meta.Solver.enumSolve #[elems, check]
    unless ← isDefEq (← inferType solverVal) shape.dom do
      return false
    let spec ← whnf (mkApp shape.pred solverVal)
    let spec3 := splitAnd3 spec
    let (sC, cC, nC) ← match spec3 with
      | some t => pure t
      | none =>
        return false
    -- soundness: `∀ g c, solverVal g = some c → P g c`
    let soundPf ← forallTelescope sC fun fvs body => do
      if fvs.size != 3 then throwError "sound shape"
      let g := fvs[0]!
      let c := fvs[1]!
      let h := fvs[2]!
      let h1 ← mkAppM ``Lynth.Meta.Solver.enumSolve_sound
        #[elems, check, g, c, h]
      let pf ← ofCheckTrue check g c h1
      let pfH ← mkExpectedTypeHint pf body
      mkLambdaFVars fvs pfH
    -- output binder type from `check` (unfolded, so instances work)
    let cTyU ← lambdaTelescope check fun bs _ => do
      if bs.size != 2 then throwError "check shape"
      pure (← inferType bs[1]!)
    -- completeness: `∀ g, (∃ c, P g c) → ∃ c, solverVal g = some c`
    let completePf ← forallTelescope cC fun fvs body => do
      if fvs.size != 2 then throwError "complete shape"
      let g := fvs[0]!
      let hEx := fvs[1]!
      -- minor premise over unfolded output binder; `Exists.elim`
      -- accepts it up to defeq against the folded `hEx` predicate
      let minor ← withLocalDeclD `c cTyU fun cU => do
        let pU ← unfoldedApp P g cU
        withLocalDeclD `hc pU fun hcU => do
          -- `check g cU = true` from `hcU`, reusing `check`'s baked-in
          -- instance (never freshly synthesized over alias-typed vars)
          let some (_, instU) ← checkDecideAt check g cU
            | throwError "check shape"
          let decTrue := mkAppN (mkConst ``decide_eq_true [])
            #[pU, instU, hcU]
          let chkApp := mkApp (mkApp check g) cU
          let chkTy ← mkEq chkApp (mkConst ``Bool.true [])
          let chkTrue ← mkExpectedTypeHint decTrue chkTy
          -- `cU ∈ elems`
          let hmem ← memElems elems cU
          let hex ← mkAppM ``Lynth.Meta.Solver.enumSolve_complete
            #[elems, check, g, cU, hmem, chkTrue]
          mkLambdaFVars #[cU, hcU] hex
      -- eliminate the folded hypothesis with the unfolded minor
      -- (accepted up to defeq)
      let bodyC ← mkAppM ``Exists.elim #[hEx, minor]
      mkLambdaFVars fvs bodyC
    -- none-iff: `∀ g, solverVal g = none ↔ ¬∃ c, P g c`
    let nonePf ← forallTelescope nC fun fvs body => do
      if fvs.size != 1 then throwError "none shape"
      let g := fvs[0]!
      -- `body` is the `Iff`; split into sides for binder types
      let (lhs, rhs) ← match body with
        | .app (.app (.const ``Iff _) l) r => pure (l, r)
        | _ => throwError "none body not Iff"
      let hAll ← mkAppM ``Lynth.Meta.Solver.enumSolve_none_iff
        #[elems, check, g]
      -- forward: `= none → ¬∃` (inner minor proves `False`)
      let fwd ← withLocalDeclD `hN lhs fun hN => do
        let hAllF ← mkAppM ``Iff.mp #[hAll, hN]
        -- `rhs` is `¬∃ ..` (`Not`-applied); unfold to the arrow first
        let rhsR ← whnf rhs
        let exTy ← match rhsR with
          | .forallE _ d _ _ => pure d
          | _ => throwError "rhs shape"
        withLocalDeclD `hExInner exTy fun hExInner => do
          let minorF ← withLocalDeclD `c cTyU fun cU => do
            let pU ← unfoldedApp P g cU
            withLocalDeclD `hc pU fun hcU => do
              let some (_, instU) := ← checkDecideAt check g cU
                | throwError "check shape"
              let decTrue := mkAppN (mkConst ``decide_eq_true [])
                #[pU, instU, hcU]
              let chkApp := mkApp (mkApp check g) cU
              let chkTy ← mkEq chkApp (mkConst ``Bool.true [])
              let chkTrue ← mkExpectedTypeHint decTrue chkTy
              let hmem ← memElems elems cU
              let hF := mkApp (mkApp hAllF cU) hmem
              let hFeq ← mkExpectedTypeHint hF
                (← mkEq chkApp (mkConst ``Bool.false []))
              -- `chkTrue : chk = true`, `hFeq : chk = false`: derive
              -- `False` via `noConfusion` with explicit `False` motive
              -- (bare `mkAppM` leaves the motive stuck and fails)
              let transH ← mkAppM ``Eq.trans
                #[← mkAppM ``Eq.symm #[hFeq], chkTrue]
              let contraU := mkAppN (mkConst ``Bool.noConfusion [Level.zero])
                #[mkConst ``False [], mkConst ``Bool.false [],
                  mkConst ``Bool.true [], transH]
              let contra ← mkExpectedTypeHint contraU (mkConst ``False [])
              mkLambdaFVars #[cU, hcU] contra
          let contraE ← mkAppM ``Exists.elim #[hExInner, minorF]
          mkLambdaFVars #[hN, hExInner] contraE
      -- backward: `¬∃ → = none` via `∀ out ∈ elems, check = false`
      let bwd ← withLocalDeclD `hNe rhs fun hNe => do
        let rhsIff ← match (← inferType hAll) with
          | .app (.app (.const ``Iff _) _) r => pure r
          | _ => throwError "iff shape"
        let needRHS ← forallTelescope rhsIff fun fvs2 body2 => do
          if fvs2.size != 2 then throwError "rhs shape"
          let out := fvs2[0]!
          let hmem := fvs2[1]!
          let chkApp := mkApp (mkApp check g) out
          let chkTrueTy ← mkEq chkApp (mkConst ``Bool.true [])
          let lam ← withLocalDeclD `hT chkTrueTy fun hT => do
            let pfU ← ofCheckTrue check g out hT
            let outF ← mkExpectedTypeHint out outTy
            let foldAppR ← Core.betaReduce (mkApp (mkApp P g) outF)
            let pfF ← mkExpectedTypeHint pfU foldAppR
            let wit ← mkAppM ``Exists.intro #[outF, pfF]
            let rhsR ← whnf rhs
            let exTy ← match rhsR with
              | .forallE _ d _ _ => pure d
              | _ => throwError "rhs shape"
            let witH ← mkExpectedTypeHint wit exTy
            let contra := mkApp hNe witH
            mkLambdaFVars #[hT] contra
          -- `lam : ¬(check g out = true)`; conclude `= false`
          let hFalse ← mkAppM ``Bool.eq_false_of_ne_true #[lam]
          let hFalseH ← mkExpectedTypeHint hFalse body2
          mkLambdaFVars fvs2 hFalseH
        let mprRes ← mkAppM ``Iff.mpr #[hAll, needRHS]
        mkLambdaFVars #[hNe] mprRes
      let iffPf ← mkAppM ``Iff.intro #[fwd, bwd]
      let iffH ← mkExpectedTypeHint iffPf body
      mkLambdaFVars fvs iffH
    -- assemble `sound ∧ complete ∧ none` and close the goal
    let pfCC ← mkAppM ``And.intro #[completePf, nonePf]
    let pf ← mkAppM ``And.intro #[soundPf, pfCC]
    let specTy := mkApp shape.pred solverVal
    let pfH ← mkExpectedTypeHint pf specTy
    let val ← shape.mkVal solverVal pfH
    (← getMainGoal).assign val
    return true
  catch _ => return false

/-- Run: intro Pi params (e.g. board size), recognize solver subtypes,
extract the validity predicate, and synthesize via enumeration. -/
def run : TacticM ProcedureOutcome := do
  let snapshot ← saveState
  -- intro Pi binders (size params like `n`) to expose the Subtype
  let mut nIntros := 0
  while true do
    let t ← whnf (← getMainTarget)
    match t with
    | .forallE _ _ _ _ =>
      try
        evalTactic (← `(tactic| intro _))
        nIntros := nIntros + 1
      catch _ => break
    | _ => break
  let goal ← getMainTarget
  let some shape ← Lynth.Witness.classify goal
    | restoreState snapshot
      return .failure []
  match ← matchSolverDom shape.dom with
  | none =>
    restoreState snapshot
    return .failure []
  | some _ =>
    match ← extractValid shape.pred shape.dom with
    | none =>
      restoreState snapshot
      return .failure []
    | some (inTy, outTy, P) =>
      match ← getElems outTy with
      | none =>
        restoreState snapshot
        return .failure []
      | some elems =>
        match ← buildCheck P inTy outTy with
        | none =>
          restoreState snapshot
          return .failure []
        | some check =>
          if ← synthesize shape P inTy outTy elems check then
            return .success
          else
            restoreState snapshot
            return .failure []

end Lynth.Meta.Procedure
