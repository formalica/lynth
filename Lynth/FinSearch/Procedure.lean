import Lean
import Std.Tactic.BVDecide
import Lynth.Procedure
import Lynth.Witness
import Lynth.FinSearch.Syntax
import Lynth.FinSearch.Encode
import Lynth.FinSearch.Detect
import Lynth.FinSearch.Recognize

/-!
Finite-domain synthesis procedure: constraint puzzles with subtype
answers over finite function domains.

Runs FIRST in the pipeline: scalar domains yield to `Witness` (which
owns them); function domains over finite types (`Fin n`, `Bool`) go
to the SAT child. Decidable constraints (`Recognize`) become CNF
(`Encode`), CDCL finds a model, the model decodes to a closed value
term (nested `fun` + `List.getD` chains), and kernel-checked side
tactics verify it. Sound by construction: only verified models close
goals; everything else yields.
-/
namespace Lynth.FinSearch.Procedure

open Lean Elab Tactic Meta
open Lynth.FinSearch
open Lynth.FinSearch.Recognize
open Lynth.FinSearch.Encode

/-- Finite domain descriptor: type + cardinality. -/
structure FDom where
  ty : Expr
  card : Nat

/-- Classify a domain type: `Bool`/`Fin n` fast paths, otherwise any
non-recursive inductive over finite fields (`Option`/`Sum`/`Prod`/…).
Literal bounds only for `Fin`; nothing here is `Option`-specific. -/
def domOf (ty : Expr) : MetaM (Option FDom) := do
  let tyR ← whnf ty
  match tyR with
  | .const ``Bool _ => pure (some { ty, card := 2 })
  | _ =>
    match tyR.getAppFn with
    | .const ``Fin _ =>
      let tyArgs := tyR.getAppArgs
      if tyArgs.isEmpty then pure none
      else
        let w ← whnf tyArgs.back!
        match w with
        | .lit (.natVal n) =>
          if n == 0 then pure none else pure (some { ty, card := n })
        | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ =>
          if n == 0 then pure none else pure (some { ty, card := n })
        | _ => pure none
    | _ =>
      match ← finCard ty 8 with
      | some n => if n == 0 then pure none else pure (some { ty, card := n })
      | none => pure none

/-- Peel Pi binders with finite literal domains; returns binder
descriptors + codomain. `none` = scalar (yield to `Witness`) or
unsupported (dependent binders, non-finite types).
Unfolds with default transparency so user type aliases
(`def Board := Fin 9 → Fin 9 → Fin 9`) are seen through. -/
def analyzeDomain (dom : Expr) : MetaM (Option (List FDom × FDom)) := do
  let dom ← whnf dom
  go dom [] 8
where
  go (cur : Expr) (dims : List FDom) : Nat → MetaM (Option (List FDom × FDom))
    | 0 => pure none
    | fuel + 1 => do
      let curR ← whnf cur
      match curR with
      | .forallE _ d b _ =>
        if b.hasLooseBVars then pure none
        else match ← domOf d with
          | some fd => go b (dims ++ [fd]) fuel
          | none => pure none
      | _ =>
        match ← domOf cur with
        | some c =>
          if dims.isEmpty then pure none
          else pure (some (dims, c))
        | none => pure none

/-- SAT-model bit lookup (default false; complete models never miss). -/
def lookupAssign (m : Lynth.Sat.Assignment) (v : Nat) : Bool :=
  match m.getD (v - 1) none with
  | some b => b
  | none => false

/-- Decode a CDCL model to per-cell values. Cells are atom ids;
bits are scanned from the var map itself. -/
def decodeModel (vmap : List ((Nat × Nat) × Nat))
    (model : Lynth.Sat.Assignment) (nCells : Nat) : List Nat :=
  (List.range nCells).map fun a =>
    let bits := vmap.filterMap fun ((x, y), v) =>
      if x == a then some (y, v) else none
    match bits.find? fun (_, v) => lookupAssign model v with
    | some (w, _) => w
    | none => 0

/-- Closed literal for a decoded value: `Bool` via constants,
`Fin` via `Fin.mk` + decided bound, anything else finite via the
generic constructor layout (inverse of `exprToIdx`). -/
def valLit (cod : FDom) (v : Nat) : MetaM Expr := do
  let ct ← whnfR cod.ty
  match ct with
  | .const ``Bool _ =>
    pure (if v == 1 then mkConst ``Bool.true else mkConst ``Bool.false)
  | _ =>
    match ct.getAppFn with
    | .const ``Fin _ =>
      let hlt ← mkAppM ``LT.lt #[mkNatLit v, mkNatLit cod.card]
      let pf ← mkDecideProof hlt
      mkAppM ``Fin.mk #[mkNatLit v, pf]
    | _ =>
      match ← finValExpr cod.ty v with
      | some e => pure e
      | none => throwError "finsearch: value {v} out of range"

/-- Build a closed value for a function domain from decoded cells.
`dims`: binder descriptors; `cod`: codomain; `get`: decoded value
for argument-value lists. Nested `fun` + `List.getD` chains, all
closed and kernel-evaluable. -/
def buildFunVal (dims : List FDom) (cod : FDom)
    (get : List Nat → Nat) : MetaM Expr := do
  -- table type at a suffix level: `List ^k codTy`
  -- (`getDecLevel`: `List.{u}` needs the level of the type itself,
  -- not the sort level that `getLevel` returns)
  let rec tabTy : List FDom → MetaM Expr
    | [] => pure cod.ty
    | _ :: ds => do
      let e ← tabTy ds
      let u ← getDecLevel e
      pure (mkApp (mkConst ``List [u]) e)
  -- nested table literal over all argument tuples
  let rec buildTab : List FDom → List Nat → MetaM Expr
    | [], args => valLit cod (get args.reverse)
    | d :: ds, args => do
      let rows ← (List.range d.card).mapM fun v => buildTab ds (v :: args)
      mkListLit (← tabTy ds) rows
  -- binders with access chain (`Fin.val` / `Bool.toNat` indices)
  let rec bind : List FDom → (List Expr → MetaM Expr) → MetaM Expr
    | [], k => k []
    | d :: ds, k =>
      withLocalDeclD `i d.ty fun fv => bind ds (fun fvs => k (fv :: fvs))
  bind dims fun fvs => do
    let tab ← buildTab dims []
    let mut acc := tab
    for (fv, d) in fvs.zip dims do
      let idx ←
        match ← whnfR d.ty with
        | .const ``Bool _ => mkAppM ``Bool.toNat #[fv]
        | .app (.const ``Fin _) _ => mkAppM ``Fin.val #[fv]
        | _ =>
          -- generic finite binder: linear `==`-search over the
          -- enumerated values (computable, so the kernel-checked
          -- side proof still evaluates; `mkAppM` synthesizes the
          -- `BEq` instance and the procedure yields if absent)
          let some n ← finCard d.ty 8
            | throwError "finsearch: non-finite binder"
          if n == 0 then throwError "finsearch: empty binder"
          else
            let mut e := mkNatLit (n - 1)
            for j in (List.range (n - 1)).reverse do
              let some vj ← finValExpr d.ty j
                | throwError "finsearch: no literal"
              let c ← mkAppM ``BEq.beq #[fv, vj]
              e ← mkAppM ``cond #[c, mkNatLit j, e]
            pure e
      acc ← mkAppM ``List.getD #[acc, idx, (← defaultFor acc)]
    -- abstract the locally-introduced binders into real `fun` binders
    -- (without this the value leaks fvars and side tactics fail)
    mkLambdaFVars fvs.toArray acc
where
  /-- Default element for a table lookup (never reached at runtime:
  indices are always in range by construction). The table has type
  `List elemTy`: a nested table defaults to `[]`, a leaf to the
  codomain's zero value. -/
  defaultFor (tab : Expr) : MetaM Expr := do
    let ty ← whnfR (← inferType tab)
    match ty with
    | .app (.const ``List _) elemTy =>
      let et ← whnfR elemTy
      match et with
      | .app (.const ``List _) innerTy => mkListLit innerTy []
      | _ =>
        match ← domOf elemTy with
        | some fd => valLit fd 0
        | none => throwError "finsearch: no table default"
    | _ => throwError "finsearch: not a table"

/-- Try to close the side goal with kernel-checked tactics.
User predicates are usually named `Prop`-valued definitions
(`miniValid`, …) which `Decidable` synthesis cannot see through, so
first unfold those (bounded fixpoint, one name at a time). Computable
constants (`Fintype.card`, `List.getD`, …) evaluate as-is under
`decide` and are left alone. -/
def closeSide : TacticM Bool := do
  -- Unfold the puzzle's own predicates so `Decidable` synthesis sees
  -- the structure. Bounded fixpoint over CURRENT-MODULE `Prop`-valued
  -- definitions only: re-scanning must never unfold library defs
  -- (e.g. `Ne`), which would damage TC-visible structure. Computable
  -- constants (`Fintype.card`, `List.getD`, …) evaluate as-is under
  -- `decide` and are left alone.
  let mut seen : List Name := []
  for _ in List.range 4 do
    let tgt ← getMainTarget
    let mut fresh : Array (TSyntax `ident) := #[]
    for n in tgt.getUsedConstants do
      if n ∈ seen then continue
      -- current module only (`none` = defined in this file)
      if (← getEnv).getModuleIdxFor? n |>.isSome then continue
      match (← getEnv).find? n with
      | some (.defnInfo di) =>
        -- `Prop`-valued only (binders opened first: `whnfR` panics on
        -- loose bvars)
        let isProp ← forallTelescope di.type fun _ resTy => do
          match ← whnfR resTy with
          | .sort _ => pure true
          | _ => pure false
        if isProp then
          seen := n :: seen
          fresh := fresh.push (mkIdent n)
      | _ => pure ()
    if fresh.isEmpty then break
    -- one name at a time: a single bad equation lemma must not block
    -- the rest
    for id in fresh do
      try
        evalTactic (← `(tactic| unfold $id))
      catch _ => pure ()
  let s1 ← `(tactic| decide)
  let s2 ← `(tactic| rfl)
  let s3 ← `(tactic| simp_all)
  for stx in ([s1, s2, s3] : List (TSyntax `tactic)) do
    let snap ← saveState
    try
      evalTactic stx
      if (← getUnsolvedGoals).isEmpty then return true
      else restoreState snap
    catch _ => restoreState snap
  pure false

/-- Run: detect finite-function goals, solve by SAT + decode + verify.
Yields on anything else (scalars belong to `Witness`). -/
def run : TacticM ProcedureOutcome := do
  let snapshot ← saveState
  let goal ← getMainTarget
  let some shape ← Lynth.Witness.classify goal
    | return .failure []
  let some (dims, cod) ← analyzeDomain shape.dom
    | return .failure []
  -- translate the opened predicate to constraints; keep decoded
  -- argument structure (pure data: arg lists per cell, no fvars escape)
  let outcome ←
    try
      let pred ← whnf shape.pred
      match pred with
      | .lam _ _ _ _ =>
        lambdaTelescope pred fun fvars body => do
          if fvars.size != 1
          then pure (none : Option (FProp × Array (Option (List Nat))))
          else
            let cells ← IO.mkRef (α := Array (Expr × Option (List Nat))) #[]
            let grid := fvars[0]!
            match ← recognizeProp cells grid body 64 with
            | none => pure none
            | some prop =>
              let cellArr ← cells.get
              -- router: over-budget estimates yield gracefully
              if !Detect.route true cellArr.size then pure none
              else pure (some (prop, cellArr.map (·.2)))
      | _ => pure none
    catch _ => pure none
  match outcome with
  | none =>
    return .failure []
  | some (prop, argTable) =>
    let nCells := argTable.size
    -- solve, decode, rebuild, verify
    try
      match runEncode prop Detect.maxSatVars with
      | none =>
        return .failure []
      | some (cnf, vmap) =>
        match Lynth.Sat.Cdcl.cdclSolve cnf Detect.solveFuel with
        | { result := some .unsat, .. } =>
          return .failure []
        | { result := none, .. } =>
          return .failure []
        | { result := some (.sat model), .. } =>
          let vals := decodeModel vmap model nCells
          let get : List Nat → Nat := fun args =>
            match (List.range nCells).find? fun a =>
              match argTable[a]! with
              | some as => as == args
              | none => false with
            | some a => vals.getD a 0
            | none => 0
          let val ← buildFunVal dims cod get
          let mvar ← getMainGoal
          let sideTy := mkApp shape.pred val
          let sidePrf ← mkFreshExprSyntheticOpaqueMVar sideTy
          let v ← shape.mkVal val sidePrf
          mvar.assign v
          replaceMainGoal [sidePrf.mvarId!]
          if ← closeSide then return .success
          else
            restoreState snapshot
            return .failure []
    catch _ =>
      restoreState snapshot
      return .failure []

end Lynth.FinSearch.Procedure
