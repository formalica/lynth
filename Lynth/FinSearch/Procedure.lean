import Lean
import Std.Tactic.BVDecide
import Batteries.Data.HashMap
import Batteries.Lean.HashSet
import Lynth.Procedure
import Lynth.Witness
import Lynth.FinSearch.Syntax
import Lynth.FinSearch.Theory
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
            let memo ← IO.mkRef (α := Memo) ∅
            let dedup ← IO.mkRef (α := Dedup) ∅
            let grid := fvars[0]!
            match ← recognizeProp memo dedup cells grid body 64 with
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
  | some (prop0, argTable) =>
    let nCells := argTable.size
    -- fold Boolean debris first (`x = true` arrives as an
    -- iff-gate pair around the real conjunction; without this the
    -- split below would cut two giant wrappers instead of the
    -- per-row pieces). Identities only, so eager behavior is
    -- unchanged (the encoder folds again anyway).
    let prop := simpProp prop0
    -- shared closing step: decoded per-cell values become a closed
    -- board value, the goal is assigned, and kernel-checked tactics
    -- verify it (soundness backstop for both eager and lazy paths)
    let finish : List Nat → TacticM ProcedureOutcome := fun vals => do
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
      if ← Lynth.Witness.closeSide then return .success
      else
        restoreState snapshot
        return .failure []
    -- branch only on grid cells' one-hot bits (aux/gate vars are
    -- implied; see `WS.branch`): collect vars whose cell has
    -- argument values in the table
    let branchOf : List ((Nat × Nat) × Nat) → Std.HashSet Nat := fun vmap =>
      let gridCells : Std.HashSet Nat :=
        (List.range nCells).foldl (fun s a =>
          match argTable[a]! with
          | some _ => s.insert a
          | none => s) ∅
      vmap.foldl (fun s ((a, _), v) =>
        if gridCells.contains a then s.insert v else s) ∅
    -- solve, decode, rebuild, verify
    try
      let (base, atoms) := Theory.splitLazy prop
      if atoms.isEmpty then
        match runEncode prop Detect.maxSatVars with
        | none =>
          return .failure []
        | some (cnf, vmap, _) =>
          match Lynth.Sat.Cdcl.cdclSolve cnf Detect.solveFuel 100 (branchOf vmap) with
          | { result := some .unsat, .. } =>
            return .failure []
          | { result := none, .. } =>
            return .failure []
          | { result := some (.sat model), .. } =>
            finish (decodeModel vmap model nCells)
      else
        -- lazy loop: big pieces stay out of the CNF; the solver
        -- proposes candidates over the small base, and each failure
        -- teaches blocking clauses over the cells that caused it
        -- (certified duplicate pairs, generalized over values).
        -- Every learned clause rules out the current candidate, so
        -- the loop always makes progress; anything learned is
        -- implied by the corresponding piece (same fixed-context
        -- evidence as greedy), and the kernel re-verifies the end.
        let atomCells : List (Nat × Nat) :=
          (atoms.toList.flatMap collectCells).eraseDups
        match runEncode base Detect.maxSatVars atomCells with
        | none =>
          return .failure []
        | some (cnf0, vmap, _) =>
          let branch := branchOf vmap
          let cardOf : Nat → Nat := fun a =>
            (vmap.filter fun ((x, _), _) => x == a).length
          let findVar : (Nat × Nat) → Option Nat := fun (a, w) =>
            (vmap.find? fun ((x, y), _) => x == a && y == w).map (·.2)
          let rec loop (fuel : Nat) (learned : List Lynth.Sat.Clause) :
              TacticM ProcedureOutcome := do
            match fuel with
            | 0 => return .failure []
            | fuel + 1 =>
              match Lynth.Sat.Cdcl.cdclSolve (cnf0 ++ learned) Detect.solveFuel 100 branch with
              | { result := some .unsat, .. } =>
                return .failure []
              | { result := none, .. } =>
                return .failure []
              | { result := some (.sat model), .. } =>
                let vals := decodeModel vmap model nCells
                let assign : Nat → Nat := fun a => vals.getD a 0
                let failed := atoms.toList.filter fun atm =>
                  evalProp atm assign (fun _ => false) == false
                match failed with
                | [] => finish vals
                | _ =>
                  let mut next := learned
                  for atm in failed do
                    let cells := ((collectCells atm).map (·.1)).eraseDups
                    match Theory.certifyPair atm cells assign cardOf with
                    | some (i, j) =>
                      let gen := Theory.generalizePair atm i j assign cardOf
                      if gen.isEmpty then
                        match findVar (i, assign i), findVar (j, assign j) with
                        | some a, some b =>
                          next := [-Int.ofNat a, -Int.ofNat b] :: next
                        | _, _ => return .failure []
                      else
                        let mut bad := false
                        for v' in gen do
                          match findVar (i, v'), findVar (j, v') with
                          | some a, some b =>
                            next := [-Int.ofNat a, -Int.ofNat b] :: next
                          | _, _ => bad := true
                        if bad then return .failure []
                    | none =>
                      let core0 := Theory.minimizeCore atm cells assign cardOf
                      let core :=
                        if core0.isEmpty then cells.map fun a => (a, assign a)
                        else core0
                      match core.mapM findVar with
                      | none => return .failure []
                      | some lits =>
                        next := (lits.map fun x => -Int.ofNat x) :: next
                  loop fuel next
          loop Theory.maxIters []
    catch _ =>
      restoreState snapshot
      return .failure []

end Lynth.FinSearch.Procedure
