import Lean
import Lynth.Procedure
import Mathlib.Data.List.Sublists

/-!
Witness synthesis for computational goals: `Subtype` refinements
(`{ n // P n }`) and existentials (`∃ x, P x`).

For `def f : { n : Nat // P n } := by lynth`, lynth must produce a
*computable* witness: enumerate candidates per domain type, assign
`Subtype.mk w ?proof`, and close the side condition with kernel-checked
tactics. The search bound keeps the procedure total; larger witnesses
fall through to the next procedure with an explanation.
-/
namespace Lynth.Witness

open Lean Elab Tactic Meta

/-- Search bound for automatic witness enumeration. -/
def searchBound : Nat := 256

/-- Diagonal pairing of two candidate lists (sum order). -/
def diagonal (xs : List Expr) (ys : List Expr) : List (Expr × Expr) :=
  let n := Nat.max xs.length ys.length
  (List.range n).flatMap fun s =>
    (List.range (s + 1)).filterMap fun i =>
      match xs[i]?, ys[s - i]? with
      | some a, some b => some (a, b)
      | _, _ => none

/-- Pair value constructor (implicits inferred from explicit args). -/
def mkProdVal (_α _β a b : Expr) : MetaM Expr := do
  mkAppM ``Prod.mk #[a, b]

/-- Integer literal expression. -/
def intLit : Int → Expr
  | Int.ofNat n => mkApp (mkConst ``Int.ofNat) (mkNatLit n)
  | Int.negSucc n => mkApp (mkConst ``Int.negSucc) (mkNatLit n)

/-- Numeric literal core (no recursion). -/
def numLitCore : Expr → Option Int
  | .lit (.natVal n) => some (n : Int)
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ =>
    some (n : Int)
  | .app (.const ``Int.ofNat _) (.lit (.natVal n)) => some (n : Int)
  | .app (.const ``Int.negSucc _) (.lit (.natVal n)) => some (-((n : Int) + 1))
  | _ => none

/-- Numeric literal, including one negation layer. -/
def numLit (e : Expr) : MetaM (Option Int) := do
  let e ← whnfR e
  match numLitCore e with
  | some k => pure (some k)
  | none =>
    match e.getAppFn with
    | .const n _ =>
      if n == ``Neg.neg then
        match e.getAppArgs.back? with
        | some a =>
          match numLitCore a with
          | some k => pure (some (-k))
          | none => pure none
        | none => pure none
      else pure none
    | _ => pure none

/-- Comparison split after whnf: `(headName, lhs, rhs)`. -/
def cmpSplit (e : Expr) : MetaM (Option (Name × Expr × Expr)) := do
  let e ← whnfR e
  match e.getAppFn with
  | .const n _ =>
    let args := e.getAppArgs
    if args.size < 2 then pure none
    else pure (some (n, args[args.size - 2]!, args[args.size - 1]!))
  | _ => pure none

/-- Bound info from a predicate: forced equality and/or lower bound
(as integers; `Nat` clamps at `0`). -/
structure Bounds where
  eq : Option Int := none
  lo : Int := 0

/-- Merge: first equality wins, lower bounds maximize. -/
def mergeB (x y : Bounds) : Bounds :=
  { eq := x.eq <|> y.eq, lo := max x.lo y.lo }

/-- Analyze a predicate body for bounds on fvar `v`.
`flip` tracks negation polarity (`¬(a ≤ b)` ⟺ `b < a`).
Fuel-bounded (formula depth). -/
def analyzeBody (body : Expr) (v : FVarId) (flip : Bool) (depth : Nat := 8) :
    MetaM Bounds := do
  match depth with
  | 0 => pure {}
  | depth + 1 =>
    let e ← whnfR body
    match e with
    | .app (.app (.const ``And _) a) b =>
      pure (mergeB (← analyzeBody a v flip depth) (← analyzeBody b v flip depth))
    | .app (.const ``Not _) a => analyzeBody a v (!flip) depth
    | _ =>
      match ← cmpSplit e with
      | none => pure {}
      | some (n, a, b) =>
        -- normalize `GT`/`GE` and polarity (flipped LE/LT swap+dualize)
        let (n0, a0, b0) :=
          if n == ``GT.gt then (``LT.lt, b, a)
          else if n == ``GE.ge then (``LE.le, b, a)
          else (n, a, b)
        let (nn, aa, bb) :=
          if flip then
            if n0 == ``LE.le then (``LT.lt, b0, a0)
            else if n0 == ``LT.lt then (``LE.le, b0, a0)
            else (n0, a0, b0) -- flipped `Eq` is `Ne`: no bound info
          else (n0, a0, b0)
        let isV : Expr → Bool :=
          let fv := Expr.fvar v
          (· == fv)
        if nn == ``Eq then
          if isV aa then
            match ← numLit bb with
            | some k => pure { eq := some k }
            | none => pure {}
          else if isV bb then
            match ← numLit aa with
            | some k => pure { eq := some k }
            | none => pure {}
          else pure {}
        else if nn == ``LE.le then
          -- `k ≤ v` lower-bounds `v`
          if !(isV aa) && isV bb then
            match ← numLit aa with
            | some k => pure { lo := k }
            | none => pure {}
          else pure {}
        else if nn == ``LT.lt then
          -- `k < v` lower-bounds `v` at `k + 1`
          if !(isV aa) && isV bb then
            match ← numLit aa with
            | some k => pure { lo := k + 1 }
            | none => pure {}
          else pure {}
        else pure {}

/-- Extract `(start, forced)` from a predicate by opening its binder.
Falls back to `(0, none)` for unrecognized shapes. -/
def boundInfo (pred : Expr) : MetaM (Int × Option Int) := do
  let p ← whnf pred
  match p with
  | .lam _ _ _ _ =>
    lambdaTelescope p fun fvars body => do
      if fvars.size != 1 then pure (0, none)
      else match fvars[0]! with
        | .fvar v =>
          let bi ← analyzeBody body v false
          pure (bi.lo, bi.eq)
        | _ => pure (0, none)
  | _ => pure (0, none)

/-- All length-`n` tables over a codomain pool (function graphs in
domain order). -/
def allTables : List Expr → Nat → List (List Expr)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | p, n + 1 => (allTables p n).flatMap fun rest => p.map fun v => v :: rest

/-- Table function `fun i => tab.getD i.val dflt` over a `Fin` domain;
kernel-computable, no proofs required. -/
def mkTableFun (dom cod : Expr) (tab : List Expr) (dflt : Expr) : MetaM Expr := do
  let tabLit ← mkListLit cod tab
  withLocalDeclD `i dom fun i => do
    let idx ← mkAppM ``Fin.val #[i]
    let body ← mkAppM ``List.getD #[tabLit, idx, dflt]
    mkLambdaFVars #[i] body

/-- Single-constructor structure fields (explicit, closed): returns
`(ctor, fields)`. Bails on multi-constructor, dependent, or open field
types (sound under-approximation for small closed aggregates). -/
def structFields (dom : Expr) : MetaM (Option (Name × Array Expr)) := do
  let dom ← whnfR dom
  match dom.getAppFn with
  | .const head _ =>
    match (← getEnv).find? head with
    | some (.inductInfo info) =>
      if info.numCtors != 1 then pure none
      else
        let ctor := info.ctors.head!
        let cty ← inferType (← mkConstWithFreshMVarLevels ctor)
        forallTelescope cty fun xs _ => do
          let mut fields := #[]
          for x in xs do
            let decl ← x.fvarId!.getDecl
            if decl.binderInfo.isExplicit then
              let fty ← inferType x
              if fty.hasFVar then return none
              fields := fields.push fty
          pure (some (ctor, fields))
    | _ => pure none
  | _ => pure none

/-- Candidate witnesses with nesting depth (products recurse).
`start` shifts the search window (from bound analysis); `0` by default. -/
def candidatesAux (dom : Expr) (bound depth : Nat) (start : Int := 0) :
    MetaM (List Expr) := do
  let dom ← whnfR dom
  if dom.isConstOf ``Nat then
    let s := start.toNat
    pure ((List.range bound).map fun w => mkNatLit (w + s))
  else if dom.isConstOf ``Int then
    -- interleave start, start+1, start-1, start+2, start-2, …
    pure (((List.range bound).map fun i =>
      [start + Int.ofNat i, start - Int.ofNat i - 1]).flatten |>.take bound |>.map intLit)
  else if dom.isConstOf ``Bool then
    pure [mkConst ``Bool.true, mkConst ``Bool.false]
  else if dom.isAppOf ``Fin then
    -- finite domain: complete enumeration with kernel-checked bounds
    let args := dom.getAppArgs
    if args.size != 1 then pure []
    else
      let a0 ← whnfR args[0]!
      let n? : Option Nat := match a0 with
        | .lit (.natVal n) => some n
        | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ =>
          some n
        | _ => none
      match n? with
      | none => pure []
      | some n =>
        let arr ← (List.range n).toArray.filterMapM fun i => do
          try
            let iLit := mkNatLit i
            let hlt ← mkAppM ``LT.lt #[iLit, mkNatLit n]
            let pf ← mkDecideProof hlt
            some <$> mkAppM ``Fin.mk #[iLit, pf]
          catch _ => pure none
        pure arr.toList
  else if dom.isAppOf ``Prod then
    match depth with
    | 0 => pure []
    | depth + 1 =>
      let args := dom.getAppArgs
      if args.size != 2 then pure []
      else
        let ca ← candidatesAux args[0]! 16 depth
        let cb ← candidatesAux args[1]! 16 depth
        -- full product when small (positional pairing beats diagonal
        -- for coupled components); diagonal prefix otherwise
        let total := ca.length * cb.length
        if total == 0 then pure []
        else if total ≤ 60000 then
          (ca.flatMap fun a => cb.map fun b => (a, b)).mapM fun (a, b) =>
            mkProdVal args[0]! args[1]! a b
        else
          ((diagonal ca cb).take 512).mapM fun (a, b) =>
            mkProdVal args[0]! args[1]! a b
  else if let some (ctor, fields) ← structFields dom then
    match depth with
    | 0 => pure []
    | depth + 1 =>
      let mut combos : List (List Expr) := [[]]
      for fty in fields do
        let cf ← candidatesAux fty 4096 depth
        if cf.isEmpty then
          combos := []
          break
        -- NOTE: append, not prepend: field order must match the
        -- constructor's explicit arguments (prepending reverses fields;
        -- harmless for value tables, fatal for field assignment).
        combos := combos.flatMap fun rest => cf.map fun v => rest ++ [v]
        if 4096 < combos.length then
          combos := []
          break
      combos.mapM fun vs => do
        pure (mkAppN (← mkConstWithFreshMVarLevels ctor) vs.toArray)
  else if dom.isForall then
    -- finite functions as getD-table lambdas (`fun i => tab.getD i.val d`),
    -- for `Fin n` domains with finite codomains, capped total tables.
    -- Covers tiny labelings (e.g. `Fin 6 → Bool`); large spaces yield.
    match depth with
    | 0 => pure []
    | depth + 1 =>
      match dom with
      | .forallE _ d b _ =>
        if b.hasLooseBVars then pure []
        else
          let dR ← whnfR d
          match dR.getAppFn with
          | .const ``Fin _ =>
            let dc ← candidatesAux d 100000 depth
            if dc.isEmpty || 64 < dc.length then pure []
            else do
              let cc ← candidatesAux b 100000 depth
              match cc with
              | [] => pure []
              | dflt :: _ =>
                -- binary-function tables (e.g. `Fin 4 → Fin 4 → Bool`)
                -- reach 2^16; kernel `decide`-eval per table keeps this
                -- feasible, and misses fail fast by count
                let total := cc.length ^ dc.length
                if 100000 < total then pure []
                else
                  (allTables cc dc.length).mapM fun tab =>
                    mkTableFun d b tab dflt
          | _ => pure []
      | _ => pure []
  else pure []

/-- Candidate witnesses for a domain type, directed by bound analysis:
forced equalities short-circuit; lower bounds shift the window. -/
def candidates (dom pred : Expr) (bound : Nat) : MetaM (List Expr) := do
  let (start, forced) ← boundInfo pred
  let domR ← whnfR dom
  match forced with
  | some k =>
    if domR.isConstOf ``Nat then
      pure (if k < 0 then [] else [mkNatLit k.toNat])
    else if domR.isConstOf ``Int then pure [intLit k]
    else candidatesAux dom bound 4 0
  | none => candidatesAux dom bound 4 start

/-- Value constructor for `Subtype` goals (explicit implicits). -/
def mkSubtypeVal (dom pred w sidePrf : Expr) : MetaM Expr := do
  let u ← getLevel dom
  pure (mkAppN (mkConst ``Subtype.mk [u]) #[dom, pred, w, sidePrf])

/-- Value constructor for `Exists` goals (explicit implicits). -/
def mkExistsVal (dom pred w sidePrf : Expr) : MetaM Expr := do
  let u ← getLevel dom
  pure (mkAppN (mkConst ``Exists.intro [u]) #[dom, pred, w, sidePrf])

/-- Goal shape for witness synthesis: `Subtype` or `Exists` with
domain, predicate, and value constructor. -/
structure WitShape where
  dom : Expr
  pred : Expr
  mkVal : Expr → Expr → MetaM Expr

/-- Classify the goal; `none` ⟹ not a synthesis goal. -/
def classify (goal : Expr) : MetaM (Option WitShape) := do
  let ty ← whnf goal
  match ty.getAppFn with
  | .const ``Subtype _ =>
    let args := ty.getAppArgs
    if args.size != 2 then return none
    let dom := args[0]!
    let pred := args[1]!
    pure (some { dom := dom, pred := pred, mkVal := mkSubtypeVal dom pred })
  | .const ``Exists _ =>
    let args := ty.getAppArgs
    if args.size != 2 then return none
    let dom := args[0]!
    let pred := args[1]!
    pure (some { dom := dom, pred := pred, mkVal := mkExistsVal dom pred })
  | _ => pure none

/-- Unfold the puzzle's own predicates once (see `closeSide`): bounded
fixpoint over current-module `Prop`-valued definitions. Call once per
goal, not per candidate — the unfolding is candidate-independent. -/
def unfoldSideDefs : TacticM (Array Name) := do
  -- Unfold the puzzle's own predicates so `Decidable` synthesis sees
  -- the structure. Bounded fixpoint over CURRENT-MODULE `Prop`-valued
  -- definitions only: re-scanning must never unfold library defs
  -- (e.g. `Ne`), which would damage TC-visible structure. Computable
  -- constants (`Fintype.card`, `List.getD`, …) evaluate as-is under
  -- `decide` and are left alone.
  -- Returns every applied name so candidate loops can re-apply them
  -- without re-running discovery.
  let mut seen : List Name := []
  let mut applied : Array Name := #[]
  for _ in List.range 4 do
    let tgt ← getMainTarget
    let mut fresh : Array (TSyntax `ident) := #[]
    let mut freshNames : Array Name := #[]
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
          freshNames := freshNames.push n
      | _ => pure ()
    if fresh.isEmpty then break
    -- one name at a time: a single bad equation lemma must not block
    -- the rest
    for id in fresh do
      try
        evalTactic (← `(tactic| unfold $id))
      catch _ => pure ()
    applied := applied ++ freshNames
  pure applied

/-- Re-apply recorded unfold names (no discovery): the per-candidate
cheap path after one `unfoldSideDefs` discovery pass. -/
def applySideUnfolds (ns : Array Name) : TacticM Unit := do
  for n in ns do
    try
      evalTactic (← `(tactic| unfold $(mkIdent n)))
    catch _ => pure ()

def closeSideNoUnfold : TacticM Bool := do
  let s1 ← `(tactic| decide)
  let s2 ← `(tactic| rfl)
  let s3 ← `(tactic| simp_all)
  -- Fast reject: if the goal is decidable, `rfl`/`decide` settle it
  -- (`decide` evaluating to `false` means no other tactic can help —
  -- skip the expensive `simp_all`, which otherwise burns full
  -- heartbeats on every wrong candidate). `simp_all` runs only for
  -- undecidable goals it might normalize into decidable shape.
  let target ← getMainTarget
  let decidable ← try
      let _ ← synthInstance (mkApp (mkConst ``Decidable []) target)
      pure true
    catch _ => pure false
  if decidable then
    for stx in ([s2, s1] : List (TSyntax `tactic)) do
      let snap ← saveState
      try
        evalTactic stx
        if (← getUnsolvedGoals).isEmpty then return true
        else restoreState snap
      catch _ => restoreState snap
    return false
  -- optimality fallback BEFORE `simp_all`: rewrite `Sublist` to
  -- `∈ sublists` and decide (proves `∀ m, m.Sublist ref → …` over
  -- finite enumerations for minimality side-conditions). `simp_all`
  -- would rewrite `Sublist` into undecidable forms first.
  -- NOTE: `List.mem_sublists` needs the `Mathlib.Data.List.Sublists`
  -- import above, else the quotation resolves nowhere and `simp`
  -- fails silently here.
  do
    let snap ← saveState
    try
      evalTactic (← `(tactic| simp only [←List.mem_sublists]))
      evalTactic s1
      if (← getUnsolvedGoals).isEmpty then return true
      else restoreState snap
    catch _ => restoreState snap
  for stx in ([s2, s3] : List (TSyntax `tactic)) do
    let snap ← saveState
    try
      evalTactic stx
      if (← getUnsolvedGoals).isEmpty then return true
      else restoreState snap
    catch _ => restoreState snap
  -- `simp_all` may have normalized into decidable shape: retry `decide`.
  let snap ← saveState
  try
    evalTactic s1
    if (← getUnsolvedGoals).isEmpty then return true
    else restoreState snap
  catch _ => restoreState snap
  pure false

def closeSide : TacticM Bool := do
  let _ ← unfoldSideDefs
  closeSideNoUnfold

/-- Try every candidate: build the value, close the side condition
(unfolding + kernel-checked tactics via `closeSide`, `omega` fallback). -/
def run (bound : Nat := searchBound) : TacticM ProcedureOutcome := do
  let goal ← getMainTarget
  let some shape ← classify goal | return .failure []
  let cands ← candidates shape.dom shape.pred bound
  if cands.isEmpty then return .failure []
  let others ← getUnsolvedGoals
  -- unfold discovery once (candidate-independent); per candidate only
  -- re-apply the recorded names, not the full scan
  let snap0 ← saveState
  let uns ← unfoldSideDefs
  -- fast path (see `tryVals`): `DecidablePred` once, kernel `decide`
  -- eval per candidate; full close only on hits or when undecidable
  let predU ← do
    let goal ← getMainTarget
    match ← classify goal with
    | none => whnf shape.pred
    | some shape' => whnf shape'.pred
  let dpred? : Option Expr ← try
      pure (← synthInstance (← mkAppM ``DecidablePred #[predU]))
    catch _ => pure none
  for w in cands do
    let hit ← match dpred? with
      | none => pure true
      | some dpred =>
        let instW := mkApp dpred w
        let d := mkApp (mkApp (mkConst ``Decidable.decide []) (mkApp predU w)) instW
        match ← whnf d with
        | .const ``Bool.true _ => pure true
        | _ => pure false
    unless !hit do
      let snapshot ← saveState
      try
        let mvar ← getMainGoal
        let sideTy := mkApp shape.pred w
        let sidePrf ← mkFreshExprSyntheticOpaqueMVar sideTy
        -- explicit implicits from the goal's own `dom`/`pred`: no inference.
        let val ← shape.mkVal w sidePrf
        mvar.assign val
        replaceMainGoal (sidePrf.mvarId! :: others.filter (· != mvar))
        applySideUnfolds uns
        let mut closed ← closeSideNoUnfold
        unless closed do
          let snap2 ← saveState
          try
            evalTactic (← `(tactic| omega))
            if (← getUnsolvedGoals).isEmpty then closed := true
            else restoreState snap2
          catch _ =>
            restoreState snap2
        if closed then return .success
        restoreState snapshot
      catch _ =>
        restoreState snapshot
  restoreState snap0
  return .failure []

end Lynth.Witness
