import Lean
import Lynth.Procedure
import Lynth.Witness
import Lynth.FinSearch.Detect
import Lynth.FinSearch.Recognize
import Lynth.FinSearch.Procedure

/-!
List-bound inference for synthesis over `List Nat` goals
(`{ l : List Nat // P l }`).

The `FinSearch` core only handles finite domains, so an unbounded
list goal needs its length and element values inferred first. Every
inference below is asked of every recognized call through one
dispatcher (`inferenceRow`): length lower/upper bounds for
`List`-valued calls, element lower/upper bounds and value pools for
`Nat`-element lists, and target exact/lower/upper bounds answering
what a call equated to a closed value forces upon a mentioned
target list. Each Lean function the pipeline handles owns exactly
one table row; unknown heads answer `none` everywhere, so shared
code never names a single function and supporting a new function
means adding a row. Recursive questions go through the `Queries`
bundle (fuel-guarded, always on strict subterms). A wrong inference
can only make the search miss (yield), never prove a falsehood:
every candidate is kernel-checked by `decide` before it closes
anything.
-/
namespace Lynth.FinSearch.ListInfer

open Lean Elab Tactic Meta
open Lynth.FinSearch

/-- Recursive query bundle: the uniform questions, asked of any
subterm with fuel. Rows receive it explicitly so no mutual block
is needed. -/
structure Queries where
  lenLo : Expr → Nat → MetaM (Option Nat)
  lenHi : Expr → Nat → MetaM (Option Nat)
  elemLo : Expr → Nat → MetaM (Option Nat)
  elemHi : Expr → Nat → MetaM (Option Nat)
  pool : Expr → Nat → MetaM (Option (List Nat))

/-- One row of the inference dispatch: how a single Lean call node
answers the uniform bound questions. -/
structure InferRow where
  inferLengthLower : Queries → Array Expr → Nat → MetaM (Option Nat)
  inferLengthUpper : Queries → Array Expr → Nat → MetaM (Option Nat)
  inferElemLower : Queries → Array Expr → Nat → MetaM (Option Nat)
  inferElemUpper : Queries → Array Expr → Nat → MetaM (Option Nat)
  inferElemPool : Queries → Array Expr → Nat → MetaM (Option (List Nat))
  inferTargetExact : FVarId → Array Expr → Expr → MetaM (Option Nat)
  inferTargetLower : FVarId → Array Expr → Expr → MetaM (Option Nat)
  inferTargetUpper : FVarId → Array Expr → Expr → MetaM (Option Nat)

/-- Numeric literal (elaborated `OfNat` included). -/
private def natLitOf : Expr → Option Nat :=
  Lynth.FinSearch.Recognize.asNumeral

/-- Explicit list literal spine. -/
private def listLitOf : Expr → Option (List Expr) :=
  Lynth.FinSearch.Recognize.asListLit

/-- Does `e` mention free variable `tgt`? -/
private def mentionsTgt (e : Expr) (tgt : FVarId) : Bool :=
  (e.find? fun | .fvar id => id == tgt | _ => false).isSome

/-- Is `e` exactly the bare target variable? Relation rules only
fire on the bare target: nested occurrences (e.g. under another
call) carry no direct length equation. -/
private def isBareTgt (tgt : FVarId) : Expr → Bool
  | .fvar id => id == tgt
  | _ => false

/-- Last List-typed trailing argument (robust to instance-implicit
arities): the list operand of a call, if any. -/

private def listArgOf (args : Array Expr) : MetaM (Option Expr) := do
  let mut out : Option Expr := none
  for a in args do
    let ty ← try pure (← whnf (← inferType a)) catch _ => continue
    match ty.getAppFn with
    | .const ``List _ => out := some a
    | _ => pure ()
  pure out

/-- Unique Nat literal among arguments, if exactly one. -/
private def uniqNatLit (args : Array Expr) : Option Nat :=
  match args.toList.filterMap natLitOf with
  | [k] => some k
  | _ => none

/-- The unknown row: every question unanswered. Default for
unhandled heads, so the dispatch stays total. -/
def unknownRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure none,
    inferLengthUpper := fun _ _ _ => pure none,
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun _ _ _ => pure none,
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none }

def nilRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure (some 0),
    inferLengthUpper := fun _ _ _ => pure (some 0),
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun _ _ _ => pure (some []),
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none }

def consRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure (some 1),
    inferLengthUpper := fun _ _ _ => pure none,
    inferElemLower := fun _ args _ => do
      if args.size < 2 then pure none
      else pure (natLitOf args[args.size - 2]!),
    inferElemUpper := fun _ args _ => do
      if args.size < 2 then pure none
      else pure (natLitOf args[args.size - 2]!),
    inferElemPool := fun q args fuel => do
      if fuel == 0 || args.size < 2 then pure none
      else
        let h := args[args.size - 2]!
        let t := args[args.size - 1]!
        match natLitOf h, ← q.pool t (fuel - 1) with
        | some v, some vs => pure (some (v :: vs))
        | _, some vs => pure (some vs)
        | some v, none => pure (some [v])
        | _, _ => pure none,
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none }

def appendRow : InferRow :=
  { inferLengthLower := fun q args fuel => do
      if fuel == 0 || args.size < 2 then pure none
      else do
        let a ← q.lenLo args[args.size - 2]! (fuel - 1)
        let b ← q.lenLo args[args.size - 1]! (fuel - 1)
        pure (a.bind fun x => b.map fun y => x + y),
    inferLengthUpper := fun q args fuel => do
      if fuel == 0 || args.size < 2 then pure none
      else do
        let a ← q.lenHi args[args.size - 2]! (fuel - 1)
        let b ← q.lenHi args[args.size - 1]! (fuel - 1)
        pure (a.bind fun x => b.map fun y => x + y),
    inferElemLower := fun q args fuel => do
      if fuel == 0 || args.size < 2 then pure none
      else do
        let a ← q.elemLo args[args.size - 2]! (fuel - 1)
        let b ← q.elemLo args[args.size - 1]! (fuel - 1)
        pure (a.bind fun x => b.map fun y => min x y),
    inferElemUpper := fun q args fuel => do
      if fuel == 0 || args.size < 2 then pure none
      else do
        let a ← q.elemHi args[args.size - 2]! (fuel - 1)
        let b ← q.elemHi args[args.size - 1]! (fuel - 1)
        pure (a.bind fun x => b.map fun y => max x y),
    inferElemPool := fun q args fuel => do
      if fuel == 0 || args.size < 2 then pure none
      else do
        let a ← q.pool args[args.size - 2]! (fuel - 1)
        let b ← q.pool args[args.size - 1]! (fuel - 1)
        match a, b with
        | some x, some y => pure (some (x ++ y))
        | some x, none => pure (some x)
        | none, some y => pure (some y)
        | _, _ => pure none,
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none }

def reverseRow : InferRow :=
  { inferLengthLower := fun q args fuel => do
      if fuel == 0 || args.isEmpty then pure none
      else q.lenLo args.back! (fuel - 1),
    inferLengthUpper := fun q args fuel => do
      if fuel == 0 || args.isEmpty then pure none
      else q.lenHi args.back! (fuel - 1),
    inferElemLower := fun q args fuel => do
      if fuel == 0 || args.isEmpty then pure none
      else q.elemLo args.back! (fuel - 1),
    inferElemUpper := fun q args fuel => do
      if fuel == 0 || args.isEmpty then pure none
      else q.elemHi args.back! (fuel - 1),
    inferElemPool := fun q args fuel => do
      if fuel == 0 || args.isEmpty then pure none
      else q.pool args.back! (fuel - 1),
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none }

def rangeRow : InferRow :=
  { inferLengthLower := fun _ args _ => pure (uniqNatLit args),
    inferLengthUpper := fun _ args _ => pure (uniqNatLit args),
    inferElemLower := fun _ _ _ => pure (some 0),
    inferElemUpper := fun _ args _ => do
      pure (uniqNatLit args |>.bind fun n => if n == 0 then none else some (n - 1)),
    inferElemPool := fun _ args _ => do
      pure (uniqNatLit args |>.map List.range),
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none }

def replicateRow : InferRow :=
  { inferLengthLower := fun _ args _ => pure (uniqNatLit args),
    inferLengthUpper := fun _ args _ => pure (uniqNatLit args),
    inferElemLower := fun _ args _ => do
      pure (if args.isEmpty then none else natLitOf args.back!),
    inferElemUpper := fun _ args _ => do
      pure (if args.isEmpty then none else natLitOf args.back!),
    inferElemPool := fun _ args _ => do
      pure (if args.isEmpty then none
        else (natLitOf args.back!).map fun v => [v]),
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none }

def takeRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure none,
    inferLengthUpper := fun _ args _ => pure (uniqNatLit args),
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.pool l (fuel - 1),
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun tgt args closed => do
      match listLitOf closed with
      | some elts =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some elts.length else none)
        | none => pure none
      | none => pure none,
    inferTargetUpper := fun _ _ _ => pure none }

def dropRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure none,
    inferLengthUpper := fun q args fuel => do
      if fuel == 0 then pure none
      else do
        let some l ← listArgOf args | pure none
        let n := uniqNatLit args |>.getD 0
        match ← q.lenHi l (fuel - 1) with
        | some h => pure (some (h - n))
        | none => pure none,
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.pool l (fuel - 1),
    inferTargetExact := fun tgt args closed => do
      match listLitOf closed, uniqNatLit args with
      | some elts, some n =>
        match ← listArgOf args with
        | some l =>
          if isBareTgt tgt l && elts.length > 0 then
            pure (some (n + elts.length))
          else pure none
        | none => pure none
      | _, _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun tgt args closed => do
      match listLitOf closed, uniqNatLit args with
      | some [], some n =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some n else none)
        | none => pure none
      | _, _ => pure none }

def mapRow : InferRow :=
  { inferLengthLower := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.lenLo l (fuel - 1),
    inferLengthUpper := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.lenHi l (fuel - 1),
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun _ _ _ => pure none,
    inferTargetExact := fun tgt args closed => do
      match listLitOf closed with
      | some elts =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some elts.length else none)
        | none => pure none
      | none => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none }

def filterRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure none,
    inferLengthUpper := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.lenHi l (fuel - 1),
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.pool l (fuel - 1),
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun tgt args closed => do
      match listLitOf closed with
      | some elts =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some elts.length else none)
        | none => pure none
      | none => pure none,
    inferTargetUpper := fun _ _ _ => pure none }

def lengthRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure none,
    inferLengthUpper := fun _ _ _ => pure none,
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun _ _ _ => pure none,
    inferTargetExact := fun tgt args closed => do
      match natLitOf closed with
      | some k =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some k else none)
        | none => pure none
      | none => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none }

def sumRow : InferRow := unknownRow

def countRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure none,
    inferLengthUpper := fun _ _ _ => pure none,
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun _ _ _ => pure none,
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun tgt args closed => do
      match natLitOf closed with
      | some k =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some k else none)
        | none => pure none
      | none => pure none,
    inferTargetUpper := fun _ _ _ => pure none }

/-- The single dispatcher: every handled Lean function maps to its
inference row. Unknown heads get `unknownRow`. -/
def inferenceRow : Name → InferRow
  | n =>
    if n == ``List.nil then nilRow
    else if n == ``List.cons then consRow
    else if n == ``List.append then appendRow
    else if n == ``HAppend.hAppend then appendRow
    else if n == ``List.reverse then reverseRow
    else if n == ``List.range then rangeRow
    else if n == ``List.replicate then replicateRow
    else if n == ``List.take then takeRow
    else if n == ``List.drop then dropRow
    else if n == ``List.map then mapRow
    else if n == ``List.filter then filterRow
    else if n == ``List.length then lengthRow
    else if n == ``List.sum then sumRow
    else if n == ``List.count then countRow
    else unknownRow

/-- Empty bundle (all unknown): `Inhabited` witness so the
recursive bundle below compiles; never used for real queries. -/
instance : Inhabited Queries where
  default :=
    { lenLo := fun _ _ => pure none,
      lenHi := fun _ _ => pure none,
      elemLo := fun _ _ => pure none,
      elemHi := fun _ _ => pure none,
      pool := fun _ _ => pure none }

/-- The recursive query bundle, parameterized by the row lookup
so no mutual block is needed: each question dispatches on the
head and recurses on strict subterms with shrinking fuel. -/
partial def queriesFrom (rowOf : Name → InferRow) : Queries :=
  { lenLo := fun e fuel =>
      if fuel == 0 then pure none
      else match e.getAppFn with
        | .const fn _ =>
          (rowOf fn).inferLengthLower (queriesFrom rowOf) e.getAppArgs (fuel - 1)
        | _ => pure none,
    lenHi := fun e fuel =>
      if fuel == 0 then pure none
      else match e.getAppFn with
        | .const fn _ =>
          (rowOf fn).inferLengthUpper (queriesFrom rowOf) e.getAppArgs (fuel - 1)
        | _ => pure none,
    elemLo := fun e fuel =>
      if fuel == 0 then pure none
      else match e.getAppFn with
        | .const fn _ =>
          (rowOf fn).inferElemLower (queriesFrom rowOf) e.getAppArgs (fuel - 1)
        | _ => pure none,
    elemHi := fun e fuel =>
      if fuel == 0 then pure none
      else match e.getAppFn with
        | .const fn _ =>
          (rowOf fn).inferElemUpper (queriesFrom rowOf) e.getAppArgs (fuel - 1)
        | _ => pure none,
    pool := fun e fuel =>
      if fuel == 0 then pure none
      else match e.getAppFn with
        | .const fn _ =>
          (rowOf fn).inferElemPool (queriesFrom rowOf) e.getAppArgs (fuel - 1)
        | _ => pure none }

/-- The bundle handed to rows: recursive questions over
`inferenceRow`. -/
def queries : Queries := queriesFrom inferenceRow

/-- Collected bounds on the target list. -/
structure Bounds where
  lenLo : Nat := 0
  lenHi : Option Nat := none
  pool : List Nat := []

/-- Flatten top-level `And` conjunctions. -/
def splitConj : Expr → List Expr
  | .app (.app (.const ``And _) a) b => splitConj a ++ splitConj b
  | e => [e]

/-- Process one `Eq` conjunct: orient target side vs closed side,
ask the target relation methods, harvest literal pools. Anything
unrecognized contributes nothing (the kernel still enforces it
when candidates are checked). -/
def processEq (tgt : FVarId) (a b : Expr) (st : Bounds) : MetaM Bounds := do
  let oriented : Option (Expr × Expr) :=
    if mentionsTgt a tgt && !mentionsTgt b tgt then some (a, b)
    else if mentionsTgt b tgt && !mentionsTgt a tgt then some (b, a)
    else none
  match oriented with
  | none => pure st
  | some (tSide, cSide) =>
    if cSide.hasFVar then pure st
    else
      let mut st := st
      -- pool harvesting: closed list literals contribute elements
      match listLitOf cSide with
      | some elts =>
        let vs := elts.filterMap natLitOf
        if vs.length == elts.length then
          st := { st with pool := st.pool ++ vs }
        else pure ()
      | none => pure ()
      -- length reasoning by target-side shape
      match tSide with
      | .fvar id =>
        if id == tgt then
          match listLitOf cSide with
          | some elts =>
            let lo := max st.lenLo elts.length
            let hi := min (st.lenHi.getD elts.length) elts.length
            st := { st with lenLo := lo, lenHi := some hi, pool := st.pool }
          | none => pure ()
        else pure ()
      | _ =>
        match tSide.getAppFn with
        | .const fn _ =>
          let row := inferenceRow fn
          let args := tSide.getAppArgs
          match ← row.inferTargetExact tgt args cSide with
          | some n =>
            let lo := max st.lenLo n
            let hi := min (st.lenHi.getD n) n
            st := { st with lenLo := lo, lenHi := some hi }
          | none => pure ()
          match ← row.inferTargetLower tgt args cSide with
          | some n => st := { st with lenLo := max st.lenLo n }
          | none => pure ()
          match ← row.inferTargetUpper tgt args cSide with
          | some n =>
            let hi := min (st.lenHi.getD n) n
            st := { st with lenHi := some hi }
          | none => pure ()
          -- per-call pool rows supplement literal harvesting
          match ← row.inferElemPool queries args 8 with
          | some vs => st := { st with pool := st.pool ++ vs }
          | none => pure ()
        | _ => pure ()
      pure st

/-- Intersect bounds across all conjunctions to a fixpoint
(bounds only tighten, pools only grow; fuel caps the rounds). -/
def inferBounds (tgt : FVarId) (conjs : List Expr) : MetaM Bounds := do
  let mut st : Bounds := {}
  for _ in List.range 12 do
    let mut st' := st
    for c in conjs do
      let cr ← whnfR c
      match cr.getAppFn with
      | .const ``Eq _ =>
        let args := cr.getAppArgs
        if args.size != 3 then pure ()
        else st' ← processEq tgt args[args.size - 2]! args[args.size - 1]! st'
      | _ => pure ()
    st := st'
  pure st

/-- All length-`n` lists over `pool`, lexicographic. -/
def allLists : List Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | p, n + 1 => (allLists p n).flatMap fun rest => p.map fun v => v :: rest

/-- List synthesis over `List Nat`: infer exact length plus a finite
value pool, enumerate, and kernel-check each candidate. Yields on
anything else (other domains belong to earlier procedures). -/
def run : TacticM ProcedureOutcome := do
  let goal ← getMainTarget
  let some shape ← Lynth.Witness.classify goal
    | return .failure []
  -- only `List Nat` domains reach the inference fixpoint
  let domR ← whnfR shape.dom
  match domR.getAppFn with
  | .const ``List _ =>
    let dargs := domR.getAppArgs
    if dargs.size != 1 then return .failure []
    else
      let et ← whnfR dargs[0]!
      match et with
      | .const ``Nat _ =>
        let pred ← whnf shape.pred
        match pred with
        | .lam _ _ _ _ =>
          lambdaTelescope pred fun fvars body => do
            if fvars.size != 1 then return .failure []
            else
              -- the body may apply a user definition (`tdValid l`);
              -- unfold once so conjunctions/equations are visible
              let body ← whnf body
              match fvars[0]! with
              | .fvar tgt =>
                let fty ← whnfR (← inferType fvars[0]!)
                match fty.getAppFn with
                | .const ``List _ =>
                  let st ← inferBounds tgt (splitConj body)
                  match st.lenHi with
                  | none => return .failure []
                  | some n =>
                    if st.lenLo != n then return .failure []
                    else
                      let pool := st.pool.eraseDups
                      if pool.isEmpty then return .failure []
                      else if 12 < pool.length then return .failure []
                      else if 8 < n then return .failure []
                      else
                        let total := pool.length ^ n
                        if total == 0 || Detect.maxListCand < total then
                          return .failure []
                        else
                          let cands := allLists pool n
                          let others ← getUnsolvedGoals
                          for w in cands do
                            let snapshot ← saveState
                            try
                              let wv ← mkListLit (mkConst ``Nat []) (w.map mkNatLit)
                              let mvar ← getMainGoal
                              let sideTy := mkApp shape.pred wv
                              let sidePrf ← mkFreshExprSyntheticOpaqueMVar sideTy
                              let val ← shape.mkVal wv sidePrf
                              mvar.assign val
                              replaceMainGoal (sidePrf.mvarId! :: others.filter (· != mvar))
                              -- shared kernel-checked closer: unfolds the
                              -- goal's own predicates, then decides
                              if ← Lynth.FinSearch.Procedure.closeSide then
                                return .success
                              restoreState snapshot
                            catch _ =>
                              restoreState snapshot
                          return .failure []
                | _ => return .failure []
              | _ => return .failure []
        | _ => pure (.failure [])
      | _ => return .failure []
  | _ => return .failure []

end Lynth.FinSearch.ListInfer
