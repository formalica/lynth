import Lean
import Lynth.Euf.Procedure

/-!
Array theory rules: `select`/`store` internal language over `Array`.

`select(a, i)` is `GetElem.getElem`/`Array.getElem` with an `Array`
receiver; `store(a, i, v)` is `Array.set` (proof arguments ignored by
position). Two rules with core-lemma reconstruction
(`Array.getElem_set_self`, `Array.getElem_set_ne`):

- R1 (read-over-write, same index): `select(store(a,i,v),i) = v`,
  needs `i < a.size`.
- R2 (read-over-write, other index): `select(store(a,i,v),j) = select(a,j)`,
  needs `i/j < a.size` and `i ≠ j` (from a `≠`-hypothesis or `decide`).

Side conditions come from context hypotheses (up to defeq) or
kernel-reduced `decide` proofs. Every produced edge is checked by
unification against its expected equation, so the kernel re-verifies
all reconstruction. `select`-congruence itself needs no rules: it is
ordinary congruence over applications (proof-identical positions), and
dependent-proof positions fall through to later procedures.
-/
namespace Lynth.Array.Rules

open Lean Elab Tactic Meta

/-- Split a `select` into `(receiver, index)`, verifying the receiver
is an `Array`. Proof arguments are dropped by position. -/
def asSelect (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let fn := e.getAppFn
  match fn with
  | .const n _ =>
    if n != ``GetElem.getElem then return none
    let args := e.getAppArgs
    if args.size < 3 then return none
    let recv := args[args.size - 3]!
    let idx := args[args.size - 2]!
    let rty ← whnf (← inferType recv)
    match rty with
    | .app (.const ``Array _) _ => pure (some (recv, idx))
    | _ => pure none
  | _ => pure none

/-- Split a `store` into `(array, index, value)`. Proof argument
dropped by position. -/
def asStore (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let fn := e.getAppFn
  match fn with
  | .const n _ =>
    if n != ``Array.set then return none
    let args := e.getAppArgs
    if args.size < 4 then return none
    let arr := args[args.size - 4]!
    let idx := args[args.size - 3]!
    let val := args[args.size - 2]!
    let rty ← whnf (← inferType arr)
    match rty with
    | .app (.const ``Array _) _ => pure (some (arr, idx, val))
    | _ => pure none
  | _ => pure none

/-- Proposition `a < Array.size arr`, built by unification. -/
def mkBoundProp (idx arr : Expr) : MetaM Expr := do
  let size ← mkAppM ``Array.size #[arr]
  mkAppM ``LT.lt #[idx, size]

/-- Defeq test that never throws (for syntactic-leaning routing). -/
def defeqOpt (a b : Expr) : MetaM Bool := do
  try isDefEq a b catch _ => pure false

/-- Find a proof of `ty`: context scan up to defeq, then `decide` for
closed goals. Everything downstream is kernel-checked regardless. -/
def findBound (ty : Expr) : TacticM (Option Expr) := do
  for decl in ← getLCtx do
    if (decl.kind == .default) then
      try
        if ← isDefEq decl.type ty then
          return some (Expr.fvar decl.fvarId)
      catch _ => pure ()
  try
    return some (← mkDecideProof ty)
  catch _ => pure none

/-- Find a proof of `a ≠ b`: syntactic `≠`-hypothesis (either direction,
via `Ne.symm`) or `decide`. -/
def findNe (a b : Expr) : TacticM (Option Expr) := do
  for decl in ← getLCtx do
    if (decl.kind == .default) then
      match ← Lynth.Euf.Procedure.asNe decl.type with
      | some (l, r) =>
        if (← defeqOpt l a) && (← defeqOpt r b) then
          return some (Expr.fvar decl.fvarId)
        else if (← defeqOpt l b) && (← defeqOpt r a) then
          try
            return some (← mkAppM ``Ne.symm #[Expr.fvar decl.fvarId])
          catch _ => pure ()
        else pure ()
      | none => pure ()
  try
    let goal ← mkAppM ``Ne #[a, b]
    return some (← mkDecideProof goal)
  catch _ => pure none

/-- Close leftover implicit binders in a lemma application with fresh
metavariables (unified later by `isDefEq` in `checkEdge`). -/
def closePis (prf : Expr) : MetaM Expr := do
  forallTelescope (← inferType prf) fun xs _ => do
    if xs.isEmpty then pure prf
    else
      let mvs ← xs.mapM fun _ => mkFreshExprMVar none
      pure (mkAppN prf mvs)

/-- Check a built proof against its expected equation (unifies the
core lemma's implicit arguments); `none` on mismatch. Instantiates
assigned metavariables so the proof is kernel-ready. -/
def checkEdge (prf lhs rhs : Expr) : MetaM (Option Expr) := do
  try
    let want ← mkAppM ``Eq #[lhs, rhs]
    if ← isDefEq (← inferType prf) want then
      pure (some (← instantiateMVars prf))
    else pure none
  catch _ => pure none

/-- R1 + R2 rule edges over select/store subterms of `seeds`.
Capped; duplicates tolerated downstream (BFS is dup-safe). -/
def ruleEdges (seeds : List Expr) (cap : Nat := 32) :
    TacticM (Array (Expr × Expr × Expr)) := do
  let mut out := #[]
  let mut seen : Array (Expr × Expr) := #[]
  let subs := seeds.flatMap Lynth.Euf.Procedure.collectSubterms
  for s in subs do
    if cap ≤ out.size then break
    match ← asSelect s with
    | none => pure ()
    | some (recv, j) =>
      match ← asStore recv with
      | none => pure ()
      | some (arr, i, v) =>
        if ← defeqOpt i j then
          -- R1: needs `i < arr.size`
          let bt ← mkBoundProp i arr
          match ← findBound bt with
          | none => pure ()
          | some h =>
            try
              let prf0 ← mkAppM ``Array.getElem_set_self #[h]
              let prf ← closePis prf0
              match ← checkEdge prf s v with
              | some p =>
                if !(seen.any fun (a, b) => a == s && b == v) then
                  out := out.push (s, v, p)
                  seen := seen.push (s, v)
                else pure ()
              | none => pure ()
            catch _ => pure ()
        else
          -- R2: needs bounds + `i ≠ j`
          let bti ← mkBoundProp i arr
          let btj ← mkBoundProp j arr
          match (← findBound bti), (← findBound btj), (← findNe i j) with
          | some hi, some hj, some hne =>
            try
              -- `v` provided explicitly (trailing implicits throw in mkAppM)
              let prf ← mkAppOptM ``Array.getElem_set_ne
                #[none, none, none, some hi, some v, none, some hj, some hne]
              -- rebuild `select(arr, j)` reusing `s`'s implicit prefix
              -- (avoids re-inferring instances); `hj` supplies the proof
              let pre := s.getAppArgs.toList.dropLast.dropLast.dropLast
              let rhs := mkAppN s.getAppFn (pre.toArray ++ #[arr, j, hj])
              match ← checkEdge prf s rhs with
              | some p =>
                if !(seen.any fun (a, b) => a == s && b == rhs) then
                  out := out.push (s, rhs, p)
                  seen := seen.push (s, rhs)
                else pure ()
              | none => pure ()
            catch _ => pure ()
          | _, _, _ => pure ()
  pure out

end Lynth.Array.Rules
