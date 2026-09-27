import Lean
import Lynth.FinSearch.Recognize

/-!
Pattern registry for recognizing user-term shapes.

When the compiler (or any procedure) parses problem-definition terms,
it matches them against a catalog of shapes (length equations, nodup,
sublists, …). Matching by hand-rolled `if`-chains over head constants
does not scale: every new shape edits central dispatch. Instead,
shapes register as discrimination-tree patterns once, and conjuncts
retrieve candidate handlers by structure; small per-family validators
then check the non-structural side conditions (bare target, closed
literals) and extract values.

The tree is only a pre-filter (it can never manufacture a match —
validators are authoritative), so recognition stays sound no matter
what is registered. Adding a shape means registering a pattern plus a
validator; existing code is untouched (see the extension test).
-/
namespace Lynth.FinSearch.Patterns

open Lean Meta
open Lynth.FinSearch

/-- A registered shape handler: name (identity) plus family-specific
payload. `BEq` by name so re-registering a name is idempotent. -/
structure Handler (α : Type) where
  name : String
  val : α

instance : BEq (Handler α) where
  beq a b := a.name == b.name

/-- Pattern registry: discrimination-tree-indexed handlers. -/
structure Registry (α : Type) where
  tree : DiscrTree (Handler α)

/-- Empty registry. -/
def Registry.empty : Registry α :=
  ⟨DiscrTree.empty⟩

/-- Fresh wildcard slot (untyped metavariable; indexing treats it
as `star` regardless of use site). -/
def slot : MetaM Expr :=
  mkFreshExprMVar none

/-- Head applied to `nargs` fresh wildcard slots — implicit, instance,
and explicit positions alike. Count total arguments once via `#check`
(e.g. `Eq` 3, `List.length` 2, `List.sum` 4); levels default to zero
(finite-domain work is `Type`-sorted, and keys ignore levels anyway).
Pure construction, never elaborated, so no instance/type constraints
can fire. -/
def wildApp (head : Name) (nargs : Nat) : MetaM Expr := do
  let info ← match (← getEnv).find? head with
    | some info => pure info
    | none => throwError "unknown pattern head {head}"
  let mut e := mkConst head (List.replicate info.levelParams.length Level.zero)
  for _ in List.range nargs do
    e := mkApp e (← slot)
  pure e

/-- Register pattern `pat` with handler payload. -/
def Registry.register (r : Registry α) (pat : Expr) (name : String)
    (v : α) : MetaM (Registry α) := do
  pure ⟨← DiscrTree.insert r.tree pat ⟨name, v⟩⟩

/-- Retrieve handlers whose pattern structurally matches `e`. -/
def Registry.lookup (r : Registry α) (e : Expr) :
    MetaM (Array (Handler α)) :=
  DiscrTree.getMatch r.tree e

/-- Seed registry with length equations. One `Eq` pattern covers
both orientations; the validator below tries length-left then
length-right. -/
def seedLenEq : MetaM (Registry Unit) := do
  let p ← wildApp ``Eq 3
  let mut r := Registry.empty
  r ← r.register p "len-eq" ()
  pure r

/-- Validate one length-equation candidate: some side must be
`List.length` of the bare target, the other a closed literal
(either orientation). -/
private def matchLenEqAt (tgt : FVarId) (c : Expr) :
    MetaM (Option Nat) := do
  let cr ← whnfR c
  match cr.getAppFn with
  | .const ``Eq _ =>
    let args := cr.getAppArgs
    if args.size < 2 then pure none
    else
      let a := args[args.size - 2]!
      let b := args[args.size - 1]!
      match ← lenSideOf tgt a b with
      | some k => pure (some k)
      | none => lenSideOf tgt b a
  | _ => pure none
where
  /-- `lenSide` is `List.length` of bare `tgt` and `litSide` is closed. -/
  lenSideOf (tgt : FVarId) (lenSide litSide : Expr) : MetaM (Option Nat) := do
    match lenSide.getAppFn with
    | .const ``List.length _ =>
      match lenSide.getAppArgs.back? with
      | some (.fvar id) =>
        if id != tgt then pure none
        else
          match Recognize.asNumeral (← whnfR litSide) with
          | some n => pure (some n)
          | none => pure none
      | _ => pure none
    | _ => pure none

/-- Recognize `t.length = k` / `k = t.length` for bare target `t`
with closed `k`: route by shape through the registry, validate,
extract `k`. -/
def matchLenEq (reg : Registry Unit) (tgt : FVarId) (c : Expr) :
    MetaM (Option Nat) := do
  for _ in ← reg.lookup c do
    match ← matchLenEqAt tgt c with
    | some k => return some k
    | none => pure ()
  pure none

/-- Seed registry with `List.Nodup` over the target. -/
def seedNodup : MetaM (Registry Unit) := do
  let p ← wildApp ``List.Nodup 2
  let mut r := Registry.empty
  r ← r.register p "nodup" ()
  pure r

/-- Validate one nodup candidate: bare target of finite element type
(`Fin n` / `Bool`); returns the cardinality bound. -/
private def matchNodupAt (tgt : FVarId) (c : Expr) : MetaM (Option Nat) := do
  let cr ← whnfR c
  match cr.getAppFn with
  | .const ``List.Nodup _ =>
    let mut out : Option Nat := none
    for a in cr.getAppArgs do
      match a with
      | .fvar id =>
        if id != tgt then pure ()
        else
          let ty ← whnfR (← inferType a)
          match ty.getAppFn with
          | .const ``List _ =>
            let eargs := ty.getAppArgs
            if eargs.size != 1 then pure ()
            else
              let et ← whnfR eargs[0]!
              match et.getAppFn with
              | .const ``Fin _ =>
                match et.getAppArgs[0]? with
                | some nExpr =>
                  match Recognize.asNumeral (← whnfR nExpr) with
                  | some n => out := some n
                  | none => pure ()
                | none => pure ()
              | .const ``Bool _ => out := some 2
              | _ => pure ()
          | _ => pure ()
      | _ => pure ()
    pure out
  | _ => pure none

/-- Recognize `t.Nodup` for bare target `t`: cardinality bound. -/
def matchNodup (reg : Registry Unit) (tgt : FVarId) (c : Expr) :
    MetaM (Option Nat) := do
  for _ in ← reg.lookup c do
    match ← matchNodupAt tgt c with
    | some n => return some n
    | none => pure ()
  pure none

end Lynth.FinSearch.Patterns
