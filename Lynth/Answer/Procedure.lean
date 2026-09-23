import Lean
import Lynth.Procedure
import Lynth.Egraph.Procedure
import Lynth.Euf.Procedure
import Lynth.FinSearch.Procedure
import Lynth.FinSearch.ListInfer
import Lynth.Witness

/-!
Answer-goal procedure: split `Sum`/`PSum` goals (notably the FinDomain
`Answer` shape `{ w // p w } ⊕' (∀ x, ¬ p x)`) into refutation and
witness branches.

- Right branch: `refine inr`; first finite `decide` refutation on the
  `∀`-goal (under a cardinality guard), otherwise `intros` and egraph
  split-free refutation.
- Left branch: `refine inl`, then the synthesis sub-pipeline
  (`finsearch`, `listsynth`, `witness`) on the `Subtype` goal.

Every failed attempt restores the snapshot, so falling through leaves
the goal untouched for later procedures.
-/
namespace Lynth.Answer.Procedure

open Lean Elab Tactic Meta

/-- If the goal whnf-unfolds to `Sum`/`PSum`, return `isPSum`. -/
def isSumGoal : TacticM (Option Bool) := do
  let t ← whnf (← getMainTarget)
  match t with
  | .app (.app (.const ``PSum _) _) _ => pure (some true)
  | .app (.app (.const ``Sum _) _) _ => pure (some false)
  | _ => pure none

/-- Cardinality guard for finite refutation: whip `Fintype α` for the
bound domain and evaluate its cardinal to a literal. `none` if not a
small finite domain (then `decide` would hang or fail). -/
def domainCard (α : Expr) : MetaM (Option Nat) := do
  try
    -- NOTE: `Fintype.{u}` takes `α : Type u`, i.e. one level below
    -- `inferType α`; explicit levels throughout, since `mkAppM` leaves
    -- the instance unsynthesized.
    let αType ← inferType α
    let .sort (.succ u) := αType | pure none
    let inst ← synthInstance (mkApp (mkConst ``Fintype [u]) α)
    let c := mkApp (mkApp (mkConst ``Fintype.card [u]) α) inst
    match ← whnf c with
    | .lit (.natVal n) => pure (some n)
    | _ => pure none
  catch _ => pure none

/-- Max domain size for `decide` refutation (bigger spaces hang CI). -/
def maxDecideCard : Nat := 100000

/-- Finite refutation of a `∀`-goal: unfold head definitions, then
`decide`. Only runs under the cardinality guard. -/
def tryDecideForall : TacticM Bool := do
  let target ← whnf (← getMainTarget)
  match target with
  | .forallE _ α _ _ =>
    match ← domainCard α with
    | none => pure false
    | some n =>
      if n > maxDecideCard then return false
      -- collect unfoldable definitions in the target (bounded)
      let mut defs := #[]
      for s in Lynth.Euf.Procedure.collectSubterms target do
        if defs.size ≥ 8 then break
        match s with
        | .const c _ =>
          if (c.toString.startsWith "inst") then continue
          match (← getEnv).find? c with
          | some (.defnInfo _) =>
            if !(defs.any fun id => id.getId == c) then defs := defs.push (mkIdent c)
          | _ => pure ()
        | _ => pure ()
      try
        unless defs.isEmpty do
          evalTactic (← `(tactic| unfold $defs*))
        evalTactic (← `(tactic| decide))
        pure (← getUnsolvedGoals).isEmpty
      catch _ => pure false
  | _ => pure false

/-- Right branch: `refine inr`. First try finite `decide` refutation on
the `∀`-goal; otherwise `intros` and egraph split-free refutation.
True if closed. -/
def tryInr (isPSum : Bool) : TacticM Bool := do
  let snapshot ← saveState
  try
    let ctor := if isPSum then ``PSum.inr else ``Sum.inr
    evalTactic (← `(tactic| refine $(mkIdent ctor) ?_))
    if ← tryDecideForall then return true
    evalTactic (← `(tactic| intros))
    let t ← whnfR (← getMainTarget)
    unless t.isConstOf ``False do
      restoreState snapshot
      return false
    match ← Lynth.Egraph.Procedure.run with
    | .success => return true
    | .failure _ =>
      restoreState snapshot
      return false
  catch _ =>
    restoreState snapshot
    return false

/-- Left branch: `refine inl`, then synthesis sub-pipeline on the
`Subtype` goal. True if closed. -/
def tryInl (isPSum : Bool) : TacticM Bool := do
  let snapshot ← saveState
  try
    let ctor := if isPSum then ``PSum.inl else ``Sum.inl
    evalTactic (← `(tactic| refine $(mkIdent ctor) ?_))
    let procs := [Lynth.FinSearch.Procedure.run,
                  Lynth.FinSearch.ListInfer.run,
                  Lynth.Witness.run]
    for proc in procs do
      try
        match ← proc with
        | .success => return true
        | .failure _ => pure ()
      catch _ => pure ()
    restoreState snapshot
    return false
  catch _ =>
    restoreState snapshot
    return false

/-- Split answer goals; pass everything else through untouched. -/
def run : TacticM ProcedureOutcome := do
  match ← isSumGoal with
  | none => return .failure []
  | some isPSum =>
    if ← tryInr isPSum then return .success
    if ← tryInl isPSum then return .success
    return .failure []

end Lynth.Answer.Procedure
